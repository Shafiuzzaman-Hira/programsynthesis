import lark
import z3
# A language inspired from a Lark example from:
# https://github.com/lark-parser/lark/wiki/Examples
from z3 import Solver, sat, Or, Z3Exception, is_array, Z3_UNINTERPRETED_SORT


GRAMMAR = """
?start: sum
  | sum "?" sum ":" sum -> if
  | sum "=="  sum       -> eq 
  
?sum: term
  | sum "+" term        -> add
  | sum "-" term        -> sub

?term: item
  | term "*"  item      -> mul
  | term "/"  item      -> div
  | term ">>" item      -> shr
  | term "<<" item      -> shl
  | term ">"  term       -> gt


?item: NUMBER           -> num
  | "-" item            -> neg
  | CNAME               -> var
  | "(" start ")"

%import common.NUMBER
%import common.WS
%import common.CNAME
%ignore WS
""".strip()


def interp(tree, lookup):
    """Evaluate the arithmetic expression.

    Pass a tree as a Lark `Tree` object for the parsed expression. For
    `lookup`, provide a function for mapping variable names to values.
    """
    op = tree.data
    if op in ('add', 'sub', 'mul', 'div', 'shl', 'shr'):  # Binary operators.
        lhs = interp(tree.children[0], lookup)
        rhs = interp(tree.children[1], lookup)
        if op == 'add':
            return lhs + rhs
        elif op == 'sub':
            return lhs - rhs
        elif op == 'mul':
            return lhs * rhs
        elif op == 'div':
            return lhs / rhs
        elif op == 'shl':
            return lhs << rhs
        elif op == 'shr':
            return lhs >> rhs
    elif op == 'neg':  # Negation.
        sub = interp(tree.children[0], lookup)
        return -sub
    elif op == 'num':  # Literal number.
        return int(tree.children[0])
    elif op == 'var':  # Variable lookup.
        return lookup(tree.children[0])
    elif op == 'if':  # Conditional.
        cond = interp(tree.children[0], lookup)
        true = interp(tree.children[1], lookup)
        false = interp(tree.children[2], lookup)
        return (cond != 0) * true + (cond == 0) * false


def pretty(tree, subst={}, paren=False):
    """Pretty-print a tree, with optional substitutions applied.

    If `paren` is true, then loose-binding expressions are
    parenthesized. We simplify boolean expressions "on the fly."
    """

    # Add parentheses?
    if paren:
        def par(s):
            return '({})'.format(s)
    else:
        def par(s):
            return s

    op = tree.data
    if op in ('add', 'sub', 'mul', 'div', 'shl', 'shr', 'gt', 'lt', 'eq', 'and'):
        lhs = pretty(tree.children[0], subst, True)
        rhs = pretty(tree.children[1], subst, True)
        c = {
            'add': '+',
            'sub': '-',
            'mul': '*',
            'div': '/',
            'shl': '<<',
            'shr': '>>',
            'gt': '>',
            'lt': '<',
            'eq': '==',
            'and': '&',
        }[op]
        return par('{} {} {}'.format(lhs, c, rhs))
    elif op == 'neg':
        sub = pretty(tree.children[0], subst)
        return '-{}'.format(sub, True)
    elif op == 'num':
        return tree.children[0]
    elif op == 'var':
        name = tree.children[0]
        return str(subst.get(name, name))
    elif op == 'if':
        cond = pretty(tree.children[0], subst)
        true = pretty(tree.children[1], subst)
        false = pretty(tree.children[2], subst)
        return par('{} ? {} : {}'.format(cond, true, false))


def run(tree, env):
    """Ordinary expression evaluation.

    `env` is a mapping from variable names to values.
    """

    return interp(tree, lambda n: env[n])


def z3_expr(tree, vars=None):
    """Create a Z3 expression from a tree.

    Return the Z3 expression and a dict mapping variable names to all
    free variables occurring in the expression. All variables are
    represented as BitVecs of width 8. Optionally, `vars` can be an
    initial set of variables.
    """

    vars = dict(vars) if vars else {}

    # Lazily construct a mapping from names to variables.
    def get_var(name):
        if name in vars:
            return vars[name]
        else:
            v = z3.BitVec(name, 8)
            vars[name] = v
            return v

    return interp(tree, get_var), vars


# Return the model with the highest cost of formula list of formulas F
def get_wpi_model(F):
    max_cost = -1
    wpi = ''
    counter = 0
    s = Solver()
    s.add(F)
    print("Enemurating SAT models.....")
    while s.check() == sat and counter < 2000:
        m = s.model()
        counter+=1
        #print("Model " + str(counter))
        #print(s.model)
        print (sorted ([(d, m[d]) for d in m], key = lambda x: str(x[0])))
        # print()
        if len(s.model()) > max_cost:
            max_cost = len(s.model())
            wpi = s.model()

        # Create a new constraint the blocks the current model
        block = []
        for d in m:
            # d is a declaration
            if d.arity() > 0:
                raise Z3Exception("uninterpreted functions are not supported")
            # create a constant from declaration
            c = d()
            if is_array(c) or c.sort().kind() == Z3_UNINTERPRETED_SORT:
                raise Z3Exception("arrays and uninterpreted sorts are not supported")
            block.append(c != m[d])
        s.add(Or(block))
    return wpi


def model_values(model):
    """Get the values out of a Z3 model.
    :type model: object
    """
    return {
        d.name(): model[d]
        for d in model.decls()
    }


def solve(phi):
    """Solve a Z3 expression, returning the model.
    """

    s = z3.Solver()
    s.add(phi)
    s.check()
    #print ("Randomly picked")
    random_sat = s.model()
    #print(s.model())
    wpi = get_wpi_model(phi)
    return random_sat, wpi


def synthesize(tree1, tree2):
    """Given two programs, synthesize the values for holes that make
    them equal.`tree1` has no holes. In `tree2`, every variable beginning with the
    letter "h" is considered a hole.
    """

    expr1, vars1 = z3_expr(tree1)
    expr2, vars2 = z3_expr(tree2, vars1)

    # Filter out the variables starting with "h" to get the non-hole variables.
    plain_vars = {k: v for k, v in vars1.items()
                  if not k.startswith('h')}

    # Formulate the constraint for Z3.
    goal = z3.ForAll(
        list(plain_vars.values()),  # For every valuation of variables...
        expr1 == expr2,  # ...the two expressions produce equal results.
    )
    print(goal)
    return solve(goal)


if __name__ == '__main__':
    f1 = open("s2.txt", "r")
    src = f1.read()
    f2 = open("o2.txt", "r")
    output = f2.read()
    print("Specification reading done")
    parser = lark.Lark(GRAMMAR)
    output_tree = parser.parse(output)
    src_tree = parser.parse(src)
    print("Tree parsing done")
    random_model,wpi_model = synthesize(output_tree, src_tree)
    if(len(wpi_model)>0):
        print("random")
        print(pretty(src_tree, model_values(random_model)))
        print("wpi")
        #print(model)
        print(pretty(src_tree, model_values(wpi_model)))
    else:
        print("UNSAT")
