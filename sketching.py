# Synthesis faster version

import z3


def solve(phi):
    s = z3.Solver()
    s.add(phi)
    s.check()
    return s.model()


x = z3.BitVec('x', 8)
slow_expr = x * 2
h = z3.BitVec('h', 8)  # The hole, a.k.a. ??
fast_expr = x << h
goal = z3.ForAll([x], slow_expr == fast_expr)
print(solve(goal))

# [h = 1]
# We get the model [h = 1], which tells us that the two programs produce the same result for every byte x when we left-shift by 1.
# 00000001=1  00000010=2  00000100=4