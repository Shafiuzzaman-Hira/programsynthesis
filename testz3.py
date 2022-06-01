import z3

formula = (z3.Int('x') / 7 == 6)





print(solve(formula))
