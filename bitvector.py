import z3


def solve(phi):
    s = z3.Solver()
    s.add(phi)
    s.check()
    return s.model()


y = z3.BitVec('y', 8)
# y <<3  shift to left by 3 bits   5 = 00000101    40= 00101000
print(solve(y << 3 == 40))

# [y = 5]


z = z3.Int('z')
n = z3.Int('n')
print(solve(z3.ForAll([z], z * n == z)))