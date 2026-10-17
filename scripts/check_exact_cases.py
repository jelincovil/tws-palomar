#!/usr/bin/env python3
"""Independent rational matrix checks; these are NOT proofs of the Lean code."""
from fractions import Fraction as Q
from itertools import product
from random import Random

TAPS = [Q(x, 32) for x in [-1, 0, 9, 16, 9, 0, -1]]

# Exact symbolic autocorrelation in Q(sqrt(3)): multiply (a+b sqrt(3)).
def mul3(x, y):
    a, b = x
    c, d = y
    return a*c + 3*b*d, a*d + b*c

h = [(1, 1), (3, 1), (3, -1), (1, -1)]
ac = []
for lag in range(4):
    terms = [mul3(h[i], h[i+lag]) for i in range(4-lag)]
    real = Q(sum(x[0] for x in terms), 32)
    radical = Q(sum(x[1] for x in terms), 32)
    assert radical == 0
    ac.append(real)
assert [ac[abs(j)]/2 for j in range(-3, 4)] == TAPS
print('PASS: exact db2 half-autocorrelation, independently in Q(sqrt(3)).')

# Construct the circulant matrix directly by applying all shifted stencil taps,
# rather than defining its norm to be the l1 sum.
def matrix(n, taps, offsets):
    A = [[Q(0) for _ in range(n)] for _ in range(n)]
    for x in range(n):
        for a, offset in zip(taps, offsets):
            A[x][(x-offset) % n] += a
    return A

def check_matrix(A):
    norms = [sum(map(abs, row)) for row in A]
    actual = max(norms)
    i = norms.index(actual)
    witness = [Q(1) if a >= 0 else Q(-1) for a in A[i]]
    response = [sum(a*f for a, f in zip(row, witness)) for row in A]
    assert max(map(abs, witness)) == 1
    assert max(map(abs, response)) == actual
    return actual

for n in range(1, 17):
    value = check_matrix(matrix(n, TAPS, list(range(-3, 4))))
    assert value <= Q(9,8)
    if n >= 7:
        assert value == Q(9,8)
    if n in {4,5,6,7,16}:
        print(f'period {n}: exact one-dimensional matrix norm = {value}')
assert check_matrix(matrix(4, TAPS, list(range(-3, 4)))) == 1
print('PASS: alias cancellation at N=4; equality may also hold for N=5,6.')

# Explicit tensor matrices in dimension two, including the no-collision boundary.
for n in [4,5,6,7,8]:
    A = matrix(n, TAPS, list(range(-3,4)))
    B = [[A[x][u] * A[y][v] for u,v in product(range(n),repeat=2)]
         for x,y in product(range(n),repeat=2)]
    value = check_matrix(B)
    assert value == check_matrix(A)**2
    if n >= 7:
        assert value == Q(81,64)
print('PASS: explicit tensor matrices and attaining signals in dimension two.')

# d=0 is the one-point group; the empty product gives the identity.
assert check_matrix([[Q(1)]]) == Q(9,8)**0
rng = Random(20261017)
for _ in range(80):
    n = rng.randint(1,12)
    m = rng.randint(0,12)
    taps = [Q(rng.randint(-8,8), rng.randint(1,7)) for _ in range(m)]
    offsets = [rng.randint(-20,20) for _ in range(m)]
    value = check_matrix(matrix(n,taps,offsets))
    mass = sum(map(abs,taps))
    assert value <= mass
    if len({x % n for x in offsets}) == len(offsets):
        assert value == mass
print('PASS: 80 seeded signed-stencil cases, including empty stencils and collisions.')
print('These finite checks do not establish the universally quantified Lean theorems.')
