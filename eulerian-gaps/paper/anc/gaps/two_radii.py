"""Exact rational atom bounds for 8 <= k <= 57 and n >= 128.

All mathematical comparisons use fractions. The display rounds upwards to
integer millionths. All sums over repetitions and over unvisited lengths are
bounded analytically, with the inequalities given in the Eulerian-gap section.
"""
from fractions import Fraction as Q
from math import ceil

def atom_upper(v, s, J=200):
    assert v <= s**2 < 1 and v**J <= Q(1, 2)
    cost = 0
    for j in range(8,J):
        divisors = [d for d in range(1,j+1) if j % d == 0 and d % 4 and d % 9]
        primitive = sum(v**(j-j//d) for d in divisors if d > 1)/j
        repetitions = sum(v**(2*j-j//d) for d in divisors)/(2*j*(1-v**8))
        cost += primitive + repetitions
    return cost + Q(3,2)*s**J/(1-s)

def exp_upper(c):
    return (1-c/256)**-256

def main():
    v, V = Q(4,5), Q(93,100)
    cv, cV = Q(365,1000), Q(255,100)
    for value, root, cap in ((v,Q(179,200),cv),(V,Q(193,200),cV)):
        cost = atom_upper(value,root)
        assert cost < cap
        print("radius",value,"atom bound in millionths (upper)",ceil(10**6*cost))
    total = 2*(exp_upper(cv)-1)+114*(v/V)**64*(exp_upper(cV)-1)
    assert total < 1
    print("normalized total in millionths (upper)",ceil(10**6*total))
    print("PASS")

if __name__ == "__main__":
    if not __debug__:
        raise RuntimeError("Run with Python assertions enabled.")
    main()
