"""Exact rational checks for the central Eulerian-gap estimate."""
from fractions import Fraction as F
from math import isqrt
R = F(63,25)    # rho/sqrt(n)
V = F(4,5)
n = 128
# For odd l>=5, sum l^-b is at most 5^-b + integral_5^infty u^-b du / 2.
def tail(b):
    return F(1,5**b) + F(1,2*(b-1)*5**(b-1))
factor = F(16,3)
assert (F(25,4)*(n-1)+10)/n < R**2
assert F(31,10)**2 / R**2 > F(3,2)
assert 3 * F(2,5)**4 + factor**4 * tail(7) < F(1,10)
assert 1 + F(2,5)**3 + factor**3 * tail(6) < F(11,10)
assert 1 + F(2,5)**2 + factor**2 * tail(4) < F(5,4)
assert F(99,100)**2 + F(1,30)**2 < 1
assert F(89,100)*F(6,5) > 1
# Supremum of each normalized coefficient error, multiplied by sqrt(n).
assert (F(11,10)*(R/V)**2)**2 * n / (n-1)**2 < 1
assert F(5,4)*(R/V*F(n,n-5))**3/n < 1
assert (F(5,4)*(2*R/V)**7)**2 < n**6
assert F(11,4)*R/V < 9 and 81 < F(16,25)*n
assert n**3 * F(4,5)**n < 1
assert (F(n+1,n)**3)*F(4,5) < 1
print('PASS for n>=128: principal centered term exceeds 1/sqrt(n); correction below 1/sqrt(n).')
