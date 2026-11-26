"""Two-radius rigorous check after collecting equal length and loss in the logarithm."""
from fractions import Fraction as Q
from math import ceil
from two_radii import exp_upper

J=200
divisors = [()] + [tuple(d for d in range(1,i+1) if i%d==0) for i in range(1,J)]
mu=[0,1]
for i in range(2,J):
    mu.append(-sum(mu[d] for d in divisors[i][:-1]))

def atom(k,w):
    c = sum(abs(sum(mu[d] for d in divisors[i//h] if d*h>=k))*w**(i-h)/i
           for i in range(k,J) for h in divisors[i] if h<k)
    # For i>=J and h<k the complete divisor sum is zero, so the removed
    # short divisors give |sum_mu| <= k-1, independent of i.
    tail=(k-1)**2*w**(J-(k-1))/(J*(1-w))
    return Q(ceil(10**5*(c+tail)),10**5)

def recurrence_window(k):
    p=[Q(1)]
    for m in range(1,20+k):
        p.append(sum(p[:m-k+1],Q())/m if m>=k else Q())
    return max(p[20:])/min(p[20:])

def main():
    v,V=Q(4,5),Q(93,100)
    for k in range(3,8):
        c,C=atom(k,v),atom(k,V)
        R=recurrence_window(k)
        # For n>=128, residual <20 entails length >=109, loss >=55.
        cap=R*(exp_upper(c)-1)+2*k*(v/V)**55*(exp_upper(C)-1)
        uniform=Q(201,200)*(exp_upper(c)-1)+2*k*(v/V)**55*(exp_upper(C)-1)
        assert R<=Q(201,200) and cap<=uniform<1
        print(k, c, C, R,'ratio millionths upper',ceil(10**6*cap),
              'with uniform R',ceil(10**6*uniform))
    print('PASS')

if __name__=='__main__':
    if not __debug__:
        raise RuntimeError('Run with Python assertions enabled.')
    main()
