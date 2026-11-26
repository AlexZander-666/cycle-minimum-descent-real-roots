"""Enumerate actual permutations and count rationally isolated mixture roots."""
from collections import Counter
from itertools import permutations
from math import factorial
import json
from fractions import Fraction
from pathlib import Path

def descents(sigma):
    return sum(a>b for a,b in zip(sigma,sigma[1:]))

def shortest_cycle(sigma):
    seen=set()
    result=len(sigma)
    for a in range(len(sigma)):
        if a in seen:
            continue
        length=0
        while a not in seen:
            seen.add(a)
            length+=1
            a=sigma[a]
        result=min(result,length)
    return result

def evaluate(coefficients,x):
    value=Fraction(0)
    for c in reversed(coefficients):
        value=value*x+c
    return value

def check(n,raw_boxes):
    freq=Counter((shortest_cycle(p),descents(p)) for p in permutations(range(n)))
    assert sum(freq.values())==factorial(n)
    euler=Counter(descents(p) for p in permutations(range(n-1)))
    assert max(euler)==n-2 and sum(euler.values())==factorial(n-1)
    q=[euler[j] for j in range(n-1)]
    boxes=[tuple(Fraction(num,2**exp) for num,exp in pair) for pair in raw_boxes]
    assert len(boxes)==n-2 and all(a<b<0 for a,b in boxes)
    assert all(b<c for (_,b),(c,_) in zip(boxes,boxes[1:]))
    rows={}
    for k in range(3,n+1):
        terms=Counter()
        for (minimum,d),c in freq.items():
            if minimum>=k:
                assert d>0
                terms[d-1]+=c
        assert max(terms)==n-3 and terms[n-3]>0
        rows[k]=tuple(terms[j] for j in range(n-2))
    for i,(a,b) in enumerate(boxes):
        sign=(-1)**(n-3-i)
        assert evaluate(q,a)*sign<0<evaluate(q,b)*sign
        for row in rows.values():
            assert evaluate(row,a)*sign>0 and evaluate(row,b)*sign>0
    # Linearity gives these strict signs for every positive-total nonnegative mixture.
    # Each alternating gap accounts for a distinct root and the degrees exhaust multiplicity.
    return {"n":n,"original_permutations_enumerated":factorial(n),
            "eulerian_permutations_enumerated":factorial(n-1),"whole_cutoff_rows":len(rows),
            "strict_row_endpoint_tests":2*len(boxes)*len(rows),
            "distinct_polynomials":len(set(rows.values()))}

if __name__=="__main__":
    if not __debug__: raise RuntimeError("Enable Python assertions")
    boxes=json.loads((Path(__file__).resolve().parent.parent/"paper/anc/gaps/nodes-127-compact.json").read_bytes())
    print(json.dumps([check(n,boxes[str(n)]) for n in range(6,10)],indent=2))
