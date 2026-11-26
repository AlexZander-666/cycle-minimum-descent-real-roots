"""Replay the frozen rational intervals using integer recurrences and exact Horner."""
from fractions import Fraction
import json
from pathlib import Path

from certify import ordinary_row, representatives, sign_at, word_counts


def main():
    brackets = json.loads(Path(__file__).with_name("nodes-127-compact.json").read_bytes())
    rows = word_counts(127)
    euler = [1]  # rank 1
    count = reps = 0
    for n in range(3, 128):
        size = len(euler)+1
        euler = [(i+1)*(euler[i] if i < len(euler) else 0) +
                 (size-i)*(euler[i-1] if i else 0) for i in range(size)]
        if n < 6:
            continue
        polys = []
        for k in representatives(n):
            if k >= 3:
                full = ordinary_row(n, rows[n,k])
                assert full[0] == full[-1] == 0 and min(full[1],full[-2]) > 0
                polys.append(full[1:-1])
        boxes = brackets[str(n)]
        assert len(boxes) == n-2 and all(len(p) == n-2 for p in polys)
        previous = None
        for i,(a,b) in enumerate(boxes):
            x,y = (Fraction(z,1<<s) for z,s in (a,b))
            assert x < y < 0 and (previous is None or previous < x)
            sign = (-1)**(n-3-i)
            assert sign_at(euler,a) == -sign and sign_at(euler,b) == sign
            assert all(sign_at(p,a) == sign_at(p,b) == sign for p in polys)
            previous = y
        count += n-2
        reps += len(polys)
        if n % 16 == 0:
            print("Verified through rank",n,flush=True)
    assert (count,reps)==(7869,3904)
    print("PASS: 122 sizes, 7869 original cutoffs, 3904 distinct cutoff representatives.")
if __name__=="__main__":
    if not __debug__:
        raise RuntimeError("Python assertions must be enabled")
    main()
