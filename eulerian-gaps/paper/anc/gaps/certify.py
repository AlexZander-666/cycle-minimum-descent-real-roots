"""Exact coefficient and real-root replay for ordinary descents with a cycle-length cutoff."""
from argparse import ArgumentParser
from collections import Counter
from functools import reduce
from hashlib import sha256
from itertools import permutations
from math import comb, exp, factorial, frexp, gcd, pi, tan
from pathlib import Path
import json


def representatives(n):
    return range(2, min(n, n // 2 + 1) + 1)


def necklace_counts(q, last):
    primitive = [0] + [q ** size for size in range(1, last + 1)]
    # In a word of length size, the minimal period is a divisor of size.
    for length in range(1, last + 1):
        for multiple in range(2 * length, last + 1, length):
            primitive[multiple] -= primitive[length]
        assert primitive[length] >= 0 and primitive[length] % length == 0
    return [0] + [primitive[length] // length for length in range(1, last + 1)]


def apply_factor(old, step, weights):
    product = old[:]
    for m, weight in enumerate(weights, 1):
        offset = m * step
        for j in range(offset, len(old)):
            product[j] += weight * old[j - offset]
    return product


def partitions_from_long_necklaces(last, q):
    necklaces = necklace_counts(q, last)
    counts = [1] + [0] * last
    for k in range(last, 1, -1):
        multiplicity = necklaces[k]
        if multiplicity:
            added = [comb(multiplicity + j - 1, j) for j in range(1, last // k + 1)]
            counts = apply_factor(counts, k, added)
        yield k, counts


def partitions_from_short_necklace_removal(last, q):
    necklaces = necklace_counts(q, last)
    counts = [q ** size for size in range(last + 1)]
    for k in range(2, last // 2 + 2):
        step = k - 1
        removed = [(-1) ** j * comb(necklaces[step], j)
                   for j in range(1, min(necklaces[step], last // step) + 1)]
        counts = apply_factor(counts, step, removed)
        yield k, counts


def word_counts(last):
    rows = {(n, k): [] for n in range(2, last + 1) for k in representatives(n)}
    for q in range(1, last + 3):
        by_removal = dict(partitions_from_short_necklace_removal(last, q))
        for k, partial in partitions_from_long_necklaces(last, q):
            if k > last // 2 + 1:
                continue
            lo, hi = max(k, q - 2), last + 1
            for n in range(lo, hi):
                if (n, k) in rows:
                    assert by_removal[k][n] == partial[n], (n, k, q)
                    rows[n, k].append(partial[n])
    return rows


def raw_enumeration(last):
    result = {}
    for n in range(2, last + 1):
        tables = [[0] * n for _ in range(n + 1)]
        for permutation in permutations(range(n)):
            seen = [False] * n
            least = n
            for i in range(n):
                if not seen[i]:
                    length, j = 0, i
                    while not seen[j]:
                        seen[j] = True
                        length += 1
                        j = permutation[j]
                    least = min(least, length)
            if least >= 2:
                descents = sum(a > b for a, b in zip(permutation, permutation[1:]))
                for k in range(2, least + 1):
                    tables[k][descents] += 1
        for k in range(2, n + 1):
            result[n, k] = tables[k]
    return result


def totals(last):
    results = {}
    for k in range(2, last // 2 + 2):
        sums = [1]
        for n in range(1, last + 1):
            sums.append(sum(comb(n - 1, a - 1) * factorial(a - 1) * sums[n - a]
                            for a in range(k, n + 1)))
        results[k] = sums
    return results


def ordinary_row(n, words):
    signed_binomial = [(-1) ** j * comb(n + 1, j) for j in range(n + 1)]
    row = [sum(signed_binomial[j] * words[r - j] for j in range(r + 1)) for r in range(n)]
    assert sum(row) > 0 and min(row) >= 0 and row[0] == 0, (n, row)
    # Extra alphabet sizes are not used to reconstruct the numerator.
    for q in range(n + 1, len(words) + 1):
        assert words[q - 1] == sum(a * comb(q + n - r - 1, n) for r, a in enumerate(row)), (n, q)
    return row


def dyadic(value):
    mantissa, exponent = frexp(value)
    mantissa = round(mantissa * 2 ** 24)
    exponent -= 24
    return (mantissa << exponent, 0) if exponent > 0 else (mantissa, -exponent)


def make_mesh(last):
    return {str(n): [list(dyadic(-exp(-pi / tan(pi * i / (n + 1)))))
                     for i in range(2, n)] for n in range(2, last + 1)}


def sign_at(row, point):
    numerator, shift = point
    result = row[-1]
    for step, co in enumerate(reversed(row[:-1]), 1):
        result = result * numerator + (co << (shift * step))
    return (result > 0) - (result < 0)


def trim(values):
    while values and values[-1] == 0:
        values.pop()
    return values


def primitive(values):
    trim(values)
    content = reduce(gcd, values, 0)
    return [value // content for value in values] if content else []


def negative_remainder(dividend, divisor):
    dividend = dividend[:]
    direction = 1 if divisor[-1] > 0 else -1
    leading = abs(divisor[-1])
    while len(dividend) >= len(divisor):
        shift = len(dividend) - len(divisor)
        factor = direction * dividend[-1]
        dividend = primitive([leading * value - (factor * divisor[i - shift] if i >= shift else 0)
                              for i, value in enumerate(dividend)])
    return [-value for value in dividend]


def sturm_count(row):
    left = primitive(row[:])
    right = primitive([i * v for i, v in enumerate(left)][1:])
    signature = [[len(left) - 1, 1 if left[-1] > 0 else -1]]
    while right:
        signature.append([len(right) - 1, 1 if right[-1] > 0 else -1])
        left, right = right, negative_remainder(left, right)
    def changes(signs):
        return sum(a != b for a, b in zip(signs, signs[1:]))
    minus = changes([sign * (-1) ** degree for degree, sign in signature])
    plus = changes([sign for _, sign in signature])
    return minus - plus, signature[-1][0], signature


def count_sign_switches(signs):
    nonzero = [sign for sign in signs if sign]
    return sum(a != b for a, b in zip(nonzero, nonzero[1:]))


def row_certificate(n, k, row, points):
    degree = len(row) - 1
    stripped = row[1:]
    at_zero = 1
    while stripped and stripped[0] == 0:
        stripped = stripped[1:]
        at_zero += 1
    assert len(stripped) and stripped[0] > 0 and at_zero >= 1
    coeff_digest = sha256(",".join(map(str, row)).encode("ascii")).hexdigest()
    cert = {"n": n, "k": k, "degree": degree, "zero_multiplicity": at_zero, "coefficient_sha256": coeff_digest}

    if len(stripped) == 1:
        return cert | {"method": "monomial", "negative": 0}
    if n == 5 and k >= 3:
        assert row == [0, 6, 12, 6]
        return cert | {"method": "factor", "negative": 1, "negative_multiplicity": 2}

    # The endpoints are bounded outside all roots by the elementary Cauchy bound.
    far = -(1 + max(abs(v) for v in stripped[:-1]) // stripped[-1] + 1)
    node_values = [sign_at(stripped, point) if (point[0] > far << point[1]) else 0
                   for point in points]
    cert_signs = [1, *node_values, sign_at(stripped, (far, 0))]
    switches = count_sign_switches(cert_signs)
    if switches == len(stripped) - 1:
        return cert | {"method": "mesh", "negative": switches}
    distinct, gcd_degree, sequence = sturm_count(stripped)
    print(f"Sturm n={n} k={k} degree={degree} mesh_signs={switches} "
          f"distinct_nonzero={distinct} gcd_degree={gcd_degree}", flush=True)
    return cert | {"method": "sturm", "negative": distinct, "nonzero_gcd_degree": gcd_degree,
                   "all_real_via_sturm": distinct == len(stripped) - 1 - gcd_degree,
                   "chain": sequence}


def run(last, mesh, direct):
    words = word_counts(last)
    weights = totals(last)
    literal = raw_enumeration(direct)
    checks = len(literal)
    print(f"Direct one-line permutation enumeration: {checks} rows, 2 <= n <= {direct}", flush=True)
    certs = []
    for n in range(2, last + 1):
        points = mesh[str(n)]
        assert len(points) == n - 2
        assert all(a < 0 and b >= 0 for a, b in points)
        assert all((a << d) > (c << b) for (a, b), (c, d) in zip(points, points[1:]))
        for k in representatives(n):
            row = ordinary_row(n, words[n, k])
            assert sum(row) == weights[k][n], (n, k)
            if n <= direct:
                last_cutoff = n if n < 2 * k else k
                assert all(row == literal[n, cut] for cut in range(k, last_cutoff + 1)), (n, k)
            if k >= 3:
                assert row[n - 1] == 0 and row[n - 2] > 0 and row[1] > 0, (n, k)
            certs.append(row_certificate(n, k, trim(row), points))
        if n % 16 == 0 or n == last:
            print(f"Completed through n={n}, {len(certs)} representative rows", flush=True)
    failures = [(c["n"], c["k"]) for c in certs if not c.get("all_real_via_sturm", True)]
    counts = dict(Counter(c["method"] for c in certs))
    print(f"Completed {sum(n - 1 for n in range(2, last + 1))} nonempty rows "
          f"represented by {len(certs)}: {counts}; failed real-rootedness checks {failures}.", flush=True)
    return certs, failures


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--last", type=int, default=127)
    parser.add_argument("--direct", type=int, default=9)
    parser.add_argument("--generate", type=Path)
    parser.add_argument("--verify", type=Path)
    args = parser.parse_args()
    if not 2 <= args.last or not 2 <= args.direct <= args.last:
        parser.error("invalid last or direct size")
    if args.generate and args.verify:
        parser.error("indicate either certificate generation or independent replay")

    if args.verify:
        expected = json.loads(args.verify.read_text())
        mesh = expected["mesh"]
        assert expected["last"] == args.last
    else:
        mesh = make_mesh(args.last)
    cases, failures = run(args.last, mesh, args.direct)
    computed = {"last": args.last, "mesh": mesh, "cases": cases}
    if args.generate:
        args.generate.write_text(json.dumps(computed, separators=(",", ":")) + "\n")
    if args.verify:
        assert computed == expected
        print("PASS byte-stable certificate content independently matched.")
    if failures:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
