# Real zeros of descent polynomials for permutations with a minimum cycle length

**For every 3 ≤ k ≤ n, the ordinary-descent polynomial of permutations of n letters with shortest cycle of length at least k has only real zeros.** This resolves Per Alexandersson’s ordinary-descent conjecture. At each size n every nonzero nonnegative mixture, even allowing k = 1 and 2, has only real, nonpositive zeros. [Original question](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#permutations-with-long-cycles) · [Six-page proof](paper/main.pdf)

**Eulerian gaps.** For every n ≥ 6, the n−2 zeros of the ordinary Eulerian polynomial on n−1 letters separate every quotient D(n,k;t)/t with 3 ≤ k ≤ n. Each gap contains exactly one simple root of the quotient. The same holds for every nonzero nonnegative real combination of these whole cutoff rows divided by t. The Eulerian-gap observation and its initial finite evidence were communicated by Per Alexandersson’s group after the first edition. [Nine-page proof](eulerian-gaps/paper/main.pdf) · [Exact statement, sources and reproduction](eulerian-gaps/README.md)

The Eulerian-gap audit covers 575 project modules and 13 declarations. The DGX Spark result combines the independent cold build and kernel replay of 574 unchanged prerequisite modules with a cold build and independent replay of the new mixture module. All audited declarations use only the three standard Lean axioms. [Provenance](eulerian-gaps/verification/cold-provenance.json) · [Per-module receipt](eulerian-gaps/verification/cold-receipt.json) · [Axiom transcript](eulerian-gaps/verification/cold-axioms.log)

Let D(n,k;t) be the sum of t raised to the number of indices i < n satisfying π(i) > π(i+1), over permutations π whose cycles all have length at least k. Fix n ≥ 1 and take real weights w₁,…,wₙ ≥ 0 with positive sum. Every root of ∑wₖD(n,k;t) is simple except in two cases.

- For n = 4 with positive weight only at k = 2, the row is proportional to t(t+2)².
- For n = 5 with w₁ = w₂ = 0, it is proportional to 6t(t+1)².

For fixed n ≥ 3 other than 5, every row with 3 ≤ k ≤ n has a simple root at zero. The same n−3 disjoint open negative intervals isolate its remaining roots, one per interval. At n = 3 that set of intervals is empty. The proof obtains common signs from the Gessel–Reutenauer alphabet polynomial for n ≥ 128. Integer certificates cover the smaller sizes. Independently reconstructed finite rows give 327,451 integer sign evaluations at the common interior nodes for k ≥ 3. [Proof source](paper/main.tex) · [Finite and large-row proof entry](formal/LongCycleBounds/DescentAllSizes.lean) · [All cutoffs and multiplicities](formal/LongCycleBounds/DescentAllCutoffSizes.lean)

## Reproduce

From this repository's root, run the following with Python 3.11 or later. The finite verifier uses the standard library. PDF reproduction also needs pdfLaTeX; TeX Live 2026 produces the checked release bytes.

~~~sh
python3 scripts/verify.py
python3 paper/reproduce.py finite
python3 scripts/verify_paper.py --frozen
~~~

The Lean audit uses Lean 4.33.1 and the exact nine Git dependencies in the supplied Lake lock. With Lean and Lake on PATH, the following builds the whole original closure from source and checks each module with LeanChecker. It can take several hours and requires room for the Mathlib cache and compiled project.

~~~sh
python3 formal/verify_lean.py formal AllCutoffsManuscriptAudit --serial
~~~

The six-job reference run completed 499 clean strict builds and 499 separate kernel replays, including the audit module. All 22 audited declarations reported only propext, Classical.choice and Quot.sound. The 499 proof-source digests and the compiled-module digests are included. The repository distributes original sources and mathematical certificates. Build receipts omit machine-local paths and identifiers. [Toolchain](formal/lean-toolchain) · [Locks](formal/lake-manifest.json) · [Public replay transcript](verification/cold-replay-public.log) · [Per-module inventory](verification/verified-modules.tsv) · [Audit declarations](formal/AllCutoffsManuscriptAudit.lean)

ProgramComputer previously proved every single-cycle row, including the double root at n = 5, and arbitrary nonnegative cycle-type mixtures when n ≥ 25 and k ≥ 52 log n. The theorem here admits every cutoff and size and weights whole cutoff rows. [ProgramComputer’s proof](https://github.com/ProgramComputer/open-math-research/blob/4da48b72ed8f92f96c2faf60e2d63d253b3b507a/topics/long-cycle-descents/paper.tex)

Alexandersson previously proved the case k = 2. Gessel and Reutenauer supplied the cycle-type/descent-set identity used in this proof. The companion conjecture about strict excedances and roots across consecutive sizes concerns a different statistic and order of quantification. [Prior work](PRIOR-ART.md)

Bowen Zuo (East China University of Science and Technology) is the sole author of the tagged releases and takes responsibility for them. The six-page first edition was released on 26 November 2026. The nine-page revision adds Theorem 3. ChatGPT assisted with mathematical development, exact computation, formalization and drafting. All proof claims above have the source and verification scope given in this release. Original software is distributed under Apache-2.0; the paper is separately copyrighted. [Software license](LICENSE) · [Rights and attribution](LICENSE-SCOPE.md)

## Authorship

The tagged releases v1.0.0 and v1.1.0 list Bowen Zuo as sole author. They remain unchanged and may be cited as they are. Release v1.0.0 is the version cited as [Zuo26] in Alexandersson's Symmetric Functions Catalog. The manuscript prepared for journal submission is joint work of Bowen Zuo and Xiaojuan Luo (corresponding author), both of East China University of Science and Technology.
