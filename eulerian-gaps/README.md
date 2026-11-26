# The Eulerian gaps of ordinary-descent polynomials

Theorem 3 places all n−3 zeros of each genuine cutoff quotient in consecutive gaps of the ordinary Eulerian polynomial on n−1 letters. It permits every n ≥ 6 and every nonnegative mixture of whole cutoff rows indexed by 3 ≤ k ≤ n, provided some weight is positive. The original permutation statistic counts ordinary descents in one-line notation. The previous six-page paper covers the individual real-rootedness question and all-cutoff mixtures including k=1 and k=2. Those exceptional boundary cutoffs do not appear in the gap theorem. [Nine-page paper](paper/main.pdf) · [TeX sources](paper/revision-tex.zip) · [Lean statement](formal/LongCycleBounds/OrdinaryEulerianMixture.lean)

## Reproduce

Run these commands from the eulerian-gaps directory in a clean checkout. Python 3.11 or later runs the numeric tests. The paper build needs pdfLaTeX with the standard LaTeX packages. The formal build needs Lean 4.33.1, Lake, Git and the pinned Mathlib packages. Choose an empty location for the first source rebuild.

~~~sh
(cd formal && sha256sum --quiet --check SHA256SUMS)
(cd paper && sha256sum --quiet --check SHA256SUMS)
python3 -B verification/direct_check.py
python3 -B paper/anc/gaps/verify_brackets.py
python3 -B paper/anc/gaps/two_radii.py
python3 -B paper/anc/gaps/short_signed.py
python3 -B paper/anc/gaps/central-budgets.py
python3 -B paper/build.py
python3 -Bu formal/verify_cold.py --work /tmp/ordinary-eulerian-gaps-v110 --jobs 3
~~~

### Lean entry point and complete audit

Open the release extract's complete `eulerian-gaps/formal` directory and obtain the pinned dependencies. To build the mathematical entry point explicitly, run `lake build +LongCycleBounds.OrdinaryEulerianMixture` there. Use the complete formal project for the `verify_cold.py` protocol above, including its finite data modules and `EulerianBracketingAudit`. The separate analytic source selection provided during manuscript review was intended for static inspection and for building `LongCycleBounds.OrdinaryEulerianLargeVerified` on its own analytic closure.

The complete Lean project contains 575 project proof modules. On DGX Spark, 574 byte-identical prerequisites were built from source with an initially empty project object directory and each was replayed independently. The additional mixture module was built from source against those exact objects and independently replayed. The combined audit printed 13 declarations with only `Classical.choice`, `propext`, and `Quot.sound`. [Cold receipt](verification/cold-receipt.json) · [Protocol provenance](verification/cold-provenance.json) · [Axiom transcript](verification/cold-axioms.log)

The finite proof covers sizes 6 through 127. Its 7,869 cutoff pairs reduce to 3,904 representatives. An independent direct count enumerates the 408,960 permutations of sizes 6–9 and checks 252 endpoint signs from the original rows. The infinite proof starts at 128. The common-gap argument uses the sign at each simple Eulerian zero, with the degree bound accounting for multiplicity. [Statement map](formal/STATEMENT-MAP.md) · [Direct counts](verification/direct-check.json) · [Mixture kernel replay](verification/isolated-cold-top.log)
