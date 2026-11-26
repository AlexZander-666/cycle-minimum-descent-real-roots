# Ordinary-descent Eulerian bracketing

This source package proves strict negative interlacing between the ordinary-descent polynomial of permutations whose cycles all have length at least `k`, divided by its simple zero at the origin, and the ordinary Eulerian polynomial on `n−1` letters. The statement holds for every `n≥6` and `3≤k≤n`; see [STATEMENT-MAP.md](STATEMENT-MAP.md). The lower polynomial has `n−3` simple negative roots, one in each consecutive Eulerian gap, and the upper Eulerian polynomial has `n−2` simple negative roots. Both root lists exhaust their degrees.

## Reproduce from source

Use Lean 4.33.1, Git, Python 3.10 or later, and Linux with a native filesystem and enough memory. From an empty directory, extract the source ZIP and run:

```sh
sha256sum --check SHA256SUMS
python3 -Bu verify_cold.py --work /tmp/eulerian-bracketing-clean --jobs 3
```

If the pinned third-party packages and their matching caches have already been obtained, append `--packages /path/to/.lake/packages`. The verifier checks each dependency's Git commit and tracked source status. On a fresh run it copies only the source closure and lock to the specified working directory. It strictly elaborates each project module from source and runs a separate kernel replay for each compiled module. It verifies that the audit's declarations use only `Classical.choice`, `propext`, and `Quot.sound` as applicable. Keep the working directory to resume the identical source edition at verified checkpoints. The default is one worker; compiling large proof blocks requires substantial memory. `receipt.json` is written on full success.

[SOURCE-ORIGINS.tsv](SOURCE-ORIGINS.tsv) records the input origins by paths relative to the producing mathematical workspace. [FINITE-PROVENANCE.json](FINITE-PROVENANCE.json) records the original frozen bracket inputs and per-size source digests. The actual finite arithmetic is checked by the Lean proofs shipped here. The 122 finite sizes cover 7,869 cutoff pairs via 3,904 representatives. The analytic proof starts at size 128.

At each fixed rank, arbitrary nonnegative real weights on cutoffs 3 through n with at least one positive entry give the same strict Eulerian interlacer. The proof pairs the two root lists at each Eulerian zero and uses linearity of evaluation there. The source verifier checks 575 project modules and 13 named declarations.
