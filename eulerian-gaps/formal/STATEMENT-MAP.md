# Lean statement map

| Role | Module | Declaration |
| --- | --- | --- |
| All sizes and permitted cutoffs | `LongCycleBounds.OrdinaryEulerianAllVerified` | `LongCycleBounds.OrdinaryEulerianGap.original_all` |
| Original quotient of the polynomial by `X` | `LongCycleBounds.DescentEulerianBrackets` | `LongCycleBounds.DescentNecklace.EulerianBrackets.originalQuotient` |
| Finite sizes 6 through 127 | `LongCycleBounds.DescentEulerianBracketsThrough127` | `LongCycleBounds.DescentNecklace.EulerianBrackets.original_through127` |
| Analytic sizes 128 and up | `LongCycleBounds.OrdinaryEulerianLargeVerified` | `LongCycleBounds.OrdinaryEulerianGap.original_large` |
| Original finite rows and a common set of gaps for each size | `LongCycleBounds.DescentEulerianBrackets` | `LongCycleBounds.DescentNecklace.EulerianBrackets.original_of_representatives` |
| Analytic sign input | `LongCycleBounds.OrdinaryEulerianExteriorSign` | `LongCycleBounds.OrdinaryEulerianExterior.aligned_moments` |

The quotient definition uses `DescentTwoLetters.row n k`, converts its integer coefficients to real coefficients, and applies `Polynomial.divX`. The original row enumerates permutations of `Fin n` with cycle lengths at least `k` by ordinary adjacent-position descents. The comparison is at a fixed `n`, against `LongCycles.eulerian (n-1)`. The resulting `LongCycleFinite.StrictNegativeInterlacing … (n-3)` includes ordered root lists and multiplicities, and places the endpoints in the Eulerian row.

The mixture theorem is LongCycleBounds.OrdinaryEulerianGap.original_mixture_all. Its polynomial is the sum of the genuine quotients with weights over Finset.Icc 3 n; weights outside that interval have no effect. It asserts complete ordered factorizations for both polynomials.
