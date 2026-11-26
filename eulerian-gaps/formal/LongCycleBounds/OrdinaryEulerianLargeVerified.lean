import LongCycleBounds.OrdinaryEulerianMomentAssembly
import LongCycleBounds.OrdinaryEulerianExteriorSign

namespace LongCycleBounds.OrdinaryEulerianGap
open LongCycleFinite LongCycles DescentNecklace

/-- Every open interval between consecutive zeros of the Eulerian polynomial
on n-1 letters contains exactly one zero of the true ordinary-descent row divided
by X. Both root lists are simple, negative, and complete with multiplicity. -/
theorem original_large {n k : ℕ} (hn : 128≤n) (hk : 3≤k) (kn : k≤n) :
    StrictNegativeInterlacing (EulerianBrackets.originalQuotient n k) (eulerian (n-1)) (n-3) :=
  original_large_of_alignment hn hk kn (@OrdinaryEulerianExterior.aligned_moments)

#print axioms original_large
end LongCycleBounds.OrdinaryEulerianGap
