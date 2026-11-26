import LongCycleBounds.OrdinaryEulerianLargeVerified
import LongCycleBounds.DescentEulerianBracketsThrough127

namespace LongCycleBounds.OrdinaryEulerianGap
open LongCycleFinite LongCycles DescentNecklace

/-- All cutoffs of at least three in ranks six and above, with the actual
ordinary-descent quotient and the Eulerian polynomial on one fewer letter. -/
theorem original_all {n k : ℕ} (hn : 6≤n) (hk : 3≤k) (kn : k≤n) :
    StrictNegativeInterlacing (EulerianBrackets.originalQuotient n k) (eulerian (n-1)) (n-3) := by
  by_cases hi : n≤127
  · exact EulerianBrackets.original_through127 hn hi hk kn
  · exact original_large (by omega) hk kn

#print axioms original_all
end LongCycleBounds.OrdinaryEulerianGap
