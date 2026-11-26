import LongCycleBounds.DescentFiniteThrough16
import LongCycleBounds.DescentSweepData.N017
import LongCycleBounds.DescentSweepData.N018
import LongCycleBounds.DescentSweepData.N019
import LongCycleBounds.DescentSweepData.N020
import LongCycleBounds.DescentSweepData.N021
import LongCycleBounds.DescentSweepData.N022
import LongCycleBounds.DescentSweepData.N023
import LongCycleBounds.DescentSweepData.N024

/-! The ordinary-descent finite prefix through size 24. -/

namespace LongCycleBounds.DescentNecklace

/-- The full simple-root pattern for ordinary descent rows apart from the size-five exception. -/
theorem simple_roots_through24 {n k : ℕ} (lo : 3 ≤ n) (hi : n ≤ 24)
    (five : n ≠ 5) (hk : 3 ≤ k) (kn : k ≤ n) : SimpleDescentRootPattern n k := by
  by_cases small : n ≤ 16
  · exact simple_roots_through16 lo small five hk kn
  · interval_cases n
    · exact Sweep.N017.original_roots hk kn
    · exact Sweep.N018.original_roots hk kn
    · exact Sweep.N019.original_roots hk kn
    · exact Sweep.N020.original_roots hk kn
    · exact Sweep.N021.original_roots hk kn
    · exact Sweep.N022.original_roots hk kn
    · exact Sweep.N023.original_roots hk kn
    · exact Sweep.N024.original_roots hk kn

/-- Every original ordinary-descent row in the finite prefix splits over the reals. -/
theorem splits_through24 {n k : ℕ} (lo : 3 ≤ n) (hi : n ≤ 24)
    (hk : 3 ≤ k) (kn : k ≤ n) :
    ((DescentTwoLetters.row n k).map (Int.castRingHom ℝ)).Splits := by
  by_cases five : n = 5
  · subst n
    exact row_five_splits hk kn
  · exact (simple_roots_through24 lo hi five hk kn).1

#print axioms simple_roots_through24
#print axioms splits_through24

end LongCycleBounds.DescentNecklace
