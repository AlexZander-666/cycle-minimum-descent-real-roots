import LongCycleBounds.DescentFiniteThrough24
import LongCycleBounds.DescentSweepData.N025
import LongCycleBounds.DescentSweepData.N026
import LongCycleBounds.DescentSweepData.N027
import LongCycleBounds.DescentSweepData.N028
import LongCycleBounds.DescentSweepChunkData.N029
import LongCycleBounds.DescentSweepChunkData.N030
import LongCycleBounds.DescentSweepChunkData.N031
import LongCycleBounds.DescentSweepChunkData.N032

/-! The ordinary-descent finite prefix through size 32. -/

namespace LongCycleBounds.DescentNecklace

/-- The full simple-root pattern for ordinary descent rows apart from the size-five exception. -/
theorem simple_roots_through32 {n k : ℕ} (lo : 3 ≤ n) (hi : n ≤ 32)
    (five : n ≠ 5) (hk : 3 ≤ k) (kn : k ≤ n) : SimpleDescentRootPattern n k := by
  by_cases small : n ≤ 24
  · exact simple_roots_through24 lo small five hk kn
  · interval_cases n
    · exact Sweep.N025.original_roots hk kn
    · exact Sweep.N026.original_roots hk kn
    · exact Sweep.N027.original_roots hk kn
    · exact Sweep.N028.original_roots hk kn
    · exact SweepChunks.N029.original_roots hk kn
    · exact SweepChunks.N030.original_roots hk kn
    · exact SweepChunks.N031.original_roots hk kn
    · exact SweepChunks.N032.original_roots hk kn

/-- Every original ordinary-descent row in the finite prefix splits over the reals. -/
theorem splits_through32 {n k : ℕ} (lo : 3 ≤ n) (hi : n ≤ 32)
    (hk : 3 ≤ k) (kn : k ≤ n) :
    ((DescentTwoLetters.row n k).map (Int.castRingHom ℝ)).Splits := by
  by_cases five : n = 5
  · subst n
    exact row_five_splits hk kn
  · exact (simple_roots_through32 lo hi five hk kn).1

#print axioms simple_roots_through32
#print axioms splits_through32

end LongCycleBounds.DescentNecklace
