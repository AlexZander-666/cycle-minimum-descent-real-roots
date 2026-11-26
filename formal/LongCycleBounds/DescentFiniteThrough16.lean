import LongCycleBounds.DescentFiniteData.N003
import LongCycleBounds.DescentFiniteData.N004
import LongCycleBounds.DescentFiniteData.N006
import LongCycleBounds.DescentFiniteData.N007
import LongCycleBounds.DescentFiniteData.N008
import LongCycleBounds.DescentFiniteData.N009
import LongCycleBounds.DescentFiniteData.N010
import LongCycleBounds.DescentFiniteData.N011
import LongCycleBounds.DescentFiniteData.N012
import LongCycleBounds.DescentFiniteData.N013
import LongCycleBounds.DescentFiniteData.N014
import LongCycleBounds.DescentFiniteData.N015
import LongCycleBounds.DescentFiniteData.N016

/-! Complete initial finite prefix for the ordinary-descent real-rootedness question. -/

namespace LongCycleBounds.DescentNecklace

/-- Every original cutoff has the simple negative pattern apart from the five-letter row. -/
theorem simple_roots_through16 {n k : ℕ} (lo : 3 ≤ n) (hi : n ≤ 16)
    (five : n ≠ 5) (hk : 3 ≤ k) (kn : k ≤ n) : SimpleDescentRootPattern n k := by
  interval_cases n
  · exact N003.original_roots hk kn
  · exact N004.original_roots hk kn
  · exact (five rfl).elim
  · exact N006.original_roots hk kn
  · exact N007.original_roots hk kn
  · exact N008.original_roots hk kn
  · exact N009.original_roots hk kn
  · exact N010.original_roots hk kn
  · exact N011.original_roots hk kn
  · exact N012.original_roots hk kn
  · exact N013.original_roots hk kn
  · exact N014.original_roots hk kn
  · exact N015.original_roots hk kn
  · exact N016.original_roots hk kn

/-- The full finite prefix, including the known repeated root at size five, splits over ℝ. -/
theorem splits_through16 {n k : ℕ} (lo : 3 ≤ n) (hi : n ≤ 16)
    (hk : 3 ≤ k) (kn : k ≤ n) :
    ((DescentTwoLetters.row n k).map (Int.castRingHom ℝ)).Splits := by
  by_cases five : n = 5
  · subst n
    exact row_five_splits hk kn
  · exact (simple_roots_through16 lo hi five hk kn).1

#print axioms simple_roots_through16
#print axioms splits_through16

end LongCycleBounds.DescentNecklace
