import LongCycleBounds.DescentFiniteThrough32
import LongCycleBounds.DescentFiniteCertificatesThrough32
import LongCycleBounds.DescentSweepChunkData.N033
import LongCycleBounds.DescentSweepChunkData.N034
import LongCycleBounds.DescentSweepChunkData.N035
import LongCycleBounds.DescentSweepChunkData.N036
import LongCycleBounds.DescentSweepChunkData.N037
import LongCycleBounds.DescentSweepChunkData.N038
import LongCycleBounds.DescentSweepChunkData.N039
import LongCycleBounds.DescentSweepChunkData.N040

/-! The ordinary-descent finite prefix through size 40. -/

namespace LongCycleBounds.DescentNecklace

/-- The full simple-root pattern for ordinary descent rows apart from the size-five exception. -/
theorem simple_roots_through40 {n k : ℕ} (lo : 3 ≤ n) (hi : n ≤ 40)
    (five : n ≠ 5) (hk : 3 ≤ k) (kn : k ≤ n) : SimpleDescentRootPattern n k := by
  by_cases small : n ≤ 32
  · exact simple_roots_through32 lo small five hk kn
  · interval_cases n
    · exact SweepChunks.N033.original_roots hk kn
    · exact SweepChunks.N034.original_roots hk kn
    · exact SweepChunks.N035.original_roots hk kn
    · exact SweepChunks.N036.original_roots hk kn
    · exact SweepChunks.N037.original_roots hk kn
    · exact SweepChunks.N038.original_roots hk kn
    · exact SweepChunks.N039.original_roots hk kn
    · exact SweepChunks.N040.original_roots hk kn

/-- Every original ordinary-descent row in the finite prefix splits over the reals. -/
theorem splits_through40 {n k : ℕ} (lo : 3 ≤ n) (hi : n ≤ 40)
    (hk : 3 ≤ k) (kn : k ≤ n) :
    ((DescentTwoLetters.row n k).map (Int.castRingHom ℝ)).Splits := by
  by_cases five : n = 5
  · subst n
    exact row_five_splits hk kn
  · exact (simple_roots_through40 lo hi five hk kn).1

/-- The same common representative mesh is available for every audited nonexceptional size. -/
theorem finite_certificate_through40 {n : ℕ} (lo : 3 ≤ n) (hi : n ≤ 40) (five : n ≠ 5) :
    ∃ nodes : Array LongCycleFinite.Dyadic, ∃ rows : Array (List ℤ),
      nodes.size = n - 2 ∧ RepresentativeChecks n nodes rows := by
  by_cases small : n ≤ 32
  · exact FrozenCertificates.finite_certificate_through32 lo small five
  · interval_cases n
    · exact SweepChunks.N033.finite_certificate
    · exact SweepChunks.N034.finite_certificate
    · exact SweepChunks.N035.finite_certificate
    · exact SweepChunks.N036.finite_certificate
    · exact SweepChunks.N037.finite_certificate
    · exact SweepChunks.N038.finite_certificate
    · exact SweepChunks.N039.finite_certificate
    · exact SweepChunks.N040.finite_certificate

#print axioms finite_certificate_through40
#print axioms simple_roots_through40
#print axioms splits_through40

end LongCycleBounds.DescentNecklace
