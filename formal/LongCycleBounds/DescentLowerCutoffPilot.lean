import LongCycleBounds.DescentLowerCutoffChecks
import LongCycleBounds.DescentFiniteData.N003
import LongCycleBounds.DescentPackedData.C048L006.N006
import LongCycleBounds.DescentPackedData.C048L007.N007

/-! Small exact checks using the previously accepted nodes at sizes 3, 6 and 7. -/

namespace LongCycleBounds.DescentNecklace

namespace Size3

private def nodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentFiniteData.N003
    LongCycleBounds.DescentNecklace.N003.nodes

private def rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentFiniteData.N003
    LongCycleBounds.DescentNecklace.N003.rows

private theorem representative : RepresentativeChecks 3 nodes rows :=
  descentFrozenConst LongCycleBounds.DescentFiniteData.N003
    LongCycleBounds.DescentNecklace.N003.checks

private def one : List ℤ := [1, 4, 1]
private def two : List ℤ := [0, 2, 0]

private theorem oneCount : descentRowDP 3 1 = one := by
  decide +kernel

private theorem twoCount : descentRowDP 3 2 = two := by
  decide +kernel

private theorem oneSigns : rawMeshOK one nodes = true := by
  decide +kernel

private theorem twoSigns : rawMeshOK two nodes = true := by
  decide +kernel

theorem lower_cutoff_mesh : LowerCutoffMeshCertificate 3 := by
  refine ⟨nodes, rows, by decide, representative, ?_⟩
  intro k hk
  rcases hk with rfl | rfl
  · exact rawSharedSigns_of_numerator (by decide) oneCount oneSigns
  · exact rawSharedSigns_of_numerator (by decide) twoCount twoSigns

#print axioms lower_cutoff_mesh

end Size3

namespace Size6

private def nodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C048L006.N006
    LongCycleBounds.DescentNecklace.Packed.C048L006.N006.nodes

private def rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C048L006.N006
    LongCycleBounds.DescentNecklace.Packed.C048L006.N006.rows

private def codes : Fin 6 → ℕ → ℕ :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C048L006.N006
    LongCycleBounds.DescentNecklace.Packed.C048L006.N006.codes

private theorem checkedCodes (q : Fin 6) :
    PackedCutoffChecks 48 (q.val + 1) 3 (codes q) := by
  exact Packed.C048L006.checked ⟨q.val, q.isLt⟩

private theorem representative : RepresentativeChecks 6 nodes rows :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C048L006.N006
    LongCycleBounds.DescentNecklace.Packed.C048L006.N006.dataChecks

private def one : List ℤ := [1, 57, 302, 302, 57, 1]
private def two : List ℤ := [0, 16, 104, 120, 24, 1]

private theorem oneCount : descentRowDP 6 1 = one := by
  rw [← lowerCutoffNumerator_eq (bound := 48) (n := 6) (k := 1) (by decide) (by decide) (by decide)
    (by decide) codes checkedCodes]
  decide +kernel

private theorem twoCount : descentRowDP 6 2 = two := by
  rw [← lowerCutoffNumerator_eq (bound := 48) (n := 6) (k := 2) (by decide) (by decide) (by decide)
    (by decide) codes checkedCodes]
  decide +kernel

private theorem oneSigns : rawMeshOK one nodes = true := by
  decide +kernel

private theorem twoSigns : rawMeshOK two nodes = true := by
  decide +kernel

theorem lower_cutoff_mesh : LowerCutoffMeshCertificate 6 := by
  refine ⟨nodes, rows, by decide, representative, ?_⟩
  intro k hk
  rcases hk with rfl | rfl
  · exact rawSharedSigns_of_numerator (by decide) oneCount oneSigns
  · exact rawSharedSigns_of_numerator (by decide) twoCount twoSigns

#print axioms lower_cutoff_mesh

end Size6

namespace Size7

private def nodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C048L007.N007
    LongCycleBounds.DescentNecklace.Packed.C048L007.N007.nodes

private def rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C048L007.N007
    LongCycleBounds.DescentNecklace.Packed.C048L007.N007.rows

private def codes : Fin 7 → ℕ → ℕ :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C048L007.N007
    LongCycleBounds.DescentNecklace.Packed.C048L007.N007.codes

private theorem checkedCodes (q : Fin 7) :
    PackedCutoffChecks 48 (q.val + 1) 3 (codes q) := by
  exact Packed.C048L007.checked ⟨q.val, q.isLt⟩

private theorem representative : RepresentativeChecks 7 nodes rows :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C048L007.N007
    LongCycleBounds.DescentNecklace.Packed.C048L007.N007.dataChecks

private def one : List ℤ := [1, 120, 1191, 2416, 1191, 120, 1]
private def two : List ℤ := [0, 32, 392, 896, 480, 54, 0]

private theorem oneCount : descentRowDP 7 1 = one := by
  rw [← lowerCutoffNumerator_eq (bound := 48) (n := 7) (k := 1) (by decide) (by decide) (by decide)
    (by decide) codes checkedCodes]
  decide +kernel

private theorem twoCount : descentRowDP 7 2 = two := by
  rw [← lowerCutoffNumerator_eq (bound := 48) (n := 7) (k := 2) (by decide) (by decide) (by decide)
    (by decide) codes checkedCodes]
  decide +kernel

private theorem oneSigns : rawMeshOK one nodes = true := by
  decide +kernel

private theorem twoSigns : rawMeshOK two nodes = true := by
  decide +kernel

theorem lower_cutoff_mesh : LowerCutoffMeshCertificate 7 := by
  refine ⟨nodes, rows, by decide, representative, ?_⟩
  intro k hk
  rcases hk with rfl | rfl
  · exact rawSharedSigns_of_numerator (by decide) oneCount oneSigns
  · exact rawSharedSigns_of_numerator (by decide) twoCount twoSigns

#print axioms lower_cutoff_mesh

end Size7

end LongCycleBounds.DescentNecklace
