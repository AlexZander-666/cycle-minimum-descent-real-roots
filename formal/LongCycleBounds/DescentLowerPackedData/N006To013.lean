import LongCycleBounds.DescentLowerPackedData.Alphabets127
import LongCycleBounds.DescentFiniteData.N006
import LongCycleBounds.DescentFiniteData.N007
import LongCycleBounds.DescentFiniteData.N008
import LongCycleBounds.DescentFiniteData.N009
import LongCycleBounds.DescentFiniteData.N010
import LongCycleBounds.DescentFiniteData.N011
import LongCycleBounds.DescentFiniteData.N012
import LongCycleBounds.DescentFiniteData.N013

/-! Original cutoffs one and two on the unchanged meshes at sizes 6 through 13. -/

namespace LongCycleBounds.DescentNecklace.LowerPacked
set_option maxRecDepth 65536
set_option maxHeartbeats 25000000
set_option Elab.async false

namespace N006

private def nodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentFiniteData.N006
    LongCycleBounds.DescentNecklace.N006.nodes

private def rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentFiniteData.N006
    LongCycleBounds.DescentNecklace.N006.rows

private theorem originalChecks : RepresentativeChecks 6 nodes rows := 
  descentFrozenConst LongCycleBounds.DescentFiniteData.N006
    LongCycleBounds.DescentNecklace.N006.checks

private def codes (i : Fin 6) : ℕ → ℕ := Alphabets127.codes ⟨i.val, by omega⟩

private theorem checkedCodes (i : Fin 6) : PackedCutoffChecks 127 (i.val + 1) 1 (codes i) :=
  Alphabets127.checked ⟨i.val, by omega⟩

private def one : List ℤ :=
  [1, 57, 302, 302, 57, 1]

private def two : List ℤ :=
  [0, 16, 104, 120, 24, 1]

private theorem oneCount : descentRowDP 6 1 = one := by
  rw [← cachedLowerNumerator_eq (bound := 127) (n := 6) (k := 1)
    (by decide) (by decide) (by decide) codes checkedCodes]
  decide +kernel

private theorem twoCount : descentRowDP 6 2 = two := by
  rw [← cachedLowerNumerator_eq (bound := 127) (n := 6) (k := 2)
    (by decide) (by decide) (by decide) codes checkedCodes]
  decide +kernel

private theorem oneSigns : rawMeshOK one nodes = true := by
  decide +kernel

private theorem twoSigns : rawMeshOK two nodes = true := by
  decide +kernel

theorem lower_cutoff_mesh : LowerCutoffMeshCertificate 6 := by
  refine ⟨nodes, rows, by decide, originalChecks, ?_⟩
  intro k hk
  rcases hk with rfl | rfl
  · exact rawSharedSigns_of_numerator (by decide) oneCount oneSigns
  · exact rawSharedSigns_of_numerator (by decide) twoCount twoSigns

#print axioms lower_cutoff_mesh
end N006

namespace N007

private def nodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentFiniteData.N007
    LongCycleBounds.DescentNecklace.N007.nodes

private def rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentFiniteData.N007
    LongCycleBounds.DescentNecklace.N007.rows

private theorem originalChecks : RepresentativeChecks 7 nodes rows := 
  descentFrozenConst LongCycleBounds.DescentFiniteData.N007
    LongCycleBounds.DescentNecklace.N007.checks

private def codes (i : Fin 7) : ℕ → ℕ := Alphabets127.codes ⟨i.val, by omega⟩

private theorem checkedCodes (i : Fin 7) : PackedCutoffChecks 127 (i.val + 1) 1 (codes i) :=
  Alphabets127.checked ⟨i.val, by omega⟩

private def one : List ℤ :=
  [1, 120, 1191, 2416, 1191, 120, 1]

private def two : List ℤ :=
  [0, 32, 392, 896, 480, 54, 0]

private theorem oneCount : descentRowDP 7 1 = one := by
  rw [← cachedLowerNumerator_eq (bound := 127) (n := 7) (k := 1)
    (by decide) (by decide) (by decide) codes checkedCodes]
  decide +kernel

private theorem twoCount : descentRowDP 7 2 = two := by
  rw [← cachedLowerNumerator_eq (bound := 127) (n := 7) (k := 2)
    (by decide) (by decide) (by decide) codes checkedCodes]
  decide +kernel

private theorem oneSigns : rawMeshOK one nodes = true := by
  decide +kernel

private theorem twoSigns : rawMeshOK two nodes = true := by
  decide +kernel

theorem lower_cutoff_mesh : LowerCutoffMeshCertificate 7 := by
  refine ⟨nodes, rows, by decide, originalChecks, ?_⟩
  intro k hk
  rcases hk with rfl | rfl
  · exact rawSharedSigns_of_numerator (by decide) oneCount oneSigns
  · exact rawSharedSigns_of_numerator (by decide) twoCount twoSigns

#print axioms lower_cutoff_mesh
end N007

namespace N008

private def nodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentFiniteData.N008
    LongCycleBounds.DescentNecklace.N008.nodes

private def rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentFiniteData.N008
    LongCycleBounds.DescentNecklace.N008.rows

private theorem originalChecks : RepresentativeChecks 8 nodes rows := 
  descentFrozenConst LongCycleBounds.DescentFiniteData.N008
    LongCycleBounds.DescentNecklace.N008.checks

private def codes (i : Fin 8) : ℕ → ℕ := Alphabets127.codes ⟨i.val, by omega⟩

private theorem checkedCodes (i : Fin 8) : PackedCutoffChecks 127 (i.val + 1) 1 (codes i) :=
  Alphabets127.checked ⟨i.val, by omega⟩

private def one : List ℤ :=
  [1, 247, 4293, 15619, 15619, 4293, 247, 1]

private def two : List ℤ :=
  [0, 64, 1368, 5544, 5984, 1764, 108, 1]

private theorem oneCount : descentRowDP 8 1 = one := by
  rw [← cachedLowerNumerator_eq (bound := 127) (n := 8) (k := 1)
    (by decide) (by decide) (by decide) codes checkedCodes]
  decide +kernel

private theorem twoCount : descentRowDP 8 2 = two := by
  rw [← cachedLowerNumerator_eq (bound := 127) (n := 8) (k := 2)
    (by decide) (by decide) (by decide) codes checkedCodes]
  decide +kernel

private theorem oneSigns : rawMeshOK one nodes = true := by
  decide +kernel

private theorem twoSigns : rawMeshOK two nodes = true := by
  decide +kernel

theorem lower_cutoff_mesh : LowerCutoffMeshCertificate 8 := by
  refine ⟨nodes, rows, by decide, originalChecks, ?_⟩
  intro k hk
  rcases hk with rfl | rfl
  · exact rawSharedSigns_of_numerator (by decide) oneCount oneSigns
  · exact rawSharedSigns_of_numerator (by decide) twoCount twoSigns

#print axioms lower_cutoff_mesh
end N008

namespace N009

private def nodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentFiniteData.N009
    LongCycleBounds.DescentNecklace.N009.nodes

private def rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentFiniteData.N009
    LongCycleBounds.DescentNecklace.N009.rows

private theorem originalChecks : RepresentativeChecks 9 nodes rows := 
  descentFrozenConst LongCycleBounds.DescentFiniteData.N009
    LongCycleBounds.DescentNecklace.N009.checks

private def codes (i : Fin 9) : ℕ → ℕ := Alphabets127.codes ⟨i.val, by omega⟩

private theorem checkedCodes (i : Fin 9) : PackedCutoffChecks 127 (i.val + 1) 1 (codes i) :=
  Alphabets127.checked ⟨i.val, by omega⟩

private def one : List ℤ :=
  [1, 502, 14608, 88234, 156190, 88234, 14608, 502, 1]

private def two : List ℤ :=
  [0, 128, 4552, 30384, 57640, 34520, 6048, 224, 0]

private theorem oneCount : descentRowDP 9 1 = one := by
  rw [← cachedLowerNumerator_eq (bound := 127) (n := 9) (k := 1)
    (by decide) (by decide) (by decide) codes checkedCodes]
  decide +kernel

private theorem twoCount : descentRowDP 9 2 = two := by
  rw [← cachedLowerNumerator_eq (bound := 127) (n := 9) (k := 2)
    (by decide) (by decide) (by decide) codes checkedCodes]
  decide +kernel

private theorem oneSigns : rawMeshOK one nodes = true := by
  decide +kernel

private theorem twoSigns : rawMeshOK two nodes = true := by
  decide +kernel

theorem lower_cutoff_mesh : LowerCutoffMeshCertificate 9 := by
  refine ⟨nodes, rows, by decide, originalChecks, ?_⟩
  intro k hk
  rcases hk with rfl | rfl
  · exact rawSharedSigns_of_numerator (by decide) oneCount oneSigns
  · exact rawSharedSigns_of_numerator (by decide) twoCount twoSigns

#print axioms lower_cutoff_mesh
end N009

namespace N010

private def nodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentFiniteData.N010
    LongCycleBounds.DescentNecklace.N010.nodes

private def rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentFiniteData.N010
    LongCycleBounds.DescentNecklace.N010.rows

private theorem originalChecks : RepresentativeChecks 10 nodes rows := 
  descentFrozenConst LongCycleBounds.DescentFiniteData.N010
    LongCycleBounds.DescentNecklace.N010.checks

private def codes (i : Fin 10) : ℕ → ℕ := Alphabets127.codes ⟨i.val, by omega⟩

private theorem checkedCodes (i : Fin 10) : PackedCutoffChecks 127 (i.val + 1) 1 (codes i) :=
  Alphabets127.checked ⟨i.val, by omega⟩

private def one : List ℤ :=
  [1, 1013, 47840, 455192, 1310354, 1310354, 455192, 47840, 1013, 1]

private def two : List ℤ :=
  [0, 256, 14680, 153400, 470504, 495320, 180416, 19936, 448, 1]

private theorem oneCount : descentRowDP 10 1 = one := by
  rw [← cachedLowerNumerator_eq (bound := 127) (n := 10) (k := 1)
    (by decide) (by decide) (by decide) codes checkedCodes]
  decide +kernel

private theorem twoCount : descentRowDP 10 2 = two := by
  rw [← cachedLowerNumerator_eq (bound := 127) (n := 10) (k := 2)
    (by decide) (by decide) (by decide) codes checkedCodes]
  decide +kernel

private theorem oneSigns : rawMeshOK one nodes = true := by
  decide +kernel

private theorem twoSigns : rawMeshOK two nodes = true := by
  decide +kernel

theorem lower_cutoff_mesh : LowerCutoffMeshCertificate 10 := by
  refine ⟨nodes, rows, by decide, originalChecks, ?_⟩
  intro k hk
  rcases hk with rfl | rfl
  · exact rawSharedSigns_of_numerator (by decide) oneCount oneSigns
  · exact rawSharedSigns_of_numerator (by decide) twoCount twoSigns

#print axioms lower_cutoff_mesh
end N010

namespace N011

private def nodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentFiniteData.N011
    LongCycleBounds.DescentNecklace.N011.nodes

private def rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentFiniteData.N011
    LongCycleBounds.DescentNecklace.N011.rows

private theorem originalChecks : RepresentativeChecks 11 nodes rows := 
  descentFrozenConst LongCycleBounds.DescentFiniteData.N011
    LongCycleBounds.DescentNecklace.N011.checks

private def codes (i : Fin 11) : ℕ → ℕ := Alphabets127.codes ⟨i.val, by omega⟩

private theorem checkedCodes (i : Fin 11) : PackedCutoffChecks 127 (i.val + 1) 1 (codes i) :=
  Alphabets127.checked ⟨i.val, by omega⟩

private def one : List ℤ :=
  [1, 2036, 152637, 2203488, 9738114, 15724248, 9738114, 2203488, 152637, 2036, 1]

private def two : List ℤ :=
  [0, 512, 46344, 731040, 3426320, 5794944, 3739512, 881152, 63840, 906, 0]

private theorem oneCount : descentRowDP 11 1 = one := by
  rw [← cachedLowerNumerator_eq (bound := 127) (n := 11) (k := 1)
    (by decide) (by decide) (by decide) codes checkedCodes]
  decide +kernel

private theorem twoCount : descentRowDP 11 2 = two := by
  rw [← cachedLowerNumerator_eq (bound := 127) (n := 11) (k := 2)
    (by decide) (by decide) (by decide) codes checkedCodes]
  decide +kernel

private theorem oneSigns : rawMeshOK one nodes = true := by
  decide +kernel

private theorem twoSigns : rawMeshOK two nodes = true := by
  decide +kernel

theorem lower_cutoff_mesh : LowerCutoffMeshCertificate 11 := by
  refine ⟨nodes, rows, by decide, originalChecks, ?_⟩
  intro k hk
  rcases hk with rfl | rfl
  · exact rawSharedSigns_of_numerator (by decide) oneCount oneSigns
  · exact rawSharedSigns_of_numerator (by decide) twoCount twoSigns

#print axioms lower_cutoff_mesh
end N011

namespace N012

private def nodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentFiniteData.N012
    LongCycleBounds.DescentNecklace.N012.nodes

private def rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentFiniteData.N012
    LongCycleBounds.DescentNecklace.N012.rows

private theorem originalChecks : RepresentativeChecks 12 nodes rows := 
  descentFrozenConst LongCycleBounds.DescentFiniteData.N012
    LongCycleBounds.DescentNecklace.N012.checks

private def codes (i : Fin 12) : ℕ → ℕ := Alphabets127.codes ⟨i.val, by omega⟩

private theorem checkedCodes (i : Fin 12) : PackedCutoffChecks 127 (i.val + 1) 1 (codes i) :=
  Alphabets127.checked ⟨i.val, by omega⟩

private def one : List ℤ :=
  [1, 4083, 478271, 10187685, 66318474, 162512286, 162512286, 66318474, 10187685, 478271, 4083,
  1]

private def two : List ℤ :=
  [0, 1024, 144152, 3341256, 22979920, 58753904, 60946248, 25746776, 4099168, 200580, 1812, 1]

private theorem oneCount : descentRowDP 12 1 = one := by
  rw [← cachedLowerNumerator_eq (bound := 127) (n := 12) (k := 1)
    (by decide) (by decide) (by decide) codes checkedCodes]
  decide +kernel

private theorem twoCount : descentRowDP 12 2 = two := by
  rw [← cachedLowerNumerator_eq (bound := 127) (n := 12) (k := 2)
    (by decide) (by decide) (by decide) codes checkedCodes]
  decide +kernel

private theorem oneSigns : rawMeshOK one nodes = true := by
  decide +kernel

private theorem twoSigns : rawMeshOK two nodes = true := by
  decide +kernel

theorem lower_cutoff_mesh : LowerCutoffMeshCertificate 12 := by
  refine ⟨nodes, rows, by decide, originalChecks, ?_⟩
  intro k hk
  rcases hk with rfl | rfl
  · exact rawSharedSigns_of_numerator (by decide) oneCount oneSigns
  · exact rawSharedSigns_of_numerator (by decide) twoCount twoSigns

#print axioms lower_cutoff_mesh
end N012

namespace N013

private def nodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentFiniteData.N013
    LongCycleBounds.DescentNecklace.N013.nodes

private def rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentFiniteData.N013
    LongCycleBounds.DescentNecklace.N013.rows

private theorem originalChecks : RepresentativeChecks 13 nodes rows := 
  descentFrozenConst LongCycleBounds.DescentFiniteData.N013
    LongCycleBounds.DescentNecklace.N013.checks

private def codes (i : Fin 13) : ℕ → ℕ := Alphabets127.codes ⟨i.val, by omega⟩

private theorem checkedCodes (i : Fin 13) : PackedCutoffChecks 127 (i.val + 1) 1 (codes i) :=
  Alphabets127.checked ⟨i.val, by omega⟩

private def one : List ℤ :=
  [1, 8178, 1479726, 45533450, 423281535, 1505621508, 2275172004, 1505621508, 423281535,
  45533450, 1479726, 8178, 1]

private def two : List ℤ :=
  [0, 2048, 443720, 14806544, 144970904, 536362784, 837901064, 571651696, 165626392, 18402472,
  621672, 3636, 0]

private theorem oneCount : descentRowDP 13 1 = one := by
  rw [← cachedLowerNumerator_eq (bound := 127) (n := 13) (k := 1)
    (by decide) (by decide) (by decide) codes checkedCodes]
  decide +kernel

private theorem twoCount : descentRowDP 13 2 = two := by
  rw [← cachedLowerNumerator_eq (bound := 127) (n := 13) (k := 2)
    (by decide) (by decide) (by decide) codes checkedCodes]
  decide +kernel

private theorem oneSigns : rawMeshOK one nodes = true := by
  decide +kernel

private theorem twoSigns : rawMeshOK two nodes = true := by
  decide +kernel

theorem lower_cutoff_mesh : LowerCutoffMeshCertificate 13 := by
  refine ⟨nodes, rows, by decide, originalChecks, ?_⟩
  intro k hk
  rcases hk with rfl | rfl
  · exact rawSharedSigns_of_numerator (by decide) oneCount oneSigns
  · exact rawSharedSigns_of_numerator (by decide) twoCount twoSigns

#print axioms lower_cutoff_mesh
end N013

end LongCycleBounds.DescentNecklace.LowerPacked
