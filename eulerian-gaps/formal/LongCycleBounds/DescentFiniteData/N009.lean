import LongCycleBounds.DescentFiniteBlocks

/-! Size 9: frozen dyadic nodes and checked positive-count numerator rows. -/

namespace LongCycleBounds.DescentNecklace.N009

private def nodes : Array LongCycleFinite.Dyadic :=
#[
  ⟨-9894933, 17⟩,
  ⟨-10277260, 20⟩,
  ⟨-11640527, 22⟩,
  ⟨-16777216, 24⟩,
  ⟨-12090302, 25⟩,
  ⟨-13694067, 27⟩,
  ⟨-14223187, 30⟩
]

private def rows : Array (List ℤ) :=
#[
  [96, 3136, 19660, 35080, 19660, 3136, 96],
  [74, 2308, 14210, 25280, 14210, 2308, 74],
  [56, 1624, 9800, 17360, 9800, 1624, 56]
]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 3000000 in
private theorem checks : RepresentativeChecks 9 nodes rows := by
  unfold RepresentativeChecks
  decide +kernel

theorem original_roots {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 9) :
    SimpleDescentRootPattern 9 k :=
  simpleDescentRoots_of_representativeChecks (by decide) (by decide) checks hk kn

#print axioms checks
#print axioms original_roots

end LongCycleBounds.DescentNecklace.N009
