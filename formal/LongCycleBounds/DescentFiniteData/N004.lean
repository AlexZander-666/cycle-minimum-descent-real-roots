import LongCycleBounds.DescentFiniteBlocks

/-! Size 4: frozen dyadic nodes and checked positive-count numerator rows. -/

namespace LongCycleBounds.DescentNecklace.N004

private def nodes : Array LongCycleFinite.Dyadic :=
#[
  ⟨-11640527, 22⟩,
  ⟨-12090302, 25⟩
]

private def rows : Array (List ℤ) :=
#[
  [3, 3]
]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 3000000 in
private theorem checks : RepresentativeChecks 4 nodes rows := by
  unfold RepresentativeChecks
  decide +kernel

theorem original_roots {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 4) :
    SimpleDescentRootPattern 4 k :=
  simpleDescentRoots_of_representativeChecks (by decide) (by decide) checks hk kn

#print axioms checks
#print axioms original_roots

end LongCycleBounds.DescentNecklace.N004
