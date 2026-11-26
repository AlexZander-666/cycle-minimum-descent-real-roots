import LongCycleBounds.DescentFiniteBlocks

/-! Size 3: frozen dyadic nodes and checked positive-count numerator rows. -/

namespace LongCycleBounds.DescentNecklace.N003

private def nodes : Array LongCycleFinite.Dyadic :=
#[
  ⟨-16777216, 24⟩
]

private def rows : Array (List ℤ) :=
#[
  [2]
]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 3000000 in
private theorem checks : RepresentativeChecks 3 nodes rows := by
  unfold RepresentativeChecks
  decide +kernel

theorem original_roots {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 3) :
    SimpleDescentRootPattern 3 k :=
  simpleDescentRoots_of_representativeChecks (by decide) (by decide) checks hk kn

#print axioms checks
#print axioms original_roots

end LongCycleBounds.DescentNecklace.N003
