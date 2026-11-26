import LongCycleBounds.DescentFiniteBlocks

/-! Size 7: frozen dyadic nodes and checked positive-count numerator rows. -/

namespace LongCycleBounds.DescentNecklace.N007

private def nodes : Array LongCycleFinite.Dyadic :=
#[
  ⟨-12132387, 19⟩,
  ⟨-15410016, 22⟩,
  ⟨-16777216, 24⟩,
  ⟨-9132858, 25⟩,
  ⟨-11600148, 28⟩
]

private def rows : Array (List ℤ) :=
#[
  [24, 264, 564, 264, 24],
  [18, 168, 348, 168, 18]
]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 3000000 in
private theorem checks : RepresentativeChecks 7 nodes rows := by
  unfold RepresentativeChecks
  decide +kernel

theorem original_roots {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 7) :
    SimpleDescentRootPattern 7 k :=
  simpleDescentRoots_of_representativeChecks (by decide) (by decide) checks hk kn

#print axioms checks
#print axioms original_roots

end LongCycleBounds.DescentNecklace.N007
