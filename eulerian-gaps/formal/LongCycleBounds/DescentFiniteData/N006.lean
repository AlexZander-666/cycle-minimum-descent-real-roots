import LongCycleBounds.DescentFiniteBlocks

/-! Size 6: frozen dyadic nodes and checked positive-count numerator rows. -/

namespace LongCycleBounds.DescentNecklace.N006

private def nodes : Array LongCycleFinite.Dyadic :=
#[
  ⟨-12842623, 20⟩,
  ⟨-8591518, 22⟩,
  ⟨-16380980, 25⟩,
  ⟨-10958625, 27⟩
]

private def rows : Array (List ℤ) :=
#[
  [12, 68, 68, 12],
  [9, 53, 47, 11]
]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 3000000 in
private theorem checks : RepresentativeChecks 6 nodes rows := by
  unfold RepresentativeChecks
  decide +kernel

theorem original_roots {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 6) :
    SimpleDescentRootPattern 6 k :=
  simpleDescentRoots_of_representativeChecks (by decide) (by decide) checks hk kn

#print axioms checks
#print axioms original_roots

end LongCycleBounds.DescentNecklace.N006
