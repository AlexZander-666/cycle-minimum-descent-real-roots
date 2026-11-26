import LongCycleBounds.DescentFiniteBlocks

/-! Size 12: frozen dyadic nodes and checked positive-count numerator rows. -/

namespace LongCycleBounds.DescentNecklace.N012

private def nodes : Array LongCycleFinite.Dyadic :=
#[
  ⟨-13033225, 15⟩,
  ⟨-9090808, 18⟩,
  ⟨-9169822, 20⟩,
  ⟨-13807009, 22⟩,
  ⟨-12284435, 23⟩,
  ⟨-11456570, 24⟩,
  ⟨-10193192, 25⟩,
  ⟨-15347897, 27⟩,
  ⟨-15481297, 29⟩,
  ⟨-10798363, 32⟩
]

private def rows : Array (List ℤ) :=
#[
  [768, 100608, 2226268, 14740088, 36370928, 36370928, 14740088, 2226268, 100608, 768],
  [588, 74058, 1611043, 10572953, 25981003, 25973569, 10569229, 1613759, 74749, 609],
  [488, 59638, 1280183, 8345553, 20445683, 20438249, 8341829, 1282899, 60329, 509],
  [380, 46066, 989087, 6450153, 15802979, 15795545, 6446429, 991803, 46757, 401],
  [335, 39865, 849010, 5526430, 13542760, 13542760, 5526430, 849010, 39865, 335]
]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 3000000 in
private theorem checks : RepresentativeChecks 12 nodes rows := by
  unfold RepresentativeChecks
  decide +kernel

theorem original_roots {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 12) :
    SimpleDescentRootPattern 12 k :=
  simpleDescentRoots_of_representativeChecks (by decide) (by decide) checks hk kn

#print axioms checks
#print axioms original_roots

end LongCycleBounds.DescentNecklace.N012
