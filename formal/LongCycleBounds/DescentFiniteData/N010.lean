import LongCycleBounds.DescentFiniteBlocks

/-! Size 10: frozen dyadic nodes and checked positive-count numerator rows. -/

namespace LongCycleBounds.DescentNecklace.N010

private def nodes : Array LongCycleFinite.Dyadic :=
#[
  ⟨-8699434, 16⟩,
  ⟨-15952867, 20⟩,
  ⟨-8804804, 21⟩,
  ⟨-13178246, 23⟩,
  ⟨-10679531, 24⟩,
  ⟨-15984170, 26⟩,
  ⟨-8822081, 27⟩,
  ⟨-16177776, 31⟩
]

private def rows : Array (List ℤ) :=
#[
  [192, 10176, 100656, 293904, 293904, 100656, 10176, 192],
  [147, 7527, 73365, 212409, 212139, 73311, 7605, 153],
  [120, 5736, 54648, 157224, 157224, 54648, 5736, 120],
  [99, 4791, 45519, 131019, 131049, 45525, 4773, 105]
]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 3000000 in
private theorem checks : RepresentativeChecks 10 nodes rows := by
  unfold RepresentativeChecks
  decide +kernel

theorem original_roots {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 10) :
    SimpleDescentRootPattern 10 k :=
  simpleDescentRoots_of_representativeChecks (by decide) (by decide) checks hk kn

#print axioms checks
#print axioms original_roots

end LongCycleBounds.DescentNecklace.N010
