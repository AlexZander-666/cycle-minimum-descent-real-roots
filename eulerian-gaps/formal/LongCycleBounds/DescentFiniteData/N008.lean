import LongCycleBounds.DescentFiniteBlocks

/-! Size 8: frozen dyadic nodes and checked positive-count numerator rows. -/

namespace LongCycleBounds.DescentNecklace.N008

private def nodes : Array LongCycleFinite.Dyadic :=
#[
  ⟨-11080015, 18⟩,
  ⟨-12863317, 21⟩,
  ⟨-14597089, 23⟩,
  ⟨-9641476, 24⟩,
  ⟨-10940995, 26⟩,
  ⟨-12701922, 29⟩
]

private def rows : Array (List ℤ) :=
#[
  [48, 933, 3513, 3513, 933, 48],
  [36, 657, 2457, 2457, 657, 36],
  [30, 540, 1950, 1950, 540, 30]
]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 3000000 in
private theorem checks : RepresentativeChecks 8 nodes rows := by
  unfold RepresentativeChecks
  decide +kernel

theorem original_roots {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 8) :
    SimpleDescentRootPattern 8 k :=
  simpleDescentRoots_of_representativeChecks (by decide) (by decide) checks hk kn

#print axioms checks
#print axioms original_roots

end LongCycleBounds.DescentNecklace.N008
