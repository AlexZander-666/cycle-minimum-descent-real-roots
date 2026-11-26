import LongCycleBounds.DescentFiniteBlocks

/-! Size 11: frozen dyadic nodes and checked positive-count numerator rows. -/

namespace LongCycleBounds.DescentNecklace.N011

private def nodes : Array LongCycleFinite.Dyadic :=
#[
  ⟨-15123388, 16⟩,
  ⟨-12132387, 19⟩,
  ⟨-12863317, 21⟩,
  ⟨-9732927, 22⟩,
  ⟨-16777216, 24⟩,
  ⟨-14459935, 25⟩,
  ⟨-10940995, 26⟩,
  ⟨-11600148, 28⟩,
  ⟨-9305950, 31⟩
]

private def rows : Array (List ℤ) :=
#[
  [384, 32256, 483996, 2173824, 3526560, 2173824, 483996, 32256, 384],
  [294, 23760, 350328, 1558608, 2519760, 1557312, 350592, 24000, 306],
  [240, 18792, 273756, 1210632, 1953300, 1209336, 274020, 19032, 252],
  [186, 13872, 200328, 885264, 1429500, 885264, 200328, 13872, 186]
]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 3000000 in
private theorem checks : RepresentativeChecks 11 nodes rows := by
  unfold RepresentativeChecks
  decide +kernel

theorem original_roots {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 11) :
    SimpleDescentRootPattern 11 k :=
  simpleDescentRoots_of_representativeChecks (by decide) (by decide) checks hk kn

#print axioms checks
#print axioms original_roots

end LongCycleBounds.DescentNecklace.N011
