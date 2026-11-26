import LongCycleBounds.DescentFiniteBlocks

/-! Size 13: frozen dyadic nodes and checked positive-count numerator rows. -/

namespace LongCycleBounds.DescentNecklace.N013

private def nodes : Array LongCycleFinite.Dyadic :=
#[
  ⟨-11157750, 14⟩,
  ⟨-13471432, 18⟩,
  ⟨-12842623, 20⟩,
  ⟨-9520920, 21⟩,
  ⟨-8591518, 22⟩,
  ⟨-16777216, 24⟩,
  ⟨-16380980, 25⟩,
  ⟨-14781921, 26⟩,
  ⟨-10958625, 27⟩,
  ⟨-10447107, 29⟩,
  ⟨-12613429, 33⟩
]

private def rows : Array (List ℤ) :=
#[
  [1536, 310272, 9911172, 93737832, 336152292, 509202624, 336152292, 93737832, 9911172, 310272,
    1536],
  [1176, 228768, 7188948, 67405368, 240635808, 363952680, 240571800, 67410600, 7204080, 230760,
    1212],
  [972, 184104, 5715144, 53225784, 189342384, 286044360, 189278376, 53231016, 5730276, 186096,
    1008],
  [792, 147744, 4578444, 42638184, 151698624, 229178040, 151634616, 42643416, 4593576, 149736,
    828],
  [630, 113820, 3502590, 32560080, 115817100, 175013160, 115817100, 32560080, 3502590, 113820,
    630]
]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 3000000 in
private theorem checks : RepresentativeChecks 13 nodes rows := by
  unfold RepresentativeChecks
  decide +kernel

theorem original_roots {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 13) :
    SimpleDescentRootPattern 13 k :=
  simpleDescentRoots_of_representativeChecks (by decide) (by decide) checks hk kn

#print axioms checks
#print axioms original_roots

end LongCycleBounds.DescentNecklace.N013
