import LongCycleBounds.DescentFiniteBlocks

/-! Size 14: frozen dyadic nodes and checked positive-count numerator rows. -/

namespace LongCycleBounds.DescentNecklace.N014

private def nodes : Array LongCycleFinite.Dyadic :=
#[
  ⟨-9502315, 13⟩,
  ⟨-9894933, 17⟩,
  ⟨-8872784, 19⟩,
  ⟨-12863317, 21⟩,
  ⟨-11640527, 22⟩,
  ⟨-11670558, 23⟩,
  ⟨-12059191, 24⟩,
  ⟨-12090302, 25⟩,
  ⟨-10940995, 26⟩,
  ⟨-15861706, 28⟩,
  ⟨-14223187, 30⟩,
  ⟨-14810864, 34⟩
]

private def rows : Array (List ℤ) :=
#[
  [3072, 949248, 43057680, 567801600, 2860568400, 6253690848, 6253690848, 2860568400, 567801600,
    43057680, 949248, 3072],
  [2352, 700668, 31293120, 409250580, 2052230040, 4476598440, 4476030936, 2051860680, 409447860,
    31382760, 707436, 2424],
  [1938, 560034, 24686370, 320603730, 1601637120, 3487817808, 3487370928, 1601341920, 320758830,
    24758670, 565614, 1998],
  [1602, 460242, 20283090, 263448450, 1316201760, 2866264176, 2865817296, 1315906560, 263603550,
    20355390, 465822, 1662],
  [1332, 370332, 16196940, 209938500, 1048428360, 2283362136, 2283362136, 1048428360, 209938500,
    16196940, 370332, 1332],
  [1161, 324069, 14172435, 183695535, 917375490, 1997942778, 1997939502, 917376390, 183696165,
    14171985, 324111, 1179]
]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 3000000 in
private theorem checks : RepresentativeChecks 14 nodes rows := by
  unfold RepresentativeChecks
  decide +kernel

theorem original_roots {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 14) :
    SimpleDescentRootPattern 14 k :=
  simpleDescentRoots_of_representativeChecks (by decide) (by decide) checks hk kn

#print axioms checks
#print axioms original_roots

end LongCycleBounds.DescentNecklace.N014
