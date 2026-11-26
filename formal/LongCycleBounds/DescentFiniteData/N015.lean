import LongCycleBounds.DescentFiniteBlocks

/-! Size 15: frozen dyadic nodes and checked positive-count numerator rows. -/

namespace LongCycleBounds.DescentNecklace.N015

private def nodes : Array LongCycleFinite.Dyadic :=
#[
  ⟨-16117061, 13⟩,
  ⟨-14435886, 17⟩,
  ⟨-12132387, 19⟩,
  ⟨-8555533, 20⟩,
  ⟨-15410016, 22⟩,
  ⟨-15670441, 23⟩,
  ⟨-16777216, 24⟩,
  ⟨-8981080, 24⟩,
  ⟨-9132858, 25⟩,
  ⟨-16449881, 27⟩,
  ⟨-11600148, 28⟩,
  ⟨-9749141, 30⟩,
  ⟨-8732206, 34⟩
]

private def rows : Array (List ℤ) :=
#[
  [6144, 2887680, 183621692, 3312641296, 22841402416, 69520835632, 100058866264, 69520835632,
    22841402416, 3312641296, 183621692, 2887680, 6144],
  [4704, 2132664, 133591784, 2390647432, 16406625660, 49807484704, 71622138560, 49799977632,
    16406366080, 2392679432, 134046600, 2154680, 4852],
  [3876, 1702464, 105226592, 1869960352, 12783687180, 38731807072, 55661700416, 38726660448,
    12783495100, 1871355872, 105542880, 1718144, 3988],
  [3226, 1411024, 87172396, 1549124976, 10590856374, 32088789760, 46114706792, 32083643136,
    10590664294, 1550520496, 87488684, 1426704, 3338],
  [2722, 1165744, 71655020, 1271312336, 8687289534, 26319721728, 37827325032, 26319721728,
    8687289534, 1271312336, 71655020, 1165744, 2722],
  [2182, 921664, 56539340, 1002748736, 6851799834, 20759173248, 29835921192, 20759173248,
    6851799834, 1002748736, 56539340, 921664, 2182]
]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 3000000 in
private theorem checks : RepresentativeChecks 15 nodes rows := by
  unfold RepresentativeChecks
  decide +kernel

theorem original_roots {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 15) :
    SimpleDescentRootPattern 15 k :=
  simpleDescentRoots_of_representativeChecks (by decide) (by decide) checks hk kn

#print axioms checks
#print axioms original_roots

end LongCycleBounds.DescentNecklace.N015
