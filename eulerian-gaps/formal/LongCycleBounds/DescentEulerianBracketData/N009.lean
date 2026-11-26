import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentFiniteData.N009

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N009

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentFiniteData.N009 LongCycleBounds.DescentNecklace.N009.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentFiniteData.N009 LongCycleBounds.DescentNecklace.N009.rows

private theorem actual : RepresentativeChecks 9 previousNodes rows :=
  descentFrozenConst LongCycleBounds.DescentFiniteData.N009 LongCycleBounds.DescentNecklace.N009.checks

private def first : LongCycleFinite.Dyadic := ⟨-70721138039664005271466697571, 88⟩

private def gaps : List Window := [
  ⟨⟨-141436734043839671564221944163, 89⟩, ⟨-1080227949692319364775146851, 86⟩⟩,
  ⟨⟨-4319001225343026348861644323, 88⟩, ⟨-1942198700292292986251932835, 89⟩⟩,
  ⟨⟨-970980525230038281201108413, 88⟩, ⟨-309491807008210983348568655, 88⟩⟩,
  ⟨⟨-19341664435380068202595259, 84⟩, ⟨-197276011903121262663287411, 89⟩⟩,
  ⟨⟨-98630209851482862721143341, 88⟩, ⟨-11087906512965958733221815, 87⟩⟩,
  ⟨⟨-22173670795632754487942289, 88⟩, ⟨-2708771634244368490476525, 89⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private theorem upper : upperOK (descentCoeffs 8) first gaps = true := by
  decide +kernel

private theorem lower : ∀ i : Fin (lastRepresentative 9 - 2),
    lowerOK (rows.getD i.val []) gaps = true := by
  decide +kernel

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 9) :
    StrictNegativeInterlacing (originalQuotient 9 k) (eulerian 8) 6 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N009
