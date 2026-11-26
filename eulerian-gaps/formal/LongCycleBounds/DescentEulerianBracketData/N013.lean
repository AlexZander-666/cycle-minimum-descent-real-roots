import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentFiniteData.N013

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N013

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentFiniteData.N013 LongCycleBounds.DescentNecklace.N013.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentFiniteData.N013 LongCycleBounds.DescentNecklace.N013.rows

private theorem actual : RepresentativeChecks 13 previousNodes rows :=
  descentFrozenConst LongCycleBounds.DescentFiniteData.N013 LongCycleBounds.DescentNecklace.N013.checks

private def first : LongCycleFinite.Dyadic := ⟨-2828139110306588238120555064598795316419803205179, 149⟩

private def gaps : List Window := [
  ⟨⟨-707011503738483365320549263058228325983534691903, 147⟩, ⟨-8454279290679799193596501301240231750672033627, 146⟩⟩,
  ⟨⟨-33775768779778370371650338609200800429068999227, 148⟩, ⟨-11541814783135513266888598455302900408173258111, 149⟩⟩,
  ⟨⟨-5769843113491353046363926244916928090409493523, 148⟩, ⟨-463975654637584131562307811819333092197515841, 146⟩⟩,
  ⟨⟨-231967498464555468598016813086570987592830957, 145⟩, ⟨-96748454095873698216795163337212525271413757, 145⟩⟩,
  ⟨⟨-48371284593632768389113409783802262746734231, 144⟩, ⟨-178407025757742747327906104456440136122712533, 147⟩⟩,
  ⟨⟨-356795519179086060700222644923146042598821041, 148⟩, ⟨-10281078185504925634784545347714077940249753, 144⟩⟩,
  ⟨⟨-164488777426505008161042274526624629246314599, 148⟩, ⟨-8575977923111317803354413122396533079943945, 145⟩⟩,
  ⟨⟨-68603850722545459539512198683750617446792145, 148⟩, ⟨-22066123517670966348571367952814105922026245, 148⟩⟩,
  ⟨⟨-44129063454327648149489459725128425711809335, 149⟩, ⟨-1882595510225503603776026594272035920757645, 147⟩⟩,
  ⟨⟨-3764839123994719349704184434449609918501195, 148⟩, ⟨-90045421623050328813069280501586018296875, 148⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private theorem upper : upperOK (descentCoeffs 12) first gaps = true := by
  decide +kernel

private theorem lower : ∀ i : Fin (lastRepresentative 13 - 2),
    lowerOK (rows.getD i.val []) gaps = true := by
  decide +kernel

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 13) :
    StrictNegativeInterlacing (originalQuotient 13 k) (eulerian 12) 10 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N013
