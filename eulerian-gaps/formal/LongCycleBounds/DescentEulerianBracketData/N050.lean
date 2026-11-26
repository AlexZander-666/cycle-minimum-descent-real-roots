import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentPackedData.C127L056.N050

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N050

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L056.N050 LongCycleBounds.DescentNecklace.Packed.C127L056.N050.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L056.N050 LongCycleBounds.DescentNecklace.Packed.C127L056.N050.rows

private theorem actual : RepresentativeChecks 50 previousNodes rows :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L056.N050 LongCycleBounds.DescentNecklace.Packed.C127L056.N050.dataChecks

private def first : LongCycleFinite.Dyadic := ⟨-562949953421312, 0⟩

private def gaps : List Window := [
  ⟨⟨-562931699810304, 0⟩, ⟨-436888576, 0⟩⟩,
  ⟨⟨-420111360, 0⟩, ⟨-1275340, 0⟩⟩,
  ⟨⟨-1257944, 0⟩, ⟨-397771, 3⟩⟩,
  ⟨⟨-49666, 0⟩, ⟨-49305, 3⟩⟩,
  ⟨⟨-6161, 0⟩, ⟨-22755, 4⟩⟩,
  ⟨⟨-182009, 7⟩, ⟨-487579, 10⟩⟩,
  ⟨⟨-487529, 10⟩, ⟨-51913, 8⟩⟩,
  ⟨⟨-207637, 10⟩, ⟨-208429, 11⟩⟩,
  ⟨⟨-416835, 12⟩, ⟨-470265, 13⟩⟩,
  ⟨⟨-470245, 13⟩, ⟨-9033, 8⟩⟩,
  ⟨⟨-289045, 13⟩, ⟨-47393, 11⟩⟩,
  ⟨⟨-94783, 12⟩, ⟨-261391, 14⟩⟩,
  ⟨⟨-32673, 11⟩, ⟨-374779, 15⟩⟩,
  ⟨⟨-374769, 15⟩, ⟨-277129, 15⟩⟩,
  ⟨⟨-277123, 15⟩, ⟨-210059, 15⟩⟩,
  ⟨⟨-420109, 16⟩, ⟨-162421, 15⟩⟩,
  ⟨⟨-81209, 14⟩, ⟨-510425, 17⟩⟩,
  ⟨⟨-31901, 13⟩, ⟨-203091, 16⟩⟩,
  ⟨⟨-406175, 17⟩, ⟨-326513, 17⟩⟩,
  ⟨⟨-326507, 17⟩, ⟨-132269, 16⟩⟩,
  ⟨⟨-132267, 16⟩, ⟨-215581, 17⟩⟩,
  ⟨⟨-107789, 16⟩, ⟨-352789, 18⟩⟩,
  ⟨⟨-352783, 18⟩, ⟨-289349, 18⟩⟩,
  ⟨⟨-289345, 18⟩, ⟨-118751, 17⟩⟩,
  ⟨⟨-474997, 19⟩, ⟨-194793, 18⟩⟩,
  ⟨⟨-97395, 17⟩, ⟨-318771, 19⟩⟩,
  ⟨⟨-159383, 18⟩, ⟨-259775, 19⟩⟩,
  ⟨⟨-259771, 19⟩, ⟨-210467, 19⟩⟩,
  ⟨⟨-420927, 20⟩, ⟨-169187, 19⟩⟩,
  ⟨⟨-338369, 20⟩, ⟨-134635, 19⟩⟩,
  ⟨⟨-269265, 20⟩, ⟨-423107, 21⟩⟩,
  ⟨⟨-423099, 21⟩, ⟨-327147, 21⟩⟩,
  ⟨⟨-327141, 21⟩, ⟨-61993, 19⟩⟩,
  ⟨⟨-495935, 22⟩, ⟨-366727, 22⟩⟩,
  ⟨⟨-366719, 22⟩, ⟨-262907, 22⟩⟩,
  ⟨⟨-65725, 20⟩, ⟨-362509, 23⟩⟩,
  ⟨⟨-90625, 21⟩, ⟨-475489, 24⟩⟩,
  ⟨⟨-118869, 22⟩, ⟨-18267, 20⟩⟩,
  ⟨⟨-146131, 23⟩, ⟨-164859, 24⟩⟩,
  ⟨⟨-164853, 24⟩, ⟨-330941, 26⟩⟩,
  ⟨⟨-330927, 26⟩, ⟨-8809, 22⟩⟩,
  ⟨⟨-140937, 26⟩, ⟨-11799, 24⟩⟩,
  ⟨⟨-188773, 28⟩, ⟨-87131, 29⟩⟩,
  ⟨⟨-348501, 31⟩, ⟨-345801, 34⟩⟩,
  ⟨⟨-345775, 34⟩, ⟨-1691, 31⟩⟩,
  ⟨⟨-108215, 37⟩, ⟨-332151, 47⟩⟩,
  ⟨⟨-332119, 47⟩, ⟨-262149, 67⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private theorem upper : upperOK (descentCoeffs 49) first gaps = true := by
  decide +kernel

private theorem lower : ∀ i : Fin (lastRepresentative 50 - 2),
    lowerOK (rows.getD i.val []) gaps = true := by
  decide +kernel

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 50) :
    StrictNegativeInterlacing (originalQuotient 50 k) (eulerian 49) 47 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N050
