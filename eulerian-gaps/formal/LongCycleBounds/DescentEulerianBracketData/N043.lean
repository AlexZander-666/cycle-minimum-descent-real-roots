import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentPackedData.C127L048.N043

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N043

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L048.N043 LongCycleBounds.DescentNecklace.Packed.C127L048.N043.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L048.N043 LongCycleBounds.DescentNecklace.Packed.C127L048.N043.rows

private theorem actual : RepresentativeChecks 43 previousNodes rows :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L048.N043 LongCycleBounds.DescentNecklace.Packed.C127L048.N043.dataChecks

private def first : LongCycleFinite.Dyadic := ⟨-4398046511104, 0⟩

private def gaps : List Window := [
  ⟨⟨-4397903904768, 0⟩, ⟨-24739712, 0⟩⟩,
  ⟨⟨-24608576, 0⟩, ⟨-165732, 0⟩⟩,
  ⟨⟨-164733, 0⟩, ⟨-319581, 5⟩⟩,
  ⟨⟨-159677, 4⟩, ⟨-415819, 8⟩⟩,
  ⟨⟨-415715, 8⟩, ⟨-461385, 10⟩⟩,
  ⟨⟨-115331, 8⟩, ⟨-11011, 6⟩⟩,
  ⟨⟨-352321, 11⟩, ⟨-41337, 9⟩⟩,
  ⟨⟨-82669, 10⟩, ⟨-89291, 11⟩⟩,
  ⟨⟨-357147, 13⟩, ⟨-213079, 13⟩⟩,
  ⟨⟨-213071, 13⟩, ⟨-136737, 13⟩⟩,
  ⟨⟨-273465, 14⟩, ⟨-370675, 15⟩⟩,
  ⟨⟨-46333, 12⟩, ⟨-65473, 13⟩⟩,
  ⟨⟨-130943, 14⟩, ⟨-191063, 15⟩⟩,
  ⟨⟨-382117, 16⟩, ⟨-71453, 14⟩⟩,
  ⟨⟨-142903, 15⟩, ⟨-435855, 17⟩⟩,
  ⟨⟨-435847, 17⟩, ⟨-168641, 16⟩⟩,
  ⟨⟨-337275, 17⟩, ⟨-263903, 17⟩⟩,
  ⟨⟨-131949, 16⟩, ⟨-416235, 18⟩⟩,
  ⟨⟨-104057, 16⟩, ⟨-329915, 18⟩⟩,
  ⟨⟨-164955, 17⟩, ⟨-262145, 18⟩⟩,
  ⟨⟨-524281, 19⟩, ⟨-104149, 17⟩⟩,
  ⟨⟨-416589, 19⟩, ⟨-41275, 16⟩⟩,
  ⟨⟨-165097, 18⟩, ⟨-65101, 17⟩⟩,
  ⟨⟨-520799, 20⟩, ⟨-407495, 20⟩⟩,
  ⟨⟨-407487, 20⟩, ⟨-315335, 20⟩⟩,
  ⟨⟨-315329, 20⟩, ⟨-480885, 21⟩⟩,
  ⟨⟨-120219, 19⟩, ⟨-359671, 21⟩⟩,
  ⟨⟨-22479, 17⟩, ⟨-262405, 21⟩⟩,
  ⟨⟨-262399, 21⟩, ⟨-370789, 22⟩⟩,
  ⟨⟨-92695, 20⟩, ⟨-251291, 22⟩⟩,
  ⟨⟨-502569, 23⟩, ⟨-322509, 23⟩⟩,
  ⟨⟨-322499, 23⟩, ⟨-384819, 24⟩⟩,
  ⟨⟨-192403, 23⟩, ⟨-207815, 24⟩⟩,
  ⟨⟨-207807, 24⟩, ⟨-390091, 26⟩⟩,
  ⟨⟨-390073, 26⟩, ⟨-74479, 25⟩⟩,
  ⟨⟨-74475, 25⟩, ⟨-165273, 28⟩⟩,
  ⟨⟨-82631, 27⟩, ⟨-430197, 32⟩⟩,
  ⟨⟨-430165, 32⟩, ⟨-415301, 36⟩⟩,
  ⟨⟨-207633, 35⟩, ⟨-11129, 38⟩⟩,
  ⟨⟨-356095, 43⟩, ⟨-262165, 60⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private theorem upper : upperOK (descentCoeffs 42) first gaps = true := by
  decide +kernel

private theorem lower : ∀ i : Fin (lastRepresentative 43 - 2),
    lowerOK (rows.getD i.val []) gaps = true := by
  decide +kernel

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 43) :
    StrictNegativeInterlacing (originalQuotient 43 k) (eulerian 42) 40 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N043
