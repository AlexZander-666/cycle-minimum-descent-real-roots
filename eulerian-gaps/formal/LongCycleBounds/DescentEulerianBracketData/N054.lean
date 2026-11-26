import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentPackedData.C127L056.N054

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N054

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L056.N054 LongCycleBounds.DescentNecklace.Packed.C127L056.N054.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L056.N054 LongCycleBounds.DescentNecklace.Packed.C127L056.N054.rows

private theorem actual : RepresentativeChecks 54 previousNodes rows :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L056.N054 LongCycleBounds.DescentNecklace.Packed.C127L056.N054.dataChecks

private def first : LongCycleFinite.Dyadic := ⟨-9007199254740992, 0⟩

private def gaps : List Window := [
  ⟨⟨-9006907196964864, 0⟩, ⟨-2223636480, 0⟩⟩,
  ⟨⟨-1955201024, 0⟩, ⟨-4083984, 0⟩⟩,
  ⟨⟨-3997592, 0⟩, ⟨-494611, 2⟩⟩,
  ⟨⟨-246945, 1⟩, ⟨-419499, 5⟩⟩,
  ⟨⟨-419327, 5⟩, ⟨-174007, 6⟩⟩,
  ⟨⟨-173973, 6⟩, ⟨-431713, 9⟩⟩,
  ⟨⟨-431663, 9⟩, ⟨-86829, 8⟩⟩,
  ⟨⟨-43411, 7⟩, ⟨-20855, 7⟩⟩,
  ⟨⟨-83415, 9⟩, ⟨-363835, 12⟩⟩,
  ⟨⟨-363817, 12⟩, ⟨-217721, 12⟩⟩,
  ⟨⟨-435425, 13⟩, ⟨-279599, 13⟩⟩,
  ⟨⟨-279589, 13⟩, ⟨-379147, 14⟩⟩,
  ⟨⟨-1481, 6⟩, ⟨-134149, 13⟩⟩,
  ⟨⟨-268291, 14⟩, ⟨-392881, 15⟩⟩,
  ⟨⟨-49109, 12⟩, ⟨-147833, 14⟩⟩,
  ⟨⟨-73915, 13⟩, ⟨-227517, 15⟩⟩,
  ⟨⟨-455025, 16⟩, ⟨-89143, 14⟩⟩,
  ⟨⟨-356565, 16⟩, ⟨-283599, 16⟩⟩,
  ⟨⟨-141797, 15⟩, ⟨-228305, 16⟩⟩,
  ⟨⟨-456603, 17⟩, ⟨-46401, 14⟩⟩,
  ⟨⟨-185601, 16⟩, ⟨-304155, 17⟩⟩,
  ⟨⟨-152075, 16⟩, ⟨-250747, 17⟩⟩,
  ⟨⟨-501487, 18⟩, ⟨-415329, 18⟩⟩,
  ⟨⟨-415323, 18⟩, ⟨-172537, 17⟩⟩,
  ⟨⟨-345069, 18⟩, ⟨-287237, 18⟩⟩,
  ⟨⟨-287233, 18⟩, ⟨-119623, 17⟩⟩,
  ⟨⟨-239243, 18⟩, ⟨-199147, 18⟩⟩,
  ⟨⟨-24893, 15⟩, ⟨-165459, 18⟩⟩,
  ⟨⟨-330913, 19⟩, ⟨-274065, 19⟩⟩,
  ⟨⟨-274061, 19⟩, ⟨-451873, 20⟩⟩,
  ⟨⟨-451867, 20⟩, ⟨-370251, 20⟩⟩,
  ⟨⟨-185123, 19⟩, ⟨-150501, 19⟩⟩,
  ⟨⟨-300997, 20⟩, ⟨-121159, 19⟩⟩,
  ⟨⟨-484629, 21⟩, ⟨-96363, 19⟩⟩,
  ⟨⟨-385445, 21⟩, ⟨-302049, 21⟩⟩,
  ⟨⟨-302043, 21⟩, ⟨-58107, 19⟩⟩,
  ⟨⟨-464847, 22⟩, ⟨-349829, 22⟩⟩,
  ⟨⟨-174911, 21⟩, ⟨-512275, 23⟩⟩,
  ⟨⟨-64033, 20⟩, ⟨-362507, 23⟩⟩,
  ⟨⟨-362499, 23⟩, ⟨-245789, 23⟩⟩,
  ⟨⟨-245783, 23⟩, ⟨-39455, 21⟩⟩,
  ⟨⟨-157815, 23⟩, ⟨-377767, 25⟩⟩,
  ⟨⟨-188877, 24⟩, ⟨-411901, 26⟩⟩,
  ⟨⟨-205943, 25⟩, ⟨-395751, 27⟩⟩,
  ⟨⟨-197867, 26⟩, ⟨-318367, 28⟩⟩,
  ⟨⟨-318351, 28⟩, ⟨-98745, 28⟩⟩,
  ⟨⟨-394957, 30⟩, ⟨-327723, 32⟩⟩,
  ⟨⟨-81925, 30⟩, ⟨-139031, 34⟩⟩,
  ⟨⟨-278041, 35⟩, ⟨-16959, 36⟩⟩,
  ⟨⟨-271321, 40⟩, ⟨-8191, 44⟩⟩,
  ⟨⟨-524175, 50⟩, ⟨-262149, 71⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private theorem upper : upperOK (descentCoeffs 53) first gaps = true := by
  decide +kernel

private theorem lower : ∀ i : Fin (lastRepresentative 54 - 2),
    lowerOK (rows.getD i.val []) gaps = true := by
  decide +kernel

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 54) :
    StrictNegativeInterlacing (originalQuotient 54 k) (eulerian 53) 51 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N054
