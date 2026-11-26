import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentPackedData.C127L064.N060

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N060

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L064.N060 LongCycleBounds.DescentNecklace.Packed.C127L064.N060.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L064.N060 LongCycleBounds.DescentNecklace.Packed.C127L064.N060.rows

private theorem actual : RepresentativeChecks 60 previousNodes rows :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L064.N060 LongCycleBounds.DescentNecklace.Packed.C127L064.N060.dataChecks

private def first : LongCycleFinite.Dyadic := ⟨-576460752303423488, 0⟩

private def gaps : List Window := [
  ⟨⟨-576442060605751296, 0⟩, ⟨-31885361152, 0⟩⟩,
  ⟨⟨-14705688576, 0⟩, ⟨-23442048, 0⟩⟩,
  ⟨⟨-22545472, 0⟩, ⟨-482330, 0⟩⟩,
  ⟨⟨-481305, 0⟩, ⟨-161485, 2⟩⟩,
  ⟨⟨-161399, 2⟩, ⟨-456207, 6⟩⟩,
  ⟨⟨-456099, 6⟩, ⟨-251839, 7⟩⟩,
  ⟨⟨-503609, 8⟩, ⟨-371345, 9⟩⟩,
  ⟨⟨-371311, 9⟩, ⟨-333559, 10⟩⟩,
  ⟨⟨-10423, 5⟩, ⟨-172495, 10⟩⟩,
  ⟨⟨-86243, 9⟩, ⟨-197935, 11⟩⟩,
  ⟨⟨-395853, 12⟩, ⟨-491465, 13⟩⟩,
  ⟨⟨-61431, 10⟩, ⟨-81061, 11⟩⟩,
  ⟨⟨-162117, 12⟩, ⟨-448935, 14⟩⟩,
  ⟨⟨-448923, 14⟩, ⟨-322975, 14⟩⟩,
  ⟨⟨-322967, 14⟩, ⟨-479449, 15⟩⟩,
  ⟨⟨-479439, 15⟩, ⟨-365071, 15⟩⟩,
  ⟨⟨-365063, 15⟩, ⟨-141949, 14⟩⟩,
  ⟨⟨-70973, 13⟩, ⟨-224669, 15⟩⟩,
  ⟨⟨-224665, 15⟩, ⟨-360809, 16⟩⟩,
  ⟨⟨-360803, 16⟩, ⟨-293263, 16⟩⟩,
  ⟨⟨-146629, 15⟩, ⟨-481565, 17⟩⟩,
  ⟨⟨-240779, 16⟩, ⟨-398715, 17⟩⟩,
  ⟨⟨-398709, 17⟩, ⟨-20775, 13⟩⟩,
  ⟨⟨-332395, 17⟩, ⟨-278659, 17⟩⟩,
  ⟨⟨-278655, 17⟩, ⟨-117315, 16⟩⟩,
  ⟨⟨-234627, 17⟩, ⟨-396429, 18⟩⟩,
  ⟨⟨-49553, 15⟩, ⟨-167839, 17⟩⟩,
  ⟨⟨-167837, 17⟩, ⟨-17789, 14⟩⟩,
  ⟨⟨-71155, 16⟩, ⟨-241443, 18⟩⟩,
  ⟨⟨-7545, 13⟩, ⟨-409443, 19⟩⟩,
  ⟨⟨-204719, 18⟩, ⟨-346697, 19⟩⟩,
  ⟨⟨-86673, 17⟩, ⟨-36611, 16⟩⟩,
  ⟨⟨-73221, 17⟩, ⟨-493227, 20⟩⟩,
  ⟨⟨-493221, 20⟩, ⟨-51685, 17⟩⟩,
  ⟨⟨-206737, 19⟩, ⟨-344709, 20⟩⟩,
  ⟨⟨-2693, 13⟩, ⟨-285405, 20⟩⟩,
  ⟨⟨-285401, 20⟩, ⟨-58583, 18⟩⟩,
  ⟨⟨-468657, 21⟩, ⟨-380925, 21⟩⟩,
  ⟨⟨-380919, 21⟩, ⟨-305873, 21⟩⟩,
  ⟨⟨-76467, 19⟩, ⟨-121031, 20⟩⟩,
  ⟨⟨-121029, 20⟩, ⟨-376479, 22⟩⟩,
  ⟨⟨-47059, 19⟩, ⟨-286665, 22⟩⟩,
  ⟨⟨-286659, 22⟩, ⟨-425545, 23⟩⟩,
  ⟨⟨-6649, 17⟩, ⟨-76539, 21⟩⟩,
  ⟨⟨-306149, 23⟩, ⟨-423881, 24⟩⟩,
  ⟨⟨-211935, 23⟩, ⟨-279667, 24⟩⟩,
  ⟨⟨-279659, 24⟩, ⟨-5425, 19⟩⟩,
  ⟨⟨-347189, 25⟩, ⟨-199203, 25⟩⟩,
  ⟨⟨-49799, 23⟩, ⟨-25753, 23⟩⟩,
  ⟨⟨-412031, 27⟩, ⟨-370153, 28⟩⟩,
  ⟨⟨-46267, 25⟩, ⟨-136447, 28⟩⟩,
  ⟨⟨-272879, 29⟩, ⟨-37667, 28⟩⟩,
  ⟨⟨-301317, 31⟩, ⟨-425565, 34⟩⟩,
  ⟨⟨-6649, 28⟩, ⟨-142583, 36⟩⟩,
  ⟨⟨-35643, 34⟩, ⟨-47795, 40⟩⟩,
  ⟨⟨-382327, 43⟩, ⟨-367843, 53⟩⟩,
  ⟨⟨-5747, 47⟩, ⟨-262149, 77⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private theorem upper : upperOK (descentCoeffs 59) first gaps = true := by
  decide +kernel

private theorem lower : ∀ i : Fin (lastRepresentative 60 - 2),
    lowerOK (rows.getD i.val []) gaps = true := by
  decide +kernel

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 60) :
    StrictNegativeInterlacing (originalQuotient 60 k) (eulerian 59) 57 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N060
