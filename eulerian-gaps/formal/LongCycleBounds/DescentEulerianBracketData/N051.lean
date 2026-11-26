import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentPackedData.C127L056.N051

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N051

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L056.N051 LongCycleBounds.DescentNecklace.Packed.C127L056.N051.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L056.N051 LongCycleBounds.DescentNecklace.Packed.C127L056.N051.rows

private theorem actual : RepresentativeChecks 51 previousNodes rows :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L056.N051 LongCycleBounds.DescentNecklace.Packed.C127L056.N051.dataChecks

private def first : LongCycleFinite.Dyadic := ⟨-1125899906842624, 0⟩

private def gaps : List Window := [
  ⟨⟨-1125863399620608, 0⟩, ⟨-663377920, 0⟩⟩,
  ⟨⟨-629821440, 0⟩, ⟨-1709940, 0⟩⟩,
  ⟨⟨-1683860, 0⟩, ⟨-499755, 3⟩⟩,
  ⟨⟨-62395, 0⟩, ⟨-59563, 3⟩⟩,
  ⟨⟨-476333, 6⟩, ⟨-214131, 7⟩⟩,
  ⟨⟨-428187, 8⟩, ⟨-4397, 3⟩⟩,
  ⟨⟨-140689, 8⟩, ⟨-472625, 11⟩⟩,
  ⟨⟨-472589, 11⟩, ⟨-234635, 11⟩⟩,
  ⟨⟨-117311, 10⟩, ⟨-262479, 12⟩⟩,
  ⟨⟨-262467, 12⟩, ⟨-20035, 9⟩⟩,
  ⟨⟨-80137, 11⟩, ⟨-209151, 13⟩⟩,
  ⟨⟨-418289, 14⟩, ⟨-287225, 14⟩⟩,
  ⟨⟨-287217, 14⟩, ⟨-205273, 14⟩⟩,
  ⟨⟨-51317, 12⟩, ⟨-302885, 15⟩⟩,
  ⟨⟨-151439, 14⟩, ⟨-229215, 15⟩⟩,
  ⟨⟨-458421, 16⟩, ⟨-5533, 10⟩⟩,
  ⟨⟨-177053, 15⟩, ⟨-17381, 12⟩⟩,
  ⟨⟨-278091, 16⟩, ⟨-442667, 17⟩⟩,
  ⟨⟨-110665, 15⟩, ⟨-89021, 15⟩⟩,
  ⟨⟨-356079, 17⟩, ⟨-288847, 17⟩⟩,
  ⟨⟨-144421, 16⟩, ⟨-235809, 17⟩⟩,
  ⟨⟨-471611, 18⟩, ⟨-193401, 17⟩⟩,
  ⟨⟨-96699, 16⟩, ⟨-159099, 17⟩⟩,
  ⟨⟨-318193, 18⟩, ⟨-131073, 17⟩⟩,
  ⟨⟨-524283, 19⟩, ⟨-215969, 18⟩⟩,
  ⟨⟨-431931, 19⟩, ⟨-177663, 18⟩⟩,
  ⟨⟨-355321, 19⟩, ⟨-291425, 19⟩⟩,
  ⟨⟨-72855, 17⟩, ⟨-475825, 20⟩⟩,
  ⟨⟨-237909, 19⟩, ⟨-385981, 20⟩⟩,
  ⟨⟨-385975, 20⟩, ⟨-77621, 18⟩⟩,
  ⟨⟨-310479, 20⟩, ⟨-123555, 19⟩⟩,
  ⟨⟨-123553, 19⟩, ⟨-97033, 19⟩⟩,
  ⟨⟨-388125, 21⟩, ⟨-299813, 21⟩⟩,
  ⟨⟨-299807, 21⟩, ⟨-226889, 21⟩⟩,
  ⟨⟨-453769, 22⟩, ⟨-167387, 21⟩⟩,
  ⟨⟨-334767, 22⟩, ⟨-478523, 23⟩⟩,
  ⟨⟨-29907, 19⟩, ⟨-328573, 23⟩⟩,
  ⟨⟨-82141, 21⟩, ⟨-214381, 23⟩⟩,
  ⟨⟨-214375, 23⟩, ⟨-130911, 23⟩⟩,
  ⟨⟨-523627, 25⟩, ⟨-73223, 23⟩⟩,
  ⟨⟨-292881, 25⟩, ⟨-72703, 24⟩⟩,
  ⟨⟨-290799, 26⟩, ⟨-61055, 25⟩⟩,
  ⟨⟨-15263, 23⟩, ⟨-80235, 27⟩⟩,
  ⟨⟨-320921, 29⟩, ⟨-288495, 31⟩⟩,
  ⟨⟨-288475, 31⟩, ⟨-34407, 31⟩⟩,
  ⟨⟨-275235, 34⟩, ⟨-323825, 39⟩⟩,
  ⟨⟨-323797, 39⟩, ⟨-442699, 48⟩⟩,
  ⟨⟨-442657, 48⟩, ⟨-262165, 68⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private theorem upper : upperOK (descentCoeffs 50) first gaps = true := by
  decide +kernel

private theorem lower : ∀ i : Fin (lastRepresentative 51 - 2),
    lowerOK (rows.getD i.val []) gaps = true := by
  decide +kernel

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 51) :
    StrictNegativeInterlacing (originalQuotient 51 k) (eulerian 50) 48 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N051
