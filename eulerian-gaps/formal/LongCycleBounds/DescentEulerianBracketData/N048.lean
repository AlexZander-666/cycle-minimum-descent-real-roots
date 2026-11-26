import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentPackedData.C127L048.N048

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N048

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L048.N048 LongCycleBounds.DescentNecklace.Packed.C127L048.N048.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L048.N048 LongCycleBounds.DescentNecklace.Packed.C127L048.N048.rows

private theorem actual : RepresentativeChecks 48 previousNodes rows :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L048.N048 LongCycleBounds.DescentNecklace.Packed.C127L048.N048.dataChecks

private def first : LongCycleFinite.Dyadic := ⟨-140737488355328, 0⟩

private def gaps : List Window := [
  ⟨⟨-140732924952576, 0⟩, ⟨-191525888, 0⟩⟩,
  ⟨⟨-187331072, 0⟩, ⟨-712538, 0⟩⟩,
  ⟨⟨-704976, 0⟩, ⟨-503807, 4⟩⟩,
  ⟨⟨-503311, 4⟩, ⟨-33751, 3⟩⟩,
  ⟨⟨-269923, 6⟩, ⟨-262717, 8⟩⟩,
  ⟨⟨-262675, 8⟩, ⟨-182747, 9⟩⟩,
  ⟨⟨-182729, 9⟩, ⟨-320223, 11⟩⟩,
  ⟨⟨-320201, 11⟩, ⟨-328367, 12⟩⟩,
  ⟨⟨-164175, 11⟩, ⟨-376609, 13⟩⟩,
  ⟨⟨-376593, 13⟩, ⟨-468985, 14⟩⟩,
  ⟨⟨-468969, 14⟩, ⟨-155337, 13⟩⟩,
  ⟨⟨-38833, 11⟩, ⟨-431693, 15⟩⟩,
  ⟨⟨-431681, 15⟩, ⟨-19455, 11⟩⟩,
  ⟨⟨-38909, 12⟩, ⟨-115571, 14⟩⟩,
  ⟨⟨-231137, 15⟩, ⟨-175681, 15⟩⟩,
  ⟨⟨-351355, 16⟩, ⟨-272067, 16⟩⟩,
  ⟨⟨-136031, 15⟩, ⟨-427593, 17⟩⟩,
  ⟨⟨-427585, 17⟩, ⟨-169967, 16⟩⟩,
  ⟨⟨-42491, 14⟩, ⟨-272671, 17⟩⟩,
  ⟨⟨-136333, 16⟩, ⟨-110089, 16⟩⟩,
  ⟨⟨-440349, 18⟩, ⟨-178605, 17⟩⟩,
  ⟨⟨-89301, 16⟩, ⟨-290541, 18⟩⟩,
  ⟨⟨-36317, 15⟩, ⟨-473051, 19⟩⟩,
  ⟨⟨-118261, 17⟩, ⟨-384761, 19⟩⟩,
  ⟨⟨-384755, 19⟩, ⟨-312115, 19⟩⟩,
  ⟨⟨-156055, 18⟩, ⟨-126013, 18⟩⟩,
  ⟨⟨-126011, 18⟩, ⟨-404321, 20⟩⟩,
  ⟨⟨-404315, 20⟩, ⟨-321431, 20⟩⟩,
  ⟨⟨-321425, 20⟩, ⟨-505177, 21⟩⟩,
  ⟨⟨-31573, 17⟩, ⟨-97791, 19⟩⟩,
  ⟨⟨-97789, 19⟩, ⟨-9291, 16⟩⟩,
  ⟨⟨-148653, 20⟩, ⟨-220767, 21⟩⟩,
  ⟨⟨-441525, 22⟩, ⟨-318381, 22⟩⟩,
  ⟨⟨-318373, 22⟩, ⟨-442399, 23⟩⟩,
  ⟨⟨-442389, 23⟩, ⟨-36633, 20⟩⟩,
  ⟨⟨-293055, 23⟩, ⟨-91237, 22⟩⟩,
  ⟨⟨-45617, 21⟩, ⟨-418581, 25⟩⟩,
  ⟨⟨-209283, 24⟩, ⟨-107309, 24⟩⟩,
  ⟨⟨-429219, 26⟩, ⟨-376061, 27⟩⟩,
  ⟨⟨-376043, 27⟩, ⟨-523163, 29⟩⟩,
  ⟨⟨-261567, 28⟩, ⟨-127297, 29⟩⟩,
  ⟨⟨-254577, 30⟩, ⟨-273065, 33⟩⟩,
  ⟨⟨-68261, 31⟩, ⟨-387011, 38⟩⟩,
  ⟨⟨-386979, 38⟩, ⟨-186977, 45⟩⟩,
  ⟨⟨-373919, 46⟩, ⟨-262149, 65⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private theorem upper : upperOK (descentCoeffs 47) first gaps = true := by
  decide +kernel

private theorem lower : ∀ i : Fin (lastRepresentative 48 - 2),
    lowerOK (rows.getD i.val []) gaps = true := by
  decide +kernel

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 48) :
    StrictNegativeInterlacing (originalQuotient 48 k) (eulerian 47) 45 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N048
