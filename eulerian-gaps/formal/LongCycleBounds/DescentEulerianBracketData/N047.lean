import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentPackedData.C127L048.N047

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N047

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L048.N047 LongCycleBounds.DescentNecklace.Packed.C127L048.N047.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L048.N047 LongCycleBounds.DescentNecklace.Packed.C127L048.N047.rows

private theorem actual : RepresentativeChecks 47 previousNodes rows :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L048.N047 LongCycleBounds.DescentNecklace.Packed.C127L048.N047.dataChecks

private def first : LongCycleFinite.Dyadic := ⟨-70368744177664, 0⟩

private def gaps : List Window := [
  ⟨⟨-70366462476288, 0⟩, ⟨-125466624, 0⟩⟩,
  ⟨⟨-123369472, 0⟩, ⟨-533600, 0⟩⟩,
  ⟨⟨-528526, 0⟩, ⟨-400709, 4⟩⟩,
  ⟨⟨-100085, 2⟩, ⟨-446495, 7⟩⟩,
  ⟨⟨-446361, 7⟩, ⟨-446157, 9⟩⟩,
  ⟨⟨-446089, 9⟩, ⟨-39527, 7⟩⟩,
  ⟨⟨-316185, 10⟩, ⟨-280931, 11⟩⟩,
  ⟨⟨-17557, 7⟩, ⟨-145575, 11⟩⟩,
  ⟨⟨-145567, 11⟩, ⟨-168331, 12⟩⟩,
  ⟨⟨-42081, 10⟩, ⟨-210939, 13⟩⟩,
  ⟨⟨-421863, 14⟩, ⟨-280821, 14⟩⟩,
  ⟨⟨-70203, 12⟩, ⟨-391649, 15⟩⟩,
  ⟨⟨-391639, 15⟩, ⟨-283171, 15⟩⟩,
  ⟨⟨-70791, 13⟩, ⟨-210657, 15⟩⟩,
  ⟨⟨-421305, 16⟩, ⟨-320581, 16⟩⟩,
  ⟨⟨-320575, 16⟩, ⟨-248331, 16⟩⟩,
  ⟨⟨-496653, 17⟩, ⟨-195095, 16⟩⟩,
  ⟨⟨-390183, 17⟩, ⟨-154963, 16⟩⟩,
  ⟨⟨-9685, 12⟩, ⟨-496437, 18⟩⟩,
  ⟨⟨-496429, 18⟩, ⟨-199989, 17⟩⟩,
  ⟨⟨-399971, 18⟩, ⟨-161751, 17⟩⟩,
  ⟨⟨-40437, 15⟩, ⟨-262145, 18⟩⟩,
  ⟨⟨-524281, 19⟩, ⟨-424853, 19⟩⟩,
  ⟨⟨-212423, 18⟩, ⟨-42953, 16⟩⟩,
  ⟨⟨-171809, 18⟩, ⟨-276853, 19⟩⟩,
  ⟨⟨-17303, 15⟩, ⟨-443465, 20⟩⟩,
  ⟨⟨-221729, 19⟩, ⟨-88061, 18⟩⟩,
  ⟨⟨-352237, 20⟩, ⟨-276731, 20⟩⟩,
  ⟨⟨-138363, 19⟩, ⟨-428731, 21⟩⟩,
  ⟨⟨-428723, 21⟩, ⟨-326225, 21⟩⟩,
  ⟨⟨-163109, 20⟩, ⟨-485371, 22⟩⟩,
  ⟨⟨-485361, 22⟩, ⟨-350937, 22⟩⟩,
  ⟨⟨-350929, 22⟩, ⟨-489425, 23⟩⟩,
  ⟨⟨-489413, 23⟩, ⟨-10181, 18⟩⟩,
  ⟨⟨-325783, 23⟩, ⟨-408261, 24⟩⟩,
  ⟨⟨-51031, 21⟩, ⟨-472079, 25⟩⟩,
  ⟨⟨-236031, 24⟩, ⟨-489239, 26⟩⟩,
  ⟨⟨-489219, 26⟩, ⟨-217331, 26⟩⟩,
  ⟨⟨-434641, 27⟩, ⟨-308099, 28⟩⟩,
  ⟨⟨-308081, 28⟩, ⟨-307893, 30⟩⟩,
  ⟨⟨-9621, 25⟩, ⟨-343293, 33⟩⟩,
  ⟨⟨-343267, 33⟩, ⟨-8089, 32⟩⟩,
  ⟨⟨-517653, 38⟩, ⟨-17539, 41⟩⟩,
  ⟨⟨-280597, 45⟩, ⟨-262165, 64⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private theorem upper : upperOK (descentCoeffs 46) first gaps = true := by
  decide +kernel

private theorem lower : ∀ i : Fin (lastRepresentative 47 - 2),
    lowerOK (rows.getD i.val []) gaps = true := by
  decide +kernel

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 47) :
    StrictNegativeInterlacing (originalQuotient 47 k) (eulerian 46) 44 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N047
