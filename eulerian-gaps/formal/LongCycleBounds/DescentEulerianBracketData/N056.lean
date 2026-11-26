import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentPackedData.C127L056.N056

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N056

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L056.N056 LongCycleBounds.DescentNecklace.Packed.C127L056.N056.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L056.N056 LongCycleBounds.DescentNecklace.Packed.C127L056.N056.rows

private theorem actual : RepresentativeChecks 56 previousNodes rows :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L056.N056 LongCycleBounds.DescentNecklace.Packed.C127L056.N056.dataChecks

private def first : LongCycleFinite.Dyadic := ⟨-36028797018963968, 0⟩

private def gaps : List Window := [
  ⟨⟨-36027628787859456, 0⟩, ⟨-5579030528, 0⟩⟩,
  ⟨⟨-4505288704, 0⟩, ⟨-7259312, 0⟩⟩,
  ⟨⟨-7050176, 0⟩, ⟨-389691, 1⟩⟩,
  ⟨⟨-389053, 1⟩, ⟨-305483, 4⟩⟩,
  ⟨⟨-152673, 3⟩, ⟨-120091, 5⟩⟩,
  ⟨⟨-60033, 4⟩, ⟨-286657, 8⟩⟩,
  ⟨⟨-143311, 7⟩, ⟨-448049, 10⟩⟩,
  ⟨⟨-448011, 10⟩, ⟨-421013, 11⟩⟩,
  ⟨⟨-420987, 11⟩, ⟨-225563, 11⟩⟩,
  ⟨⟨-14097, 7⟩, ⟨-266261, 12⟩⟩,
  ⟨⟨-133125, 11⟩, ⟨-169087, 12⟩⟩,
  ⟨⟨-169081, 12⟩, ⟨-454543, 14⟩⟩,
  ⟨⟨-227265, 13⟩, ⟨-319393, 14⟩⟩,
  ⟨⟨-39923, 11⟩, ⟨-465123, 15⟩⟩,
  ⟨⟨-58139, 12⟩, ⟨-348541, 15⟩⟩,
  ⟨⟨-174267, 14⟩, ⟨-267361, 15⟩⟩,
  ⟨⟨-66839, 13⟩, ⟨-26133, 12⟩⟩,
  ⟨⟨-418121, 16⟩, ⟨-41519, 13⟩⟩,
  ⟨⟨-166073, 15⟩, ⟨-133651, 15⟩⟩,
  ⟨⟨-133649, 15⟩, ⟨-108709, 15⟩⟩,
  ⟨⟨-434829, 17⟩, ⟨-89191, 15⟩⟩,
  ⟨⟨-356759, 17⟩, ⟨-294753, 17⟩⟩,
  ⟨⟨-73687, 15⟩, ⟨-489705, 18⟩⟩,
  ⟨⟨-489699, 18⟩, ⟨-408469, 18⟩⟩,
  ⟨⟨-408463, 18⟩, ⟨-341687, 18⟩⟩,
  ⟨⟨-170841, 17⟩, ⟨-286303, 18⟩⟩,
  ⟨⟨-286299, 18⟩, ⟨-480057, 19⟩⟩,
  ⟨⟨-480051, 19⟩, ⟨-402245, 19⟩⟩,
  ⟨⟨-402239, 19⟩, ⟨-168239, 18⟩⟩,
  ⟨⟨-336473, 19⟩, ⟨-140331, 18⟩⟩,
  ⟨⟨-140329, 18⟩, ⟨-116573, 18⟩⟩,
  ⟨⟨-233143, 19⟩, ⟨-192623, 19⟩⟩,
  ⟨⟨-48155, 17⟩, ⟨-79019, 18⟩⟩,
  ⟨⟨-316071, 20⟩, ⟨-514181, 21⟩⟩,
  ⟨⟨-514173, 21⟩, ⟨-413791, 21⟩⟩,
  ⟨⟨-413785, 21⟩, ⟨-328705, 21⟩⟩,
  ⟨⟨-82175, 19⟩, ⟨-514061, 22⟩⟩,
  ⟨⟨-128513, 20⟩, ⟨-394335, 22⟩⟩,
  ⟨⟨-394327, 22⟩, ⟨-295493, 22⟩⟩,
  ⟨⟨-295487, 22⟩, ⟨-215161, 22⟩⟩,
  ⟨⟨-53789, 20⟩, ⟨-37797, 20⟩⟩,
  ⟨⟨-9449, 18⟩, ⟨-101605, 22⟩⟩,
  ⟨⟨-406409, 24⟩, ⟨-516197, 25⟩⟩,
  ⟨⟨-258091, 24⟩, ⟨-304663, 25⟩⟩,
  ⟨⟨-304653, 25⟩, ⟨-163233, 25⟩⟩,
  ⟨⟨-326453, 26⟩, ⟨-306773, 27⟩⟩,
  ⟨⟨-306759, 27⟩, ⟨-239753, 28⟩⟩,
  ⟨⟨-239741, 28⟩, ⟨-286177, 30⟩⟩,
  ⟨⟨-17885, 26⟩, ⟨-450119, 33⟩⟩,
  ⟨⟨-56261, 30⟩, ⟨-176531, 35⟩⟩,
  ⟨⟨-176517, 35⟩, ⟨-4751, 35⟩⟩,
  ⟨⟨-152019, 40⟩, ⟨-3639, 44⟩⟩,
  ⟨⟨-465749, 51⟩, ⟨-262149, 73⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private theorem upper : upperOK (descentCoeffs 55) first gaps = true := by
  decide +kernel

private theorem lower : ∀ i : Fin (lastRepresentative 56 - 2),
    lowerOK (rows.getD i.val []) gaps = true := by
  decide +kernel

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 56) :
    StrictNegativeInterlacing (originalQuotient 56 k) (eulerian 55) 53 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N056
