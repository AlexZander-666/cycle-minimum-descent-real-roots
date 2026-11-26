import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentPackedData.C127L056.N052

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N052

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L056.N052 LongCycleBounds.DescentNecklace.Packed.C127L056.N052.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L056.N052 LongCycleBounds.DescentNecklace.Packed.C127L056.N052.rows

private theorem actual : RepresentativeChecks 52 previousNodes rows :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L056.N052 LongCycleBounds.DescentNecklace.Packed.C127L056.N052.dataChecks

private def first : LongCycleFinite.Dyadic := ⟨-2251799813685248, 0⟩

private def gaps : List Window := [
  ⟨⟨-2251726799241216, 0⟩, ⟨-982140928, 0⟩⟩,
  ⟨⟨-915030016, 0⟩, ⟨-2287328, 0⟩⟩,
  ⟨⟨-2247960, 0⟩, ⟨-313575, 2⟩⟩,
  ⟨⟨-313175, 2⟩, ⟨-287721, 5⟩⟩,
  ⟨⟨-71903, 3⟩, ⟨-503703, 8⟩⟩,
  ⟨⟨-503611, 8⟩, ⟨-162335, 8⟩⟩,
  ⟨⟨-162317, 8⟩, ⟨-268785, 10⟩⟩,
  ⟨⟨-67191, 8⟩, ⟨-16499, 7⟩⟩,
  ⟨⟨-263969, 11⟩, ⟨-292827, 12⟩⟩,
  ⟨⟨-146407, 11⟩, ⟨-22203, 9⟩⟩,
  ⟨⟨-177617, 12⟩, ⟨-230567, 13⟩⟩,
  ⟨⟨-7205, 8⟩, ⟨-157667, 13⟩⟩,
  ⟨⟨-315325, 14⟩, ⟨-224643, 14⟩⟩,
  ⟨⟨-449275, 15⟩, ⟨-165329, 14⟩⟩,
  ⟨⟨-165325, 14⟩, ⟨-499595, 16⟩⟩,
  ⟨⟨-499585, 16⟩, ⟨-385473, 16⟩⟩,
  ⟨⟨-192733, 15⟩, ⟨-151277, 15⟩⟩,
  ⟨⟨-75637, 14⟩, ⟨-240785, 16⟩⟩,
  ⟨⟨-240781, 16⟩, ⟨-12111, 12⟩⟩,
  ⟨⟨-387545, 17⟩, ⟨-314675, 17⟩⟩,
  ⟨⟨-314669, 17⟩, ⟨-257273, 17⟩⟩,
  ⟨⟨-257269, 17⟩, ⟨-422861, 18⟩⟩,
  ⟨⟨-211427, 17⟩, ⟨-174379, 17⟩⟩,
  ⟨⟨-348753, 18⟩, ⟨-288251, 18⟩⟩,
  ⟨⟨-144123, 17⟩, ⟨-476809, 19⟩⟩,
  ⟨⟨-238401, 18⟩, ⟨-394083, 19⟩⟩,
  ⟨⟨-394077, 19⟩, ⟨-325027, 19⟩⟩,
  ⟨⟨-162511, 18⟩, ⟨-267113, 19⟩⟩,
  ⟨⟨-267109, 19⟩, ⟨-436773, 20⟩⟩,
  ⟨⟨-218383, 19⟩, ⟨-22165, 16⟩⟩,
  ⟨⟨-177317, 19⟩, ⟨-142703, 19⟩⟩,
  ⟨⟨-285401, 20⟩, ⟨-3549, 14⟩⟩,
  ⟨⟨-56783, 18⟩, ⟨-356551, 21⟩⟩,
  ⟨⟨-356545, 21⟩, ⟨-275103, 21⟩⟩,
  ⟨⟨-137549, 20⟩, ⟨-51957, 19⟩⟩,
  ⟨⟨-415647, 22⟩, ⟨-305915, 22⟩⟩,
  ⟨⟨-76477, 20⟩, ⟨-435869, 23⟩⟩,
  ⟨⟨-435859, 23⟩, ⟨-37257, 20⟩⟩,
  ⟨⟨-4657, 17⟩, ⟨-96725, 22⟩⟩,
  ⟨⟨-48361, 21⟩, ⟨-469371, 25⟩⟩,
  ⟨⟨-117339, 23⟩, ⟨-520637, 26⟩⟩,
  ⟨⟨-260309, 25⟩, ⟨-127837, 25⟩⟩,
  ⟨⟨-255663, 26⟩, ⟨-423353, 28⟩⟩,
  ⟨⟨-105833, 26⟩, ⟨-272897, 29⟩⟩,
  ⟨⟨-272881, 29⟩, ⟨-477721, 32⟩⟩,
  ⟨⟨-477689, 32⟩, ⟨-219175, 34⟩⟩,
  ⟨⟨-438317, 35⟩, ⟨-484533, 40⟩⟩,
  ⟨⟨-121123, 38⟩, ⟨-295047, 48⟩⟩,
  ⟨⟨-295019, 48⟩, ⟨-262149, 69⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private theorem upper : upperOK (descentCoeffs 51) first gaps = true := by
  decide +kernel

private theorem lower : ∀ i : Fin (lastRepresentative 52 - 2),
    lowerOK (rows.getD i.val []) gaps = true := by
  decide +kernel

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 52) :
    StrictNegativeInterlacing (originalQuotient 52 k) (eulerian 51) 49 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N052
