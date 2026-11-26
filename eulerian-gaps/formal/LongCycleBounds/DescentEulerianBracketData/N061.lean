import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentPackedData.C127L064.N061

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N061

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L064.N061 LongCycleBounds.DescentNecklace.Packed.C127L064.N061.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L064.N061 LongCycleBounds.DescentNecklace.Packed.C127L064.N061.rows

private theorem actual : RepresentativeChecks 61 previousNodes rows :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L064.N061 LongCycleBounds.DescentNecklace.Packed.C127L064.N061.dataChecks

private def first : LongCycleFinite.Dyadic := ⟨-1152921504606846976, 0⟩

private def gaps : List Window := [
  ⟨⟨-1152884121211502592, 0⟩, ⟨-36750622720, 0⟩⟩,
  ⟨⟨-36716937216, 0⟩, ⟨-31516416, 0⟩⟩,
  ⟨⟨-30095936, 0⟩, ⟨-605480, 0⟩⟩,
  ⟨⟨-604104, 0⟩, ⟨-389491, 3⟩⟩,
  ⟨⟨-389275, 3⟩, ⟨-133803, 4⟩⟩,
  ⟨⟨-66885, 3⟩, ⟨-72439, 5⟩⟩,
  ⟨⟨-289715, 7⟩, ⟨-421013, 9⟩⟩,
  ⟨⟨-420973, 9⟩, ⟨-373925, 10⟩⟩,
  ⟨⟨-373899, 10⟩, ⟨-23955, 7⟩⟩,
  ⟨⟨-383259, 11⟩, ⟨-436663, 12⟩⟩,
  ⟨⟨-109161, 10⟩, ⟨-33685, 9⟩⟩,
  ⟨⟨-134735, 11⟩, ⟨-353899, 13⟩⟩,
  ⟨⟨-353887, 13⟩, ⟨-244043, 13⟩⟩,
  ⟨⟨-488073, 14⟩, ⟨-350033, 14⟩⟩,
  ⟨⟨-43753, 11⟩, ⟨-518295, 15⟩⟩,
  ⟨⟨-129571, 13⟩, ⟨-393843, 15⟩⟩,
  ⟨⟨-393835, 15⟩, ⟨-305789, 15⟩⟩,
  ⟨⟨-305783, 15⟩, ⟨-241705, 15⟩⟩,
  ⟨⟨-483401, 16⟩, ⟨-24241, 12⟩⟩,
  ⟨⟨-387849, 16⟩, ⟨-157547, 15⟩⟩,
  ⟨⟨-315089, 16⟩, ⟨-517347, 17⟩⟩,
  ⟨⟨-129335, 15⟩, ⟨-3347, 10⟩⟩,
  ⟨⟨-214205, 16⟩, ⟨-357331, 17⟩⟩,
  ⟨⟨-178663, 16⟩, ⟨-299797, 17⟩⟩,
  ⟨⟨-299793, 17⟩, ⟨-505423, 18⟩⟩,
  ⟨⟨-505417, 18⟩, ⟨-427601, 18⟩⟩,
  ⟨⟨-106899, 16⟩, ⟨-181363, 17⟩⟩,
  ⟨⟨-362721, 18⟩, ⟨-308227, 18⟩⟩,
  ⟨⟨-308223, 18⟩, ⟨-262147, 18⟩⟩,
  ⟨⟨-262143, 18⟩, ⟨-222953, 18⟩⟩,
  ⟨⟨-445901, 19⟩, ⟨-189457, 18⟩⟩,
  ⟨⟨-378909, 19⟩, ⟨-321423, 19⟩⟩,
  ⟨⟨-160709, 18⟩, ⟨-135965, 18⟩⟩,
  ⟨⟨-135963, 18⟩, ⟨-458447, 20⟩⟩,
  ⟨⟨-458441, 20⟩, ⟨-384633, 20⟩⟩,
  ⟨⟨-96157, 18⟩, ⟨-160407, 19⟩⟩,
  ⟨⟨-320809, 20⟩, ⟨-265665, 20⟩⟩,
  ⟨⟨-265661, 20⟩, ⟨-109047, 19⟩⟩,
  ⟨⟨-436181, 21⟩, ⟨-354363, 21⟩⟩,
  ⟨⟨-177179, 20⟩, ⟨-142159, 20⟩⟩,
  ⟨⟨-284313, 21⟩, ⟨-224735, 21⟩⟩,
  ⟨⟨-224731, 21⟩, ⟨-348979, 22⟩⟩,
  ⟨⟨-348973, 22⟩, ⟨-132591, 21⟩⟩,
  ⟨⟨-33147, 19⟩, ⟨-49081, 20⟩⟩,
  ⟨⟨-6135, 17⟩, ⟨-281599, 23⟩⟩,
  ⟨⟨-35199, 20⟩, ⟨-24273, 20⟩⟩,
  ⟨⟨-388359, 24⟩, ⟨-510035, 25⟩⟩,
  ⟨⟨-510021, 25⟩, ⟨-314767, 25⟩⟩,
  ⟨⟨-314757, 25⟩, ⟨-179303, 25⟩⟩,
  ⟨⟨-358593, 26⟩, ⟨-91893, 25⟩⟩,
  ⟨⟨-367557, 27⟩, ⟨-163227, 27⟩⟩,
  ⟨⟨-326439, 28⟩, ⟨-59293, 27⟩⟩,
  ⟨⟨-474319, 30⟩, ⟨-513663, 32⟩⟩,
  ⟨⟨-513631, 32⟩, ⟨-176519, 33⟩⟩,
  ⟨⟨-176507, 33⟩, ⟨-454815, 38⟩⟩,
  ⟨⟨-113695, 36⟩, ⟨-143191, 42⟩⟩,
  ⟨⟨-286357, 43⟩, ⟨-122601, 52⟩⟩,
  ⟨⟨-245179, 53⟩, ⟨-262165, 78⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private theorem upper : upperOK (descentCoeffs 60) first gaps = true := by
  decide +kernel

private theorem lower : ∀ i : Fin (lastRepresentative 61 - 2),
    lowerOK (rows.getD i.val []) gaps = true := by
  decide +kernel

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 61) :
    StrictNegativeInterlacing (originalQuotient 61 k) (eulerian 60) 58 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N061
