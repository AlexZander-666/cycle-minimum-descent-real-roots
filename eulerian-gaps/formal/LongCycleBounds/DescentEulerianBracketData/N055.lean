import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentPackedData.C127L056.N055

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N055

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L056.N055 LongCycleBounds.DescentNecklace.Packed.C127L056.N055.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L056.N055 LongCycleBounds.DescentNecklace.Packed.C127L056.N055.rows

private theorem actual : RepresentativeChecks 55 previousNodes rows :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L056.N055 LongCycleBounds.DescentNecklace.Packed.C127L056.N055.dataChecks

private def first : LongCycleFinite.Dyadic := ⟨-18014398509481984, 0⟩

private def gaps : List Window := [
  ⟨⟨-18013814393929728, 0⟩, ⟨-3700006912, 0⟩⟩,
  ⟨⟨-3163136000, 0⟩, ⟨-5440896, 0⟩⟩,
  ⟨⟨-5313584, 0⟩, ⟨-310245, 1⟩⟩,
  ⟨⟨-154883, 0⟩, ⟨-253069, 4⟩⟩,
  ⟨⟨-252961, 4⟩, ⟨-408929, 7⟩⟩,
  ⟨⟨-408847, 7⟩, ⟨-124391, 7⟩⟩,
  ⟨⟨-15547, 4⟩, ⟨-197275, 9⟩⟩,
  ⟨⟨-197259, 9⟩, ⟨-46861, 8⟩⟩,
  ⟨⟨-374865, 11⟩, ⟨-202615, 11⟩⟩,
  ⟨⟨-202605, 11⟩, ⟨-240841, 12⟩⟩,
  ⟨⟨-481663, 13⟩, ⟨-307587, 13⟩⟩,
  ⟨⟨-307577, 13⟩, ⟨-207637, 13⟩⟩,
  ⟨⟨-207631, 13⟩, ⟨-292847, 14⟩⟩,
  ⟨⟨-36605, 11⟩, ⟨-427665, 15⟩⟩,
  ⟨⟨-427655, 15⟩, ⟨-160583, 14⟩⟩,
  ⟨⟨-321159, 15⟩, ⟨-246765, 15⟩⟩,
  ⟨⟨-493521, 16⟩, ⟨-386353, 16⟩⟩,
  ⟨⟨-193173, 15⟩, ⟨-153559, 15⟩⟩,
  ⟨⟨-307113, 16⟩, ⟨-494425, 17⟩⟩,
  ⟨⟨-494417, 17⟩, ⟨-402089, 17⟩⟩,
  ⟨⟨-402083, 17⟩, ⟨-329707, 17⟩⟩,
  ⟨⟨-164851, 16⟩, ⟨-34017, 14⟩⟩,
  ⟨⟨-68033, 15⟩, ⟨-225749, 17⟩⟩,
  ⟨⟨-112873, 16⟩, ⟨-93979, 16⟩⟩,
  ⟨⟨-375911, 18⟩, ⟨-78433, 16⟩⟩,
  ⟨⟨-2451, 11⟩, ⟨-262145, 18⟩⟩,
  ⟨⟨-262141, 18⟩, ⟨-219041, 18⟩⟩,
  ⟨⟨-109519, 17⟩, ⟨-365615, 19⟩⟩,
  ⟨⟨-182805, 18⟩, ⟨-304409, 19⟩⟩,
  ⟨⟨-76101, 17⟩, ⟨-505045, 20⟩⟩,
  ⟨⟨-505039, 20⟩, ⟨-208427, 19⟩⟩,
  ⟨⟨-26053, 16⟩, ⟨-341817, 20⟩⟩,
  ⟨⟨-341811, 20⟩, ⟨-69495, 18⟩⟩,
  ⟨⟨-34747, 17⟩, ⟨-111881, 19⟩⟩,
  ⟨⟨-447517, 21⟩, ⟨-355741, 21⟩⟩,
  ⟨⟨-355735, 21⟩, ⟨-69621, 19⟩⟩,
  ⟨⟨-278479, 21⟩, ⟨-53493, 19⟩⟩,
  ⟨⟨-13373, 17⟩, ⟨-160691, 21⟩⟩,
  ⟨⟨-10043, 17⟩, ⟨-469335, 23⟩⟩,
  ⟨⟨-469325, 23⟩, ⟨-165483, 22⟩⟩,
  ⟨⟨-165479, 22⟩, ⟨-111709, 22⟩⟩,
  ⟨⟨-446825, 24⟩, ⟨-285347, 24⟩⟩,
  ⟨⟨-142669, 23⟩, ⟨-169585, 24⟩⟩,
  ⟨⟨-169579, 24⟩, ⟨-366631, 26⟩⟩,
  ⟨⟨-366617, 26⟩, ⟨-174185, 26⟩⟩,
  ⟨⟨-174177, 26⟩, ⟨-276243, 28⟩⟩,
  ⟨⟨-276229, 28⟩, ⟨-336159, 30⟩⟩,
  ⟨⟨-336139, 30⟩, ⟨-271549, 32⟩⟩,
  ⟨⟨-135765, 31⟩, ⟨-443069, 36⟩⟩,
  ⟨⟨-443035, 36⟩, ⟨-203099, 40⟩⟩,
  ⟨⟨-101541, 39⟩, ⟨-174707, 49⟩⟩,
  ⟨⟨-349381, 50⟩, ⟨-262165, 72⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private theorem upper : upperOK (descentCoeffs 54) first gaps = true := by
  decide +kernel

private theorem lower : ∀ i : Fin (lastRepresentative 55 - 2),
    lowerOK (rows.getD i.val []) gaps = true := by
  decide +kernel

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 55) :
    StrictNegativeInterlacing (originalQuotient 55 k) (eulerian 54) 52 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N055
