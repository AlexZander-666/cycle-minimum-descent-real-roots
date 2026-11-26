import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentPackedData.C127L048.N045

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N045

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L048.N045 LongCycleBounds.DescentNecklace.Packed.C127L048.N045.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L048.N045 LongCycleBounds.DescentNecklace.Packed.C127L048.N045.rows

private theorem actual : RepresentativeChecks 45 previousNodes rows :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L048.N045 LongCycleBounds.DescentNecklace.Packed.C127L048.N045.dataChecks

private def first : LongCycleFinite.Dyadic := ⟨-17592186044416, 0⟩

private def gaps : List Window := [
  ⟨⟨-17591615619072, 0⟩, ⟨-55999744, 0⟩⟩,
  ⟨⟨-55475328, 0⟩, ⟨-297913, 0⟩⟩,
  ⟨⟨-295660, 0⟩, ⟨-253239, 4⟩⟩,
  ⟨⟨-506069, 5⟩, ⟨-4765, 1⟩⟩,
  ⟨⟨-76219, 5⟩, ⟨-321143, 9⟩⟩,
  ⟨⟨-321097, 9⟩, ⟨-236321, 10⟩⟩,
  ⟨⟨-472599, 11⟩, ⟨-53957, 9⟩⟩,
  ⟨⟨-107907, 10⟩, ⟨-228401, 12⟩⟩,
  ⟨⟨-456779, 13⟩, ⟨-268349, 13⟩⟩,
  ⟨⟨-134169, 12⟩, ⟨-340399, 14⟩⟩,
  ⟨⟨-340387, 14⟩, ⟨-457411, 15⟩⟩,
  ⟨⟨-457397, 15⟩, ⟨-321169, 15⟩⟩,
  ⟨⟨-40145, 12⟩, ⟨-29169, 12⟩⟩,
  ⟨⟨-466693, 16⟩, ⟨-348285, 16⟩⟩,
  ⟨⟨-174139, 15⟩, ⟨-66357, 14⟩⟩,
  ⟨⟨-132711, 15⟩, ⟨-205625, 16⟩⟩,
  ⟨⟨-205621, 16⟩, ⟨-10083, 12⟩⟩,
  ⟨⟨-161325, 16⟩, ⟨-127789, 16⟩⟩,
  ⟨⟨-127787, 16⟩, ⟨-407657, 18⟩⟩,
  ⟨⟨-203825, 17⟩, ⟨-326551, 18⟩⟩,
  ⟨⟨-326545, 18⟩, ⟨-262145, 18⟩⟩,
  ⟨⟨-524281, 19⟩, ⟨-420887, 19⟩⟩,
  ⟨⟨-26305, 15⟩, ⟨-168575, 18⟩⟩,
  ⟨⟨-42143, 16⟩, ⟨-134443, 18⟩⟩,
  ⟨⟨-268881, 19⟩, ⟨-26623, 16⟩⟩,
  ⟨⟨-53245, 17⟩, ⟨-167101, 19⟩⟩,
  ⟨⟨-83549, 18⟩, ⟨-517813, 21⟩⟩,
  ⟨⟨-129451, 19⟩, ⟨-394621, 21⟩⟩,
  ⟨⟨-394613, 21⟩, ⟨-294495, 21⟩⟩,
  ⟨⟨-36811, 18⟩, ⟨-213971, 21⟩⟩,
  ⟨⟨-106983, 20⟩, ⟨-75121, 20⟩⟩,
  ⟨⟨-300477, 22⟩, ⟨-201885, 22⟩⟩,
  ⟨⟨-403759, 23⟩, ⟨-512193, 24⟩⟩,
  ⟨⟨-512177, 24⟩, ⟨-37611, 21⟩⟩,
  ⟨⟨-300877, 24⟩, ⟨-318411, 25⟩⟩,
  ⟨⟨-159199, 24⟩, ⟨-72705, 24⟩⟩,
  ⟨⟨-145403, 25⟩, ⟨-428017, 28⟩⟩,
  ⟨⟨-213997, 27⟩, ⟨-14087, 25⟩⟩,
  ⟨⟨-450755, 30⟩, ⟨-67891, 30⟩⟩,
  ⟨⟨-271543, 32⟩, ⟨-115863, 35⟩⟩,
  ⟨⟨-231707, 36⟩, ⟨-158029, 43⟩⟩,
  ⟨⟨-79007, 42⟩, ⟨-262165, 62⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private theorem upper : upperOK (descentCoeffs 44) first gaps = true := by
  decide +kernel

private theorem lower : ∀ i : Fin (lastRepresentative 45 - 2),
    lowerOK (rows.getD i.val []) gaps = true := by
  decide +kernel

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 45) :
    StrictNegativeInterlacing (originalQuotient 45 k) (eulerian 44) 42 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N045
