import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentPackedData.C127L048.N041

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N041

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L048.N041 LongCycleBounds.DescentNecklace.Packed.C127L048.N041.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L048.N041 LongCycleBounds.DescentNecklace.Packed.C127L048.N041.rows

private theorem actual : RepresentativeChecks 41 previousNodes rows :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L048.N041 LongCycleBounds.DescentNecklace.Packed.C127L048.N041.dataChecks

private def first : LongCycleFinite.Dyadic := ⟨-1099511627776, 0⟩

private def gaps : List Window := [
  ⟨⟨-1099475976192, 0⟩, ⟨-10961056, 0⟩⟩,
  ⟨⟨-10928256, 0⟩, ⟨-370219, 2⟩⟩,
  ⟨⟨-368455, 2⟩, ⟨-402883, 6⟩⟩,
  ⟨⟨-402633, 6⟩, ⟨-35373, 5⟩⟩,
  ⟨⟨-35365, 5⟩, ⟨-41333, 7⟩⟩,
  ⟨⟨-330623, 10⟩, ⟨-523877, 12⟩⟩,
  ⟨⟨-523835, 12⟩, ⟨-505003, 13⟩⟩,
  ⟨⟨-252487, 12⟩, ⟨-278197, 13⟩⟩,
  ⟨⟨-34773, 10⟩, ⟨-168453, 13⟩⟩,
  ⟨⟨-168447, 13⟩, ⟨-437175, 15⟩⟩,
  ⟨⟨-437161, 15⟩, ⟨-149317, 14⟩⟩,
  ⟨⟨-298625, 15⟩, ⟨-26515, 12⟩⟩,
  ⟨⟨-212115, 15⟩, ⟨-310481, 16⟩⟩,
  ⟨⟨-155237, 15⟩, ⟨-116237, 15⟩⟩,
  ⟨⟨-232469, 16⟩, ⟨-354237, 17⟩⟩,
  ⟨⟨-177115, 16⟩, ⟨-136697, 16⟩⟩,
  ⟨⟨-68347, 15⟩, ⟨-53235, 15⟩⟩,
  ⟨⟨-26617, 14⟩, ⟨-166825, 17⟩⟩,
  ⟨⟨-83411, 16⟩, ⟨-65537, 16⟩⟩,
  ⟨⟨-262143, 18⟩, ⟨-411933, 19⟩⟩,
  ⟨⟨-411925, 19⟩, ⟨-161363, 18⟩⟩,
  ⟨⟨-10085, 14⟩, ⟨-251361, 19⟩⟩,
  ⟨⟨-502713, 20⟩, ⟨-387993, 20⟩⟩,
  ⟨⟨-193993, 19⟩, ⟨-73901, 18⟩⟩,
  ⟨⟨-147799, 19⟩, ⟨-442681, 21⟩⟩,
  ⟨⟨-27667, 17⟩, ⟨-323971, 21⟩⟩,
  ⟨⟨-80991, 19⟩, ⟨-115061, 20⟩⟩,
  ⟨⟨-460233, 22⟩, ⟨-157197, 21⟩⟩,
  ⟨⟨-314385, 22⟩, ⟨-407957, 23⟩⟩,
  ⟨⟨-407945, 23⟩, ⟨-123513, 22⟩⟩,
  ⟨⟨-123509, 22⟩, ⟨-34021, 21⟩⟩,
  ⟨⟨-272157, 24⟩, ⟨-131185, 24⟩⟩,
  ⟨⟨-131179, 24⟩, ⟨-51963, 24⟩⟩,
  ⟨⟨-207841, 26⟩, ⟨-485717, 29⟩⟩,
  ⟨⟨-242843, 28⟩, ⟨-170647, 30⟩⟩,
  ⟨⟨-341269, 31⟩, ⟨-372585, 35⟩⟩,
  ⟨⟨-186277, 34⟩, ⟨-100347, 40⟩⟩,
  ⟨⟨-200675, 41⟩, ⟨-262165, 58⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private theorem upper : upperOK (descentCoeffs 40) first gaps = true := by
  decide +kernel

private theorem lower : ∀ i : Fin (lastRepresentative 41 - 2),
    lowerOK (rows.getD i.val []) gaps = true := by
  decide +kernel

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 41) :
    StrictNegativeInterlacing (originalQuotient 41 k) (eulerian 40) 38 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N041
