import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentPackedData.C127L056.N053

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N053

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L056.N053 LongCycleBounds.DescentNecklace.Packed.C127L056.N053.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L056.N053 LongCycleBounds.DescentNecklace.Packed.C127L056.N053.rows

private theorem actual : RepresentativeChecks 53 previousNodes rows :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L056.N053 LongCycleBounds.DescentNecklace.Packed.C127L056.N053.dataChecks

private def first : LongCycleFinite.Dyadic := ⟨-4503599627370496, 0⟩

private def gaps : List Window := [
  ⟨⟨-4503453598482432, 0⟩, ⟨-1485451264, 0⟩⟩,
  ⟨⟨-1351229440, 0⟩, ⟨-3076272, 0⟩⟩,
  ⟨⟨-3018504, 0⟩, ⟨-394085, 2⟩⟩,
  ⟨⟨-196775, 1⟩, ⟨-347539, 5⟩⟩,
  ⟨⟨-347403, 5⟩, ⟨-148051, 6⟩⟩,
  ⟨⟨-148023, 6⟩, ⟨-93611, 7⟩⟩,
  ⟨⟨-374401, 9⟩, ⟨-305611, 10⟩⟩,
  ⟨⟨-305587, 10⟩, ⟨-296871, 11⟩⟩,
  ⟨⟨-296853, 11⟩, ⟨-326489, 12⟩⟩,
  ⟨⟨-163237, 11⟩, ⟨-393421, 13⟩⟩,
  ⟨⟨-196703, 12⟩, ⟨-507973, 14⟩⟩,
  ⟨⟨-507957, 14⟩, ⟨-172953, 13⟩⟩,
  ⟨⟨-43237, 11⟩, ⟨-30701, 11⟩⟩,
  ⟨⟨-122801, 13⟩, ⟨-11269, 10⟩⟩,
  ⟨⟨-45075, 12⟩, ⟨-271915, 15⟩⟩,
  ⟨⟨-271909, 15⟩, ⟨-52383, 13⟩⟩,
  ⟨⟨-26191, 12⟩, ⟨-82169, 14⟩⟩,
  ⟨⟨-164335, 15⟩, ⟨-523029, 17⟩⟩,
  ⟨⟨-523021, 17⟩, ⟨-421027, 17⟩⟩,
  ⟨⟨-105255, 15⟩, ⟨-342099, 17⟩⟩,
  ⟨⟨-171047, 16⟩, ⟨-140017, 16⟩⟩,
  ⟨⟨-280029, 17⟩, ⟨-1801, 10⟩⟩,
  ⟨⟨-230525, 17⟩, ⟨-381113, 18⟩⟩,
  ⟨⟨-381107, 18⟩, ⟨-315873, 18⟩⟩,
  ⟨⟨-78967, 16⟩, ⟨-131073, 17⟩⟩,
  ⟨⟨-131071, 17⟩, ⟨-435115, 19⟩⟩,
  ⟨⟨-435109, 19⟩, ⟨-45079, 16⟩⟩,
  ⟨⟨-360627, 19⟩, ⟨-298101, 19⟩⟩,
  ⟨⟨-18631, 15⟩, ⟨-245401, 19⟩⟩,
  ⟨⟨-490795, 20⟩, ⟨-200877, 19⟩⟩,
  ⟨⟨-100437, 18⟩, ⟨-326443, 20⟩⟩,
  ⟨⟨-163219, 19⟩, ⟨-262781, 20⟩⟩,
  ⟨⟨-32847, 17⟩, ⟨-209083, 20⟩⟩,
  ⟨⟨-418159, 21⟩, ⟨-327969, 21⟩⟩,
  ⟨⟨-81991, 19⟩, ⟨-505461, 22⟩⟩,
  ⟨⟨-126363, 20⟩, ⟨-47643, 19⟩⟩,
  ⟨⟨-23821, 18⟩, ⟨-139899, 21⟩⟩,
  ⟨⟨-17487, 18⟩, ⟨-397349, 23⟩⟩,
  ⟨⟨-397339, 23⟩, ⟨-270567, 23⟩⟩,
  ⟨⟨-270559, 23⟩, ⟨-43669, 21⟩⟩,
  ⟨⟨-174671, 23⟩, ⟨-52621, 22⟩⟩,
  ⟨⟨-210477, 24⟩, ⟨-462975, 26⟩⟩,
  ⟨⟨-231479, 25⟩, ⟨-224877, 26⟩⟩,
  ⟨⟨-449735, 27⟩, ⟨-367063, 28⟩⟩,
  ⟨⟨-91761, 26⟩, ⟨-14507, 25⟩⟩,
  ⟨⟨-464197, 30⟩, ⟨-395621, 32⟩⟩,
  ⟨⟨-197797, 31⟩, ⟨-349093, 35⟩⟩,
  ⟨⟨-174533, 34⟩, ⟨-45319, 37⟩⟩,
  ⟨⟨-181261, 39⟩, ⟨-196641, 48⟩⟩,
  ⟨⟨-393245, 49⟩, ⟨-262165, 70⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private theorem upper : upperOK (descentCoeffs 52) first gaps = true := by
  decide +kernel

private theorem lower : ∀ i : Fin (lastRepresentative 53 - 2),
    lowerOK (rows.getD i.val []) gaps = true := by
  decide +kernel

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 53) :
    StrictNegativeInterlacing (originalQuotient 53 k) (eulerian 52) 50 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N053
