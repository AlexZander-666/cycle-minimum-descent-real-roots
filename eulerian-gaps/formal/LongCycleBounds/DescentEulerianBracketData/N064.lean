import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentPackedData.C127L064.N064

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N064

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L064.N064 LongCycleBounds.DescentNecklace.Packed.C127L064.N064.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L064.N064 LongCycleBounds.DescentNecklace.Packed.C127L064.N064.rows

private theorem actual : RepresentativeChecks 64 previousNodes rows :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L064.N064 LongCycleBounds.DescentNecklace.Packed.C127L064.N064.dataChecks

private def first : LongCycleFinite.Dyadic := ⟨-9223372036854775808, 0⟩

private def gaps : List Window := [
  ⟨⟨-9223072969692020736, 0⟩, ⟨-124276178944, 0⟩⟩,
  ⟨⟨-124007481344, 0⟩, ⟨-76175360, 0⟩⟩,
  ⟨⟨-71132928, 0⟩, ⟨-1191092, 0⟩⟩,
  ⟨⟨-1187728, 0⟩, ⟨-340819, 2⟩⟩,
  ⟨⟨-85151, 0⟩, ⟨-431799, 5⟩⟩,
  ⟨⟨-215841, 4⟩, ⟨-440825, 7⟩⟩,
  ⟨⟨-440757, 7⟩, ⟨-306375, 8⟩⟩,
  ⟨⟨-38293, 5⟩, ⟨-131463, 8⟩⟩,
  ⟨⟨-131453, 8⟩, ⟨-16393, 6⟩⟩,
  ⟨⟨-262273, 10⟩, ⟨-18273, 7⟩⟩,
  ⟨⟨-146177, 10⟩, ⟨-354515, 12⟩⟩,
  ⟨⟨-177251, 11⟩, ⟨-458863, 13⟩⟩,
  ⟨⟨-14339, 8⟩, ⟨-312671, 13⟩⟩,
  ⟨⟨-156331, 12⟩, ⟨-222045, 13⟩⟩,
  ⟨⟨-444079, 14⟩, ⟨-326153, 14⟩⟩,
  ⟨⟨-163073, 13⟩, ⟨-123115, 13⟩⟩,
  ⟨⟨-246225, 14⟩, ⟨-11887, 10⟩⟩,
  ⟨⟨-380377, 15⟩, ⟨-149737, 14⟩⟩,
  ⟨⟨-74867, 13⟩, ⟨-479145, 16⟩⟩,
  ⟨⟨-479137, 16⟩, ⟨-194251, 15⟩⟩,
  ⟨⟨-24281, 12⟩, ⟨-79651, 14⟩⟩,
  ⟨⟨-318599, 16⟩, ⟨-131899, 15⟩⟩,
  ⟨⟨-263793, 16⟩, ⟨-220183, 16⟩⟩,
  ⟨⟨-55045, 14⟩, ⟨-92509, 15⟩⟩,
  ⟨⟨-370031, 17⟩, ⟨-156335, 16⟩⟩,
  ⟨⟨-156333, 16⟩, ⟨-265395, 17⟩⟩,
  ⟨⟨-16587, 13⟩, ⟨-452153, 18⟩⟩,
  ⟨⟨-113037, 16⟩, ⟨-386211, 18⟩⟩,
  ⟨⟨-193103, 17⟩, ⟨-330511, 18⟩⟩,
  ⟨⟨-165253, 17⟩, ⟨-141581, 17⟩⟩,
  ⟨⟨-141579, 17⟩, ⟨-485379, 19⟩⟩,
  ⟨⟨-485373, 19⟩, ⟨-415845, 19⟩⟩,
  ⟨⟨-12995, 14⟩, ⟨-177935, 18⟩⟩,
  ⟨⟨-177933, 18⟩, ⟨-303969, 19⟩⟩,
  ⟨⟨-303965, 19⟩, ⟨-517873, 20⟩⟩,
  ⟨⟨-517867, 20⟩, ⟨-219785, 19⟩⟩,
  ⟨⟨-109891, 18⟩, ⟨-92857, 18⟩⟩,
  ⟨⟨-371423, 20⟩, ⟨-78027, 18⟩⟩,
  ⟨⟨-39013, 17⟩, ⟨-521011, 21⟩⟩,
  ⟨⟨-130251, 19⟩, ⟨-431381, 21⟩⟩,
  ⟨⟨-431375, 21⟩, ⟨-176887, 20⟩⟩,
  ⟨⟨-44221, 18⟩, ⟨-286849, 21⟩⟩,
  ⟨⟨-71711, 19⟩, ⟨-229473, 21⟩⟩,
  ⟨⟨-458939, 22⟩, ⟨-180661, 21⟩⟩,
  ⟨⟨-90329, 20⟩, ⟨-139545, 21⟩⟩,
  ⟨⟨-69771, 20⟩, ⟨-210701, 22⟩⟩,
  ⟨⟨-210697, 22⟩, ⟨-19343, 19⟩⟩,
  ⟨⟨-309481, 23⟩, ⟨-439577, 24⟩⟩,
  ⟨⟨-439567, 24⟩, ⟨-149765, 23⟩⟩,
  ⟨⟨-149761, 23⟩, ⟨-387693, 25⟩⟩,
  ⟨⟨-193841, 24⟩, ⟨-470115, 26⟩⟩,
  ⟨⟨-117525, 24⟩, ⟨-524031, 27⟩⟩,
  ⟨⟨-524013, 27⟩, ⟨-261373, 27⟩⟩,
  ⟨⟨-130681, 26⟩, ⟨-448629, 29⟩⟩,
  ⟨⟨-14019, 24⟩, ⟨-155909, 29⟩⟩,
  ⟨⟨-38975, 27⟩, ⟨-159189, 31⟩⟩,
  ⟨⟨-159179, 31⟩, ⟨-403501, 35⟩⟩,
  ⟨⟨-403473, 35⟩, ⟨-461705, 39⟩⟩,
  ⟨⟨-461669, 39⟩, ⟨-240745, 44⟩⟩,
  ⟨⟨-240725, 44⟩, ⟨-290517, 55⟩⟩,
  ⟨⟨-290489, 55⟩, ⟨-262149, 81⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private theorem upper : upperOK (descentCoeffs 63) first gaps = true := by
  decide +kernel

private theorem lower : ∀ i : Fin (lastRepresentative 64 - 2),
    lowerOK (rows.getD i.val []) gaps = true := by
  decide +kernel

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 64) :
    StrictNegativeInterlacing (originalQuotient 64 k) (eulerian 63) 61 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N064
