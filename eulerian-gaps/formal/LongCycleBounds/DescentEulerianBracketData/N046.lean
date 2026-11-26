import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentPackedData.C127L048.N046

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N046

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L048.N046 LongCycleBounds.DescentNecklace.Packed.C127L048.N046.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L048.N046 LongCycleBounds.DescentNecklace.Packed.C127L048.N046.rows

private theorem actual : RepresentativeChecks 46 previousNodes rows :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L048.N046 LongCycleBounds.DescentNecklace.Packed.C127L048.N046.dataChecks

private def first : LongCycleFinite.Dyadic := ⟨-35184372088832, 0⟩

private def gaps : List Window := [
  ⟨⟨-35183231238144, 0⟩, ⟨-84048640, 0⟩⟩,
  ⟨⟨-82999808, 0⟩, ⟨-398302, 0⟩⟩,
  ⟨⟨-394917, 0⟩, ⟨-39805, 1⟩⟩,
  ⟨⟨-79541, 2⟩, ⟨-92267, 5⟩⟩,
  ⟨⟨-184481, 6⟩, ⟨-94649, 7⟩⟩,
  ⟨⟨-94635, 7⟩, ⟨-136725, 9⟩⟩,
  ⟨⟨-17089, 6⟩, ⟨-492645, 12⟩⟩,
  ⟨⟨-492613, 12⟩, ⟨-515939, 13⟩⟩,
  ⟨⟨-515913, 13⟩, ⟨-300699, 13⟩⟩,
  ⟨⟨-300687, 13⟩, ⟨-94785, 12⟩⟩,
  ⟨⟨-379127, 14⟩, ⟨-253571, 14⟩⟩,
  ⟨⟨-507127, 15⟩, ⟨-88723, 13⟩⟩,
  ⟨⟨-354883, 15⟩, ⟨-257249, 15⟩⟩,
  ⟨⟨-257243, 15⟩, ⟨-191693, 15⟩⟩,
  ⟨⟨-191689, 15⟩, ⟨-291981, 16⟩⟩,
  ⟨⟨-291975, 16⟩, ⟨-452433, 17⟩⟩,
  ⟨⟨-452425, 17⟩, ⟨-88815, 15⟩⟩,
  ⟨⟨-355253, 17⟩, ⟨-17615, 13⟩⟩,
  ⟨⟨-281835, 17⟩, ⟨-450597, 18⟩⟩,
  ⟨⟨-225295, 17⟩, ⟨-181041, 17⟩⟩,
  ⟨⟨-90519, 16⟩, ⟨-291845, 18⟩⟩,
  ⟨⟨-291841, 18⟩, ⟨-470937, 19⟩⟩,
  ⟨⟨-235465, 18⟩, ⟨-94897, 17⟩⟩,
  ⟨⟨-189791, 18⟩, ⟨-2383, 12⟩⟩,
  ⟨⟨-305019, 19⟩, ⟨-121915, 18⟩⟩,
  ⟨⟨-121913, 18⟩, ⟨-96719, 18⟩⟩,
  ⟨⟨-386869, 20⟩, ⟨-303781, 20⟩⟩,
  ⟨⟨-303775, 20⟩, ⟨-470725, 21⟩⟩,
  ⟨⟨-117679, 19⟩, ⟨-179247, 20⟩⟩,
  ⟨⟨-358487, 21⟩, ⟨-267141, 21⟩⟩,
  ⟨⟨-267135, 21⟩, ⟨-387283, 22⟩⟩,
  ⟨⟨-193637, 21⟩, ⟨-271011, 22⟩⟩,
  ⟨⟨-67751, 20⟩, ⟨-362511, 23⟩⟩,
  ⟨⟨-362501, 23⟩, ⟨-457077, 24⟩⟩,
  ⟨⟨-457063, 24⟩, ⟨-266397, 24⟩⟩,
  ⟨⟨-266387, 24⟩, ⟨-278999, 25⟩⟩,
  ⟨⟨-278987, 25⟩, ⟨-502667, 27⟩⟩,
  ⟨⟨-125661, 25⟩, ⟨-181527, 27⟩⟩,
  ⟨⟨-363033, 28⟩, ⟨-93115, 28⟩⟩,
  ⟨⟨-93109, 28⟩, ⟨-431737, 33⟩⟩,
  ⟨⟨-431705, 33⟩, ⟨-86577, 35⟩⟩,
  ⟨⟨-173139, 36⟩, ⟨-421173, 45⟩⟩,
  ⟨⟨-210567, 44⟩, ⟨-262149, 63⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private theorem upper : upperOK (descentCoeffs 45) first gaps = true := by
  decide +kernel

private theorem lower : ∀ i : Fin (lastRepresentative 46 - 2),
    lowerOK (rows.getD i.val []) gaps = true := by
  decide +kernel

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 46) :
    StrictNegativeInterlacing (originalQuotient 46 k) (eulerian 45) 43 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N046
