import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentPackedData.C127L064.N063

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N063

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L064.N063 LongCycleBounds.DescentNecklace.Packed.C127L064.N063.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L064.N063 LongCycleBounds.DescentNecklace.Packed.C127L064.N063.rows

private theorem actual : RepresentativeChecks 63 previousNodes rows :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L064.N063 LongCycleBounds.DescentNecklace.Packed.C127L064.N063.dataChecks

private def first : LongCycleFinite.Dyadic := ⟨-4611686018427387904, 0⟩

private def gaps : List Window := [
  ⟨⟨-4611536484846010368, 0⟩, ⟨-82736316416, 0⟩⟩,
  ⟨⟨-82601836544, 0⟩, ⟨-57686016, 0⟩⟩,
  ⟨⟨-54326144, 0⟩, ⟨-950368, 0⟩⟩,
  ⟨⟨-947916, 0⟩, ⟨-282783, 2⟩⟩,
  ⟨⟨-70653, 0⟩, ⟨-368169, 5⟩⟩,
  ⟨⟨-368073, 5⟩, ⟨-191675, 6⟩⟩,
  ⟨⟨-383293, 7⟩, ⟨-270405, 8⟩⟩,
  ⟨⟨-135189, 7⟩, ⟨-469493, 10⟩⟩,
  ⟨⟨-117365, 8⟩, ⟨-472613, 11⟩⟩,
  ⟨⟨-236293, 10⟩, ⟨-265339, 11⟩⟩,
  ⟨⟨-265327, 11⟩, ⟨-323667, 12⟩⟩,
  ⟨⟨-323655, 12⟩, ⟨-420989, 13⟩⟩,
  ⟨⟨-26311, 9⟩, ⟨-72005, 11⟩⟩,
  ⟨⟨-288011, 13⟩, ⟨-410437, 14⟩⟩,
  ⟨⟨-410427, 14⟩, ⟨-302263, 14⟩⟩,
  ⟨⟨-302255, 14⟩, ⟨-228705, 14⟩⟩,
  ⟨⟨-457401, 15⟩, ⟨-353939, 15⟩⟩,
  ⟨⟨-88483, 13⟩, ⟨-279043, 15⟩⟩,
  ⟨⟨-279037, 15⟩, ⟨-446929, 16⟩⟩,
  ⟨⟨-223461, 15⟩, ⟨-90661, 14⟩⟩,
  ⟨⟨-181319, 15⟩, ⟨-148765, 15⟩⟩,
  ⟨⟨-148763, 15⟩, ⟨-246387, 16⟩⟩,
  ⟨⟨-492767, 17⟩, ⟨-411249, 17⟩⟩,
  ⟨⟨-411243, 17⟩, ⟨-172717, 16⟩⟩,
  ⟨⟨-345429, 17⟩, ⟨-72923, 15⟩⟩,
  ⟨⟨-36461, 14⟩, ⟨-494719, 18⟩⟩,
  ⟨⟨-494713, 18⟩, ⟨-105227, 16⟩⟩,
  ⟨⟨-420903, 18⟩, ⟨-179489, 17⟩⟩,
  ⟨⟨-179487, 17⟩, ⟨-153323, 17⟩⟩,
  ⟨⟨-153321, 17⟩, ⟨-262147, 18⟩⟩,
  ⟨⟨-524287, 19⟩, ⟨-224103, 18⟩⟩,
  ⟨⟨-56025, 16⟩, ⟨-191433, 18⟩⟩,
  ⟨⟨-382861, 19⟩, ⟨-163267, 18⟩⟩,
  ⟨⟨-326529, 19⟩, ⟨-34727, 16⟩⟩,
  ⟨⟨-69453, 17⟩, ⟨-471183, 20⟩⟩,
  ⟨⟨-471177, 20⟩, ⟨-99469, 18⟩⟩,
  ⟨⟨-397871, 20⟩, ⟨-334203, 20⟩⟩,
  ⟨⟨-167099, 19⟩, ⟨-278915, 20⟩⟩,
  ⟨⟨-139455, 19⟩, ⟨-28871, 17⟩⟩,
  ⟨⟨-461929, 21⟩, ⟨-378993, 21⟩⟩,
  ⟨⟨-378987, 21⟩, ⟨-153763, 20⟩⟩,
  ⟨⟨-307521, 21⟩, ⟨-492543, 22⟩⟩,
  ⟨⟨-61567, 19⟩, ⟨-388319, 22⟩⟩,
  ⟨⟨-48539, 19⟩, ⟨-300479, 22⟩⟩,
  ⟨⟨-300473, 22⟩, ⟨-454711, 23⟩⟩,
  ⟨⟨-227351, 22⟩, ⟨-334861, 23⟩⟩,
  ⟨⟨-167427, 22⟩, ⟨-238599, 23⟩⟩,
  ⟨⟨-477187, 24⟩, ⟨-326477, 24⟩⟩,
  ⟨⟨-326469, 24⟩, ⟨-424641, 25⟩⟩,
  ⟨⟨-424629, 25⟩, ⟨-258993, 25⟩⟩,
  ⟨⟨-258985, 25⟩, ⟨-72703, 24⟩⟩,
  ⟨⟨-290801, 26⟩, ⟨-146379, 26⟩⟩,
  ⟨⟨-146373, 26⟩, ⟨-63535, 26⟩⟩,
  ⟨⟨-15883, 24⟩, ⟨-89635, 28⟩⟩,
  ⟨⟨-358521, 30⟩, ⟨-46669, 29⟩⟩,
  ⟨⟨-373329, 32⟩, ⟨-486157, 35⟩⟩,
  ⟨⟨-486123, 35⟩, ⟨-289365, 38⟩⟩,
  ⟨⟨-144671, 37⟩, ⟨-80345, 42⟩⟩,
  ⟨⟨-321353, 44⟩, ⟨-217911, 54⟩⟩,
  ⟨⟨-435781, 55⟩, ⟨-262165, 80⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private theorem upper : upperOK (descentCoeffs 62) first gaps = true := by
  decide +kernel

private theorem lower : ∀ i : Fin (lastRepresentative 63 - 2),
    lowerOK (rows.getD i.val []) gaps = true := by
  decide +kernel

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 63) :
    StrictNegativeInterlacing (originalQuotient 63 k) (eulerian 62) 60 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N063
