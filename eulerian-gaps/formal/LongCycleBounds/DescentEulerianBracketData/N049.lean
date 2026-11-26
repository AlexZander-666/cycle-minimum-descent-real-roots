import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentPackedData.C127L056.N049

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N049

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L056.N049 LongCycleBounds.DescentNecklace.Packed.C127L056.N049.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L056.N049 LongCycleBounds.DescentNecklace.Packed.C127L056.N049.rows

private theorem actual : RepresentativeChecks 49 previousNodes rows :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L056.N049 LongCycleBounds.DescentNecklace.Packed.C127L056.N049.dataChecks

private def first : LongCycleFinite.Dyadic := ⟨-281474976710656, 0⟩

private def gaps : List Window := [
  ⟨⟨-281465849905152, 0⟩, ⟨-290091008, 0⟩⟩,
  ⟨⟨-281701376, 0⟩, ⟨-950648, 0⟩⟩,
  ⟨⟨-939128, 0⟩, ⟨-158299, 2⟩⟩,
  ⟨⟨-316267, 3⟩, ⟨-163195, 5⟩⟩,
  ⟨⟨-326283, 6⟩, ⟨-154665, 7⟩⟩,
  ⟨⟨-309279, 8⟩, ⟨-422237, 10⟩⟩,
  ⟨⟨-211097, 9⟩, ⟨-182393, 10⟩⟩,
  ⟨⟨-45595, 8⟩, ⟨-370091, 12⟩⟩,
  ⟨⟨-370071, 12⟩, ⟨-420985, 13⟩⟩,
  ⟨⟨-420967, 13⟩, ⟨-520899, 14⟩⟩,
  ⟨⟨-520881, 14⟩, ⟨-343357, 14⟩⟩,
  ⟨⟨-171673, 13⟩, ⟨-59413, 12⟩⟩,
  ⟨⟨-475291, 15⟩, ⟨-170877, 14⟩⟩,
  ⟨⟨-170873, 14⟩, ⟨-506515, 16⟩⟩,
  ⟨⟨-63313, 13⟩, ⟨-96123, 14⟩⟩,
  ⟨⟨-96121, 14⟩, ⟨-297531, 16⟩⟩,
  ⟨⟨-148763, 15⟩, ⟨-233807, 16⟩⟩,
  ⟨⟨-233803, 16⟩, ⟨-371979, 17⟩⟩,
  ⟨⟨-371973, 17⟩, ⟨-298743, 17⟩⟩,
  ⟨⟨-298737, 17⟩, ⟨-483343, 18⟩⟩,
  ⟨⟨-60417, 15⟩, ⟨-393061, 18⟩⟩,
  ⟨⟨-393055, 18⟩, ⟨-80183, 16⟩⟩,
  ⟨⟨-320727, 18⟩, ⟨-262147, 18⟩⟩,
  ⟨⟨-262143, 18⟩, ⟨-214263, 18⟩⟩,
  ⟨⟨-53565, 16⟩, ⟨-87417, 17⟩⟩,
  ⟨⟨-349663, 19⟩, ⟨-142177, 18⟩⟩,
  ⟨⟨-284349, 19⟩, ⟨-230035, 19⟩⟩,
  ⟨⟨-460063, 20⟩, ⟨-184743, 19⟩⟩,
  ⟨⟨-46185, 17⟩, ⟨-293919, 20⟩⟩,
  ⟨⟨-146957, 19⟩, ⟨-230969, 20⟩⟩,
  ⟨⟨-230965, 20⟩, ⟨-357461, 21⟩⟩,
  ⟨⟨-357455, 21⟩, ⟨-67837, 19⟩⟩,
  ⟨⟨-135671, 20⟩, ⟨-201083, 21⟩⟩,
  ⟨⟨-402157, 22⟩, ⟨-289171, 22⟩⟩,
  ⟨⟨-72291, 20⟩, ⟨-400285, 23⟩⟩,
  ⟨⟨-400275, 23⟩, ⟨-131927, 22⟩⟩,
  ⟨⟨-131923, 22⟩, ⟨-326475, 24⟩⟩,
  ⟨⟨-326465, 24⟩, ⟨-371381, 25⟩⟩,
  ⟨⟨-371367, 25⟩, ⟨-94201, 24⟩⟩,
  ⟨⟨-94197, 24⟩, ⟨-325515, 27⟩⟩,
  ⟨⟨-325499, 27⟩, ⟨-55545, 26⟩⟩,
  ⟨⟨-222167, 28⟩, ⟨-26325, 27⟩⟩,
  ⟨⟨-105293, 29⟩, ⟨-434519, 34⟩⟩,
  ⟨⟨-217243, 33⟩, ⟨-72353, 36⟩⟩,
  ⟨⟨-289387, 38⟩, ⟨-31151, 43⟩⟩,
  ⟨⟨-498369, 47⟩, ⟨-262165, 66⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private theorem upper : upperOK (descentCoeffs 48) first gaps = true := by
  decide +kernel

private theorem lower : ∀ i : Fin (lastRepresentative 49 - 2),
    lowerOK (rows.getD i.val []) gaps = true := by
  decide +kernel

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 49) :
    StrictNegativeInterlacing (originalQuotient 49 k) (eulerian 48) 46 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N049
