import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentSweepData.N027

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N027

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentSweepData.N027 LongCycleBounds.DescentNecklace.Sweep.N027.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentSweepData.N027 LongCycleBounds.DescentNecklace.Sweep.N027.rows

private theorem actual : RepresentativeChecks 27 previousNodes rows :=
  representativeChecks_of_shared (by decide) previousNodes rows
    (descentFrozenConst LongCycleBounds.DescentSweepData.N027 LongCycleBounds.DescentNecklace.Sweep.N027.counts) (descentFrozenConst LongCycleBounds.DescentSweepData.N027 LongCycleBounds.DescentNecklace.Sweep.N027.signs)

private def first : LongCycleFinite.Dyadic := ⟨-67072000, 0⟩

private def gaps : List Window := [
  ⟨⟨-67069824, 0⟩, ⟨-301559, 3⟩⟩,
  ⟨⟨-285197, 3⟩, ⟨-186427, 7⟩⟩,
  ⟨⟨-46563, 5⟩, ⟨-236347, 10⟩⟩,
  ⟨⟨-236291, 10⟩, ⟨-278637, 12⟩⟩,
  ⟨⟨-69651, 10⟩, ⟨-457715, 14⟩⟩,
  ⟨⟨-228841, 13⟩, ⟨-228711, 14⟩⟩,
  ⟨⟨-228699, 14⟩, ⟨-517435, 16⟩⟩,
  ⟨⟨-517413, 16⟩, ⟨-317471, 16⟩⟩,
  ⟨⟨-79365, 14⟩, ⟨-411249, 17⟩⟩,
  ⟨⟨-411237, 17⟩, ⟨-137989, 16⟩⟩,
  ⟨⟨-137985, 16⟩, ⟨-378457, 18⟩⟩,
  ⟨⟨-378447, 18⟩, ⟨-262145, 18⟩⟩,
  ⟨⟨-131069, 17⟩, ⟨-181581, 18⟩⟩,
  ⟨⟨-363153, 19⟩, ⟨-498017, 20⟩⟩,
  ⟨⟨-124501, 18⟩, ⟨-334205, 20⟩⟩,
  ⟨⟨-83549, 18⟩, ⟨-54117, 18⟩⟩,
  ⟨⟨-432923, 21⟩, ⟨-33203, 18⟩⟩,
  ⟨⟨-265615, 21⟩, ⟨-75121, 20⟩⟩,
  ⟨⟨-37559, 19⟩, ⟨-300291, 23⟩⟩,
  ⟨⟨-300277, 23⟩, ⟨-493275, 25⟩⟩,
  ⟨⟨-493249, 25⟩, ⟨-290827, 26⟩⟩,
  ⟨⟨-290807, 26⟩, ⟨-368891, 29⟩⟩,
  ⟨⟨-92215, 27⟩, ⟨-59569, 31⟩⟩,
  ⟨⟨-476507, 34⟩, ⟨-262325, 44⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private theorem upper : upperOK (descentCoeffs 26) first gaps = true := by
  decide +kernel

private theorem lower : ∀ i : Fin (lastRepresentative 27 - 2),
    lowerOK (rows.getD i.val []) gaps = true := by
  decide +kernel

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 27) :
    StrictNegativeInterlacing (originalQuotient 27 k) (eulerian 26) 24 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N027
