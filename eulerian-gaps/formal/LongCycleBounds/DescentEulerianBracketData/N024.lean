import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentSweepData.N024

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N024

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentSweepData.N024 LongCycleBounds.DescentNecklace.Sweep.N024.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentSweepData.N024 LongCycleBounds.DescentNecklace.Sweep.N024.rows

private theorem actual : RepresentativeChecks 24 previousNodes rows :=
  representativeChecks_of_shared (by decide) previousNodes rows
    (descentFrozenConst LongCycleBounds.DescentSweepData.N024 LongCycleBounds.DescentNecklace.Sweep.N024.counts) (descentFrozenConst LongCycleBounds.DescentSweepData.N024 LongCycleBounds.DescentNecklace.Sweep.N024.signs)

private def first : LongCycleFinite.Dyadic := ⟨-8377584, 0⟩

private def gaps : List Window := [
  ⟨⟨-8377312, 0⟩, ⟨-335349, 5⟩⟩,
  ⟨⟨-327185, 5⟩, ⟨-299347, 9⟩⟩,
  ⟨⟨-37393, 6⟩, ⟨-451157, 12⟩⟩,
  ⟨⟨-225535, 11⟩, ⟨-294575, 13⟩⟩,
  ⟨⟨-147273, 12⟩, ⟨-128803, 13⟩⟩,
  ⟨⟨-515179, 15⟩, ⟨-267365, 15⟩⟩,
  ⟨⟨-33419, 12⟩, ⟨-308553, 16⟩⟩,
  ⟨⟨-308541, 16⟩, ⟨-380769, 17⟩⟩,
  ⟨⟨-95189, 15⟩, ⟨-489705, 18⟩⟩,
  ⟨⟨-244845, 17⟩, ⟨-161045, 17⟩⟩,
  ⟨⟨-10065, 13⟩, ⟨-426729, 19⟩⟩,
  ⟨⟨-426717, 19⟩, ⟨-70165, 17⟩⟩,
  ⟨⟨-70163, 17⟩, ⟨-705, 11⟩⟩,
  ⟨⟨-360949, 20⟩, ⟨-445453, 21⟩⟩,
  ⟨⟨-222719, 20⟩, ⟨-64259, 19⟩⟩,
  ⟨⟨-514053, 22⟩, ⟨-266779, 22⟩⟩,
  ⟨⟨-266767, 22⟩, ⟨-116651, 22⟩⟩,
  ⟨⟨-116645, 22⟩, ⟨-152333, 24⟩⟩,
  ⟨⟨-152323, 24⟩, ⟨-28711, 24⟩⟩,
  ⟨⟨-459339, 28⟩, ⟨-205593, 31⟩⟩,
  ⟨⟨-411147, 32⟩, ⟨-262501, 41⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private theorem upper : upperOK (descentCoeffs 23) first gaps = true := by
  decide +kernel

private theorem lower : ∀ i : Fin (lastRepresentative 24 - 2),
    lowerOK (rows.getD i.val []) gaps = true := by
  decide +kernel

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 24) :
    StrictNegativeInterlacing (originalQuotient 24 k) (eulerian 23) 21 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N024
