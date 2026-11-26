import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentSweepData.N021

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N021

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentSweepData.N021 LongCycleBounds.DescentNecklace.Sweep.N021.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentSweepData.N021 LongCycleBounds.DescentNecklace.Sweep.N021.rows

private theorem actual : RepresentativeChecks 21 previousNodes rows :=
  representativeChecks_of_shared (by decide) previousNodes rows
    (descentFrozenConst LongCycleBounds.DescentSweepData.N021 LongCycleBounds.DescentNecklace.Sweep.N021.counts) (descentFrozenConst LongCycleBounds.DescentSweepData.N021 LongCycleBounds.DescentNecklace.Sweep.N021.signs)

private def first : LongCycleFinite.Dyadic := ⟨-1045266, 0⟩

private def gaps : List Window := [
  ⟨⟨-1045232, 0⟩, ⟨-385031, 7⟩⟩,
  ⟨⟨-190483, 6⟩, ⟨-472681, 11⟩⟩,
  ⟨⟨-59057, 8⟩, ⟨-421019, 13⟩⟩,
  ⟨⟨-420953, 13⟩, ⟨-37783, 11⟩⟩,
  ⟨⟨-151119, 13⟩, ⟨-279045, 15⟩⟩,
  ⟨⟨-69757, 13⟩, ⟨-148765, 15⟩⟩,
  ⟨⟨-74379, 14⟩, ⟨-172723, 16⟩⟩,
  ⟨⟨-345433, 17⟩, ⟨-420913, 18⟩⟩,
  ⟨⟨-420899, 18⟩, ⟨-262145, 18⟩⟩,
  ⟨⟨-32767, 15⟩, ⟨-326537, 19⟩⟩,
  ⟨⟨-163263, 18⟩, ⟨-198943, 19⟩⟩,
  ⟨⟨-24867, 16⟩, ⟨-461949, 21⟩⟩,
  ⟨⟨-115483, 19⟩, ⟨-492551, 22⟩⟩,
  ⟨⟨-246265, 21⟩, ⟨-227365, 22⟩⟩,
  ⟨⟨-454707, 23⟩, ⟨-163241, 23⟩⟩,
  ⟨⟨-326461, 24⟩, ⟨-290831, 26⟩⟩,
  ⟨⟨-36351, 23⟩, ⟨-179349, 29⟩⟩,
  ⟨⟨-44833, 27⟩, ⟨-131499, 37⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private theorem upper : upperOK (descentCoeffs 20) first gaps = true := by
  decide +kernel

private theorem lower : ∀ i : Fin (lastRepresentative 21 - 2),
    lowerOK (rows.getD i.val []) gaps = true := by
  decide +kernel

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 21) :
    StrictNegativeInterlacing (originalQuotient 21 k) (eulerian 20) 18 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N021
