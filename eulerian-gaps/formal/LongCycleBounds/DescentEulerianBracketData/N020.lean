import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentSweepData.N020

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N020

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentSweepData.N020 LongCycleBounds.DescentNecklace.Sweep.N020.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentSweepData.N020 LongCycleBounds.DescentNecklace.Sweep.N020.rows

private theorem actual : RepresentativeChecks 20 previousNodes rows :=
  representativeChecks_of_shared (by decide) previousNodes rows
    (descentFrozenConst LongCycleBounds.DescentSweepData.N020 LongCycleBounds.DescentNecklace.Sweep.N020.counts) (descentFrozenConst LongCycleBounds.DescentSweepData.N020 LongCycleBounds.DescentNecklace.Sweep.N020.signs)

private def first : LongCycleFinite.Dyadic := ⟨-522068, 0⟩

private def gaps : List Window := [
  ⟨⟨-522051, 0⟩, ⟨-503911, 8⟩⟩,
  ⟨⟨-499857, 8⟩, ⟨-21567, 7⟩⟩,
  ⟨⟨-344925, 11⟩, ⟨-324255, 13⟩⟩,
  ⟨⟨-20263, 9⟩, ⟨-479457, 15⟩⟩,
  ⟨⟨-479419, 15⟩, ⟨-7021, 10⟩⟩,
  ⟨⟨-449319, 16⟩, ⟨-481581, 17⟩⟩,
  ⟨⟨-481559, 17⟩, ⟨-139329, 16⟩⟩,
  ⟨⟨-278647, 17⟩, ⟨-335685, 18⟩⟩,
  ⟨⟨-335673, 18⟩, ⟨-409453, 19⟩⟩,
  ⟨⟨-409439, 19⟩, ⟨-493225, 20⟩⟩,
  ⟨⟨-61651, 17⟩, ⟨-285411, 20⟩⟩,
  ⟨⟨-35675, 17⟩, ⟨-305873, 21⟩⟩,
  ⟨⟨-305859, 21⟩, ⟨-143337, 21⟩⟩,
  ⟨⟨-71665, 20⟩, ⟨-211947, 23⟩⟩,
  ⟨⟨-423867, 24⟩, ⟨-398413, 26⟩⟩,
  ⟨⟨-199191, 25⟩, ⟨-136485, 28⟩⟩,
  ⟨⟨-17059, 25⟩, ⟨-263271, 37⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private theorem upper : upperOK (descentCoeffs 19) first gaps = true := by
  decide +kernel

private theorem lower : ∀ i : Fin (lastRepresentative 20 - 2),
    lowerOK (rows.getD i.val []) gaps = true := by
  decide +kernel

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 20) :
    StrictNegativeInterlacing (originalQuotient 20 k) (eulerian 19) 17 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N020
