import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentSweepData.N017

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N017

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentSweepData.N017 LongCycleBounds.DescentNecklace.Sweep.N017.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentSweepData.N017 LongCycleBounds.DescentNecklace.Sweep.N017.rows

private theorem actual : RepresentativeChecks 17 previousNodes rows :=
  representativeChecks_of_shared (by decide) previousNodes rows
    (descentFrozenConst LongCycleBounds.DescentSweepData.N017 LongCycleBounds.DescentNecklace.Sweep.N017.counts) (descentFrozenConst LongCycleBounds.DescentSweepData.N017 LongCycleBounds.DescentNecklace.Sweep.N017.signs)

private def first : LongCycleFinite.Dyadic := ⟨-259501, 2⟩

private def gaps : List Window := [
  ⟨⟨-518985, 3⟩, ⟨-70463, 7⟩⟩,
  ⟨⟨-70213, 7⟩, ⟨-32813, 9⟩⟩,
  ⟨⟨-262425, 12⟩, ⟨-143611, 13⟩⟩,
  ⟨⟨-71797, 12⟩, ⟨-458431, 16⟩⟩,
  ⟨⟨-458399, 16⟩, ⟨-110669, 15⟩⟩,
  ⟨⟨-442653, 17⟩, ⟨-235809, 17⟩⟩,
  ⟨⟨-235799, 17⟩, ⟨-262145, 18⟩⟩,
  ⟨⟨-131067, 17⟩, ⟨-291429, 19⟩⟩,
  ⟨⟨-291417, 19⟩, ⟨-155243, 19⟩⟩,
  ⟨⟨-38809, 17⟩, ⟨-299815, 21⟩⟩,
  ⟨⟨-37475, 18⟩, ⟨-478541, 23⟩⟩,
  ⟨⟨-29907, 19⟩, ⟨-523663, 25⟩⟩,
  ⟨⟨-523623, 25⟩, ⟨-488389, 28⟩⟩,
  ⟨⟨-488343, 28⟩, ⟨-66209, 32⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private theorem upper : upperOK (descentCoeffs 16) first gaps = true := by
  decide +kernel

private theorem lower : ∀ i : Fin (lastRepresentative 17 - 2),
    lowerOK (rows.getD i.val []) gaps = true := by
  decide +kernel

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 17) :
    StrictNegativeInterlacing (originalQuotient 17 k) (eulerian 16) 14 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N017
