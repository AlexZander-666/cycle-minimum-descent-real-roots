import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentSweepChunkData.N033

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N033

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentSweepChunkData.N033 LongCycleBounds.DescentNecklace.SweepChunks.N033.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentSweepChunkData.N033 LongCycleBounds.DescentNecklace.SweepChunks.N033.rows

private theorem actual : RepresentativeChecks 33 previousNodes rows :=
  representativeChecks_of_sweepChunks (by decide) previousNodes rows
    (descentFrozenConst LongCycleBounds.DescentSweepChunkData.N033 LongCycleBounds.DescentNecklace.SweepChunks.N033.atAlphabet) (descentFrozenConst LongCycleBounds.DescentSweepChunkData.N033 LongCycleBounds.DescentNecklace.SweepChunks.N033.swept)
    (descentFrozenConst LongCycleBounds.DescentSweepChunkData.N033 LongCycleBounds.DescentNecklace.SweepChunks.N033.counts) (descentFrozenConst LongCycleBounds.DescentSweepChunkData.N033 LongCycleBounds.DescentNecklace.SweepChunks.N033.signs)

private def first : LongCycleFinite.Dyadic := ⟨-4294574080, 0⟩

private def gaps : List Window := [
  ⟨⟨-4294434816, 0⟩, ⟨-534142, 0⟩⟩,
  ⟨⟨-403104, 0⟩, ⟨-35037, 2⟩⟩,
  ⟨⟨-8743, 0⟩, ⟨-248851, 8⟩⟩,
  ⟨⟨-248761, 8⟩, ⟨-472629, 11⟩⟩,
  ⟨⟨-118139, 9⟩, ⟨-168797, 11⟩⟩,
  ⟨⟨-337563, 12⟩, ⟨-307601, 13⟩⟩,
  ⟨⟨-153791, 12⟩, ⟨-327607, 14⟩⟩,
  ⟨⟨-40949, 11⟩, ⟨-48453, 12⟩⟩,
  ⟨⟨-387609, 15⟩, ⟨-246765, 15⟩⟩,
  ⟨⟨-246757, 15⟩, ⟨-331029, 16⟩⟩,
  ⟨⟨-82755, 14⟩, ⟨-461031, 17⟩⟩,
  ⟨⟨-461019, 17⟩, ⟨-329709, 17⟩⟩,
  ⟨⟨-329701, 17⟩, ⟨-240149, 17⟩⟩,
  ⟨⟨-480287, 18⟩, ⟨-353857, 18⟩⟩,
  ⟨⟨-353849, 18⟩, ⟨-262149, 18⟩⟩,
  ⟨⟨-262143, 18⟩, ⟨-97103, 17⟩⟩,
  ⟨⟨-97101, 17⟩, ⟨-71541, 17⟩⟩,
  ⟨⟨-286157, 19⟩, ⟨-416857, 20⟩⟩,
  ⟨⟨-416847, 20⟩, ⟨-298121, 20⟩⟩,
  ⟨⟨-149057, 19⟩, ⟨-415193, 21⟩⟩,
  ⟨⟨-415183, 21⟩, ⟨-139243, 20⟩⟩,
  ⟨⟨-139239, 20⟩, ⟨-354575, 22⟩⟩,
  ⟨⟨-88641, 20⟩, ⟨-26221, 19⟩⟩,
  ⟨⟨-209761, 22⟩, ⟨-446835, 24⟩⟩,
  ⟨⟨-446817, 24⟩, ⟨-407165, 25⟩⟩,
  ⟨⟨-203573, 24⟩, ⟨-290825, 26⟩⟩,
  ⟨⟨-36351, 23⟩, ⟨-17265, 24⟩⟩,
  ⟨⟨-69055, 26⟩, ⟨-490763, 32⟩⟩,
  ⟨⟨-490723, 32⟩, ⟨-326233, 37⟩⟩,
  ⟨⟨-163101, 36⟩, ⟨-262197, 50⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private theorem upper : upperOK (descentCoeffs 32) first gaps = true := by
  decide +kernel

private theorem lower : ∀ i : Fin (lastRepresentative 33 - 2),
    lowerOK (rows.getD i.val []) gaps = true := by
  decide +kernel

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 33) :
    StrictNegativeInterlacing (originalQuotient 33 k) (eulerian 32) 30 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N033
