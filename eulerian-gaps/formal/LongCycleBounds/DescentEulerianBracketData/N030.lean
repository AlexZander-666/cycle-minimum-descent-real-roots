import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentSweepChunkData.N030

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N030

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentSweepChunkData.N030 LongCycleBounds.DescentNecklace.SweepChunks.N030.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentSweepChunkData.N030 LongCycleBounds.DescentNecklace.SweepChunks.N030.rows

private theorem actual : RepresentativeChecks 30 previousNodes rows :=
  representativeChecks_of_sweepChunks (by decide) previousNodes rows
    (descentFrozenConst LongCycleBounds.DescentSweepChunkData.N030 LongCycleBounds.DescentNecklace.SweepChunks.N030.atAlphabet) (descentFrozenConst LongCycleBounds.DescentSweepChunkData.N030 LongCycleBounds.DescentNecklace.SweepChunks.N030.swept)
    (descentFrozenConst LongCycleBounds.DescentSweepChunkData.N030 LongCycleBounds.DescentNecklace.SweepChunks.N030.counts) (descentFrozenConst LongCycleBounds.DescentSweepChunkData.N030 LongCycleBounds.DescentNecklace.SweepChunks.N030.signs)

private def first : LongCycleFinite.Dyadic := ⟨-536756224, 0⟩

private def gaps : List Window := [
  ⟨⟨-536738816, 0⟩, ⟨-265707, 1⟩⟩,
  ⟨⟨-465917, 2⟩, ⟨-459217, 7⟩⟩,
  ⟨⟨-229291, 6⟩, ⟨-243815, 9⟩⟩,
  ⟨⟨-243743, 9⟩, ⟨-258413, 11⟩⟩,
  ⟨⟨-516757, 12⟩, ⟨-198271, 12⟩⟩,
  ⟨⟨-198255, 12⟩, ⟨-94789, 12⟩⟩,
  ⟨⟨-379135, 14⟩, ⟨-208585, 14⟩⟩,
  ⟨⟨-3259, 8⟩, ⟨-504107, 16⟩⟩,
  ⟨⟨-504089, 16⟩, ⟨-40605, 13⟩⟩,
  ⟨⟨-324829, 16⟩, ⟨-109443, 15⟩⟩,
  ⟨⟨-855, 8⟩, ⟨-304157, 17⟩⟩,
  ⟨⟨-304149, 17⟩, ⟨-53895, 15⟩⟩,
  ⟨⟨-215575, 17⟩, ⟨-309067, 18⟩⟩,
  ⟨⟨-309059, 18⟩, ⟨-444705, 19⟩⟩,
  ⟨⟨-444695, 19⟩, ⟨-19923, 15⟩⟩,
  ⟨⟨-39845, 16⟩, ⟨-225939, 19⟩⟩,
  ⟨⟨-451867, 20⟩, ⟨-313961, 20⟩⟩,
  ⟨⟨-9811, 15⟩, ⟨-423109, 21⟩⟩,
  ⟨⟨-211549, 20⟩, ⟨-272643, 21⟩⟩,
  ⟨⟨-272635, 21⟩, ⟨-329475, 22⟩⟩,
  ⟨⟨-41183, 19⟩, ⟨-362515, 23⟩⟩,
  ⟨⟨-362501, 23⟩, ⟨-346627, 24⟩⟩,
  ⟨⟨-346611, 24⟩, ⟨-66487, 23⟩⟩,
  ⟨⟨-66483, 23⟩, ⟨-140943, 26⟩⟩,
  ⟨⟨-140933, 26⟩, ⟨-299629, 30⟩⟩,
  ⟨⟨-74901, 28⟩, ⟨-278141, 35⟩⟩,
  ⟨⟨-139057, 34⟩, ⟨-262213, 47⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private theorem upper : upperOK (descentCoeffs 29) first gaps = true := by
  decide +kernel

private theorem lower : ∀ i : Fin (lastRepresentative 30 - 2),
    lowerOK (rows.getD i.val []) gaps = true := by
  decide +kernel

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 30) :
    StrictNegativeInterlacing (originalQuotient 30 k) (eulerian 29) 27 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N030
