import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentSweepChunkData.N031

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N031

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentSweepChunkData.N031 LongCycleBounds.DescentNecklace.SweepChunks.N031.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentSweepChunkData.N031 LongCycleBounds.DescentNecklace.SweepChunks.N031.rows

private theorem actual : RepresentativeChecks 31 previousNodes rows :=
  representativeChecks_of_sweepChunks (by decide) previousNodes rows
    (descentFrozenConst LongCycleBounds.DescentSweepChunkData.N031 LongCycleBounds.DescentNecklace.SweepChunks.N031.atAlphabet) (descentFrozenConst LongCycleBounds.DescentSweepChunkData.N031 LongCycleBounds.DescentNecklace.SweepChunks.N031.swept)
    (descentFrozenConst LongCycleBounds.DescentSweepChunkData.N031 LongCycleBounds.DescentNecklace.SweepChunks.N031.counts) (descentFrozenConst LongCycleBounds.DescentSweepChunkData.N031 LongCycleBounds.DescentNecklace.SweepChunks.N031.signs)

private def first : LongCycleFinite.Dyadic := ⟨-1073577984, 0⟩

private def gaps : List Window := [
  ⟨⟨-1073543168, 0⟩, ⟨-380345, 1⟩⟩,
  ⟨⟨-157419, 0⟩, ⟨-309383, 6⟩⟩,
  ⟨⟨-308909, 6⟩, ⟨-77413, 7⟩⟩,
  ⟨⟨-154777, 8⟩, ⟨-158223, 10⟩⟩,
  ⟨⟨-316401, 11⟩, ⟨-118573, 11⟩⟩,
  ⟨⟨-118563, 11⟩, ⟨-446421, 14⟩⟩,
  ⟨⟨-446395, 14⟩, ⟨-60765, 12⟩⟩,
  ⟨⟨-243049, 14⟩, ⟨-145903, 14⟩⟩,
  ⟨⟨-291795, 15⟩, ⟨-187391, 15⟩⟩,
  ⟨⟨-187385, 15⟩, ⟨-504685, 17⟩⟩,
  ⟨⟨-504671, 17⟩, ⟨-351233, 17⟩⟩,
  ⟨⟨-43903, 14⟩, ⟨-499955, 18⟩⟩,
  ⟨⟨-499943, 18⟩, ⟨-360817, 18⟩⟩,
  ⟨⟨-360809, 18⟩, ⟨-262145, 18⟩⟩,
  ⟨⟨-262139, 18⟩, ⟨-190459, 18⟩⟩,
  ⟨⟨-380909, 19⟩, ⟨-8591, 14⟩⟩,
  ⟨⟨-274905, 19⟩, ⟨-97829, 18⟩⟩,
  ⟨⟨-391307, 20⟩, ⟨-17021, 16⟩⟩,
  ⟨⟨-272329, 20⟩, ⟨-183363, 20⟩⟩,
  ⟨⟨-366715, 21⟩, ⟨-471015, 22⟩⟩,
  ⟨⟨-471001, 22⟩, ⟨-282745, 22⟩⟩,
  ⟨⟨-282735, 22⟩, ⟨-76969, 21⟩⟩,
  ⟨⟨-307863, 23⟩, ⟨-72451, 22⟩⟩,
  ⟨⟨-144895, 23⟩, ⟨-54295, 23⟩⟩,
  ⟨⟨-434335, 26⟩, ⟨-110997, 26⟩⟩,
  ⟨⟨-443957, 28⟩, ⟨-111161, 29⟩⟩,
  ⟨⟨-6947, 25⟩, ⟨-184699, 35⟩⟩,
  ⟨⟨-369363, 36⟩, ⟨-262197, 48⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private theorem upper : upperOK (descentCoeffs 30) first gaps = true := by
  decide +kernel

private theorem lower : ∀ i : Fin (lastRepresentative 31 - 2),
    lowerOK (rows.getD i.val []) gaps = true := by
  decide +kernel

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 31) :
    StrictNegativeInterlacing (originalQuotient 31 k) (eulerian 30) 28 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N031
