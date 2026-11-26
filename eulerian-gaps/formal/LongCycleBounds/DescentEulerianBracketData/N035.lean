import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentSweepChunkData.N035

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N035

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentSweepChunkData.N035 LongCycleBounds.DescentNecklace.SweepChunks.N035.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentSweepChunkData.N035 LongCycleBounds.DescentNecklace.SweepChunks.N035.rows

private theorem actual : RepresentativeChecks 35 previousNodes rows :=
  representativeChecks_of_sweepChunks (by decide) previousNodes rows
    (descentFrozenConst LongCycleBounds.DescentSweepChunkData.N035 LongCycleBounds.DescentNecklace.SweepChunks.N035.atAlphabet) (descentFrozenConst LongCycleBounds.DescentSweepChunkData.N035 LongCycleBounds.DescentNecklace.SweepChunks.N035.swept)
    (descentFrozenConst LongCycleBounds.DescentSweepChunkData.N035 LongCycleBounds.DescentNecklace.SweepChunks.N035.counts) (descentFrozenConst LongCycleBounds.DescentSweepChunkData.N035 LongCycleBounds.DescentNecklace.SweepChunks.N035.signs)

private def first : LongCycleFinite.Dyadic := ⟨-17179344896, 0⟩

private def gaps : List Window := [
  ⟨⟨-17178787840, 0⟩, ⟨-1123880, 0⟩⟩,
  ⟨⟨-599666, 0⟩, ⟨-506343, 5⟩⟩,
  ⟨⟨-505193, 5⟩, ⟨-49809, 5⟩⟩,
  ⟨⟨-199153, 7⟩, ⟨-175697, 9⟩⟩,
  ⟨⟨-351333, 10⟩, ⟨-238941, 11⟩⟩,
  ⟨⟨-119459, 10⟩, ⟨-420999, 13⟩⟩,
  ⟨⟨-420971, 13⟩, ⟨-218989, 13⟩⟩,
  ⟨⟨-437957, 14⟩, ⟨-254949, 14⟩⟩,
  ⟨⟨-254939, 14⟩, ⟨-80293, 13⟩⟩,
  ⟨⟨-321161, 15⟩, ⟨-428219, 16⟩⟩,
  ⟨⟨-214103, 15⟩, ⟨-4649, 10⟩⟩,
  ⟨⟨-37191, 13⟩, ⟨-106541, 15⟩⟩,
  ⟨⟨-213077, 16⟩, ⟨-311929, 17⟩⟩,
  ⟨⟨-155961, 16⟩, ⟨-231801, 17⟩⟩,
  ⟨⟨-463593, 18⟩, ⟨-10869, 13⟩⟩,
  ⟨⟨-43475, 15⟩, ⟨-65537, 16⟩⟩,
  ⟨⟨-524285, 19⟩, ⟨-395165, 19⟩⟩,
  ⟨⟨-395157, 19⟩, ⟨-296467, 19⟩⟩,
  ⟨⟨-296461, 19⟩, ⟨-55077, 17⟩⟩,
  ⟨⟨-220303, 19⟩, ⟨-322513, 20⟩⟩,
  ⟨⟨-161253, 19⟩, ⟨-461943, 21⟩⟩,
  ⟨⟨-115483, 19⟩, ⟨-320963, 21⟩⟩,
  ⟨⟨-160477, 20⟩, ⟨-53493, 19⟩⟩,
  ⟨⟨-106983, 20⟩, ⟨-269557, 22⟩⟩,
  ⟨⟨-67387, 20⟩, ⟨-39227, 20⟩⟩,
  ⟨⟨-313805, 23⟩, ⟨-326483, 24⟩⟩,
  ⟨⟨-326469, 24⟩, ⟨-287617, 25⟩⟩,
  ⟨⟨-143801, 24⟩, ⟨-391187, 27⟩⟩,
  ⟨⟨-97791, 25⟩, ⟨-172481, 28⟩⟩,
  ⟨⟨-344937, 29⟩, ⟨-271567, 32⟩⟩,
  ⟨⟨-33943, 29⟩, ⟨-72129, 36⟩⟩,
  ⟨⟨-288489, 38⟩, ⟨-262165, 52⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private theorem upper : upperOK (descentCoeffs 34) first gaps = true := by
  decide +kernel

private theorem lower : ∀ i : Fin (lastRepresentative 35 - 2),
    lowerOK (rows.getD i.val []) gaps = true := by
  decide +kernel

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 35) :
    StrictNegativeInterlacing (originalQuotient 35 k) (eulerian 34) 32 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N035
