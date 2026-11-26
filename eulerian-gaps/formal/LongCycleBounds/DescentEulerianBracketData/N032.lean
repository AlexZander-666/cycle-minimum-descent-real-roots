import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentSweepChunkData.N032

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N032

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentSweepChunkData.N032 LongCycleBounds.DescentNecklace.SweepChunks.N032.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentSweepChunkData.N032 LongCycleBounds.DescentNecklace.SweepChunks.N032.rows

private theorem actual : RepresentativeChecks 32 previousNodes rows :=
  representativeChecks_of_sweepChunks (by decide) previousNodes rows
    (descentFrozenConst LongCycleBounds.DescentSweepChunkData.N032 LongCycleBounds.DescentNecklace.SweepChunks.N032.atAlphabet) (descentFrozenConst LongCycleBounds.DescentSweepChunkData.N032 LongCycleBounds.DescentNecklace.SweepChunks.N032.swept)
    (descentFrozenConst LongCycleBounds.DescentSweepChunkData.N032 LongCycleBounds.DescentNecklace.SweepChunks.N032.counts) (descentFrozenConst LongCycleBounds.DescentSweepChunkData.N032 LongCycleBounds.DescentNecklace.SweepChunks.N032.signs)

private def first : LongCycleFinite.Dyadic := ⟨-2147221504, 0⟩

private def gaps : List Window := [
  ⟨⟨-2147151872, 0⟩, ⟨-304825, 0⟩⟩,
  ⟨⟨-478619, 1⟩, ⟨-416729, 6⟩⟩,
  ⟨⟨-104017, 4⟩, ⟨-392665, 9⟩⟩,
  ⟨⟨-98133, 7⟩, ⟨-386991, 11⟩⟩,
  ⟨⟨-193467, 10⟩, ⟨-283147, 12⟩⟩,
  ⟨⟨-283121, 12⟩, ⟨-262281, 13⟩⟩,
  ⟨⟨-32783, 10⟩, ⟨-17657, 10⟩⟩,
  ⟨⟨-282499, 14⟩, ⟨-21049, 11⟩⟩,
  ⟨⟨-84193, 13⟩, ⟨-430781, 16⟩⟩,
  ⟨⟨-430767, 16⟩, ⟨-36199, 13⟩⟩,
  ⟨⟨-18099, 12⟩, ⟨-50421, 14⟩⟩,
  ⟨⟨-201679, 16⟩, ⟨-287921, 17⟩⟩,
  ⟨⟨-287913, 17⟩, ⟨-208881, 17⟩⟩,
  ⟨⟨-417753, 18⟩, ⟨-305895, 18⟩⟩,
  ⟨⟨-9559, 13⟩, ⟨-449309, 19⟩⟩,
  ⟨⟨-449299, 19⟩, ⟨-10281, 14⟩⟩,
  ⟨⟨-41123, 16⟩, ⟨-119339, 18⟩⟩,
  ⟨⟨-477345, 20⟩, ⟨-85185, 18⟩⟩,
  ⟨⟨-85183, 18⟩, ⟨-237301, 20⟩⟩,
  ⟨⟨-237295, 20⟩, ⟨-319053, 21⟩⟩,
  ⟨⟨-79761, 19⟩, ⟨-408107, 22⟩⟩,
  ⟨⟨-408095, 22⟩, ⟨-486519, 23⟩⟩,
  ⟨⟨-243251, 22⟩, ⟨-524049, 24⟩⟩,
  ⟨⟨-131007, 22⟩, ⟨-485405, 25⟩⟩,
  ⟨⟨-242691, 24⟩, ⟨-355187, 26⟩⟩,
  ⟨⟨-177583, 25⟩, ⟨-350051, 28⟩⟩,
  ⟨⟨-175013, 27⟩, ⟨-330197, 31⟩⟩,
  ⟨⟨-330169, 31⟩, ⟨-122713, 35⟩⟩,
  ⟨⟨-245403, 36⟩, ⟨-262181, 49⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private theorem upper : upperOK (descentCoeffs 31) first gaps = true := by
  decide +kernel

private theorem lower : ∀ i : Fin (lastRepresentative 32 - 2),
    lowerOK (rows.getD i.val []) gaps = true := by
  decide +kernel

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 32) :
    StrictNegativeInterlacing (originalQuotient 32 k) (eulerian 31) 29 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N032
