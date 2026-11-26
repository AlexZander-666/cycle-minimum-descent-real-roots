import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentSweepChunkData.N036

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N036

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentSweepChunkData.N036 LongCycleBounds.DescentNecklace.SweepChunks.N036.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentSweepChunkData.N036 LongCycleBounds.DescentNecklace.SweepChunks.N036.rows

private theorem actual : RepresentativeChecks 36 previousNodes rows :=
  representativeChecks_of_sweepChunks (by decide) previousNodes rows
    (descentFrozenConst LongCycleBounds.DescentSweepChunkData.N036 LongCycleBounds.DescentNecklace.SweepChunks.N036.atAlphabet) (descentFrozenConst LongCycleBounds.DescentSweepChunkData.N036 LongCycleBounds.DescentNecklace.SweepChunks.N036.swept)
    (descentFrozenConst LongCycleBounds.DescentSweepChunkData.N036 LongCycleBounds.DescentNecklace.SweepChunks.N036.counts) (descentFrozenConst LongCycleBounds.DescentSweepChunkData.N036 LongCycleBounds.DescentNecklace.SweepChunks.N036.signs)

private def first : LongCycleFinite.Dyadic := ⟨-34358689792, 0⟩

private def gaps : List Window := [
  ⟨⟨-34357575680, 0⟩, ⟨-1910252, 0⟩⟩,
  ⟨⟨-861772, 0⟩, ⟨-340455, 4⟩⟩,
  ⟨⟨-84907, 2⟩, ⟨-503699, 8⟩⟩,
  ⟨⟨-503475, 8⟩, ⟨-53483, 7⟩⟩,
  ⟨⟨-427787, 10⟩, ⟨-141899, 10⟩⟩,
  ⟨⟨-283769, 11⟩, ⟨-245741, 12⟩⟩,
  ⟨⟨-491449, 13⟩, ⟨-505113, 14⟩⟩,
  ⟨⟨-505087, 14⟩, ⟨-291507, 14⟩⟩,
  ⟨⟨-291495, 14⟩, ⟨-91269, 13⟩⟩,
  ⟨⟨-45633, 12⟩, ⟨-484945, 16⟩⟩,
  ⟨⟨-484931, 16⟩, ⟨-21019, 12⟩⟩,
  ⟨⟨-336295, 16⟩, ⟨-481571, 17⟩⟩,
  ⟨⟨-60195, 14⟩, ⟨-352937, 17⟩⟩,
  ⟨⟨-352929, 17⟩, ⟨-263021, 17⟩⟩,
  ⟨⟨-263015, 17⟩, ⟨-396429, 18⟩⟩,
  ⟨⟨-396421, 18⟩, ⟨-18793, 14⟩⟩,
  ⟨⟨-150341, 17⟩, ⟨-457093, 19⟩⟩,
  ⟨⟨-457085, 19⟩, ⟨-346699, 19⟩⟩,
  ⟨⟨-86673, 17⟩, ⟨-522553, 20⟩⟩,
  ⟨⟨-261271, 19⟩, ⟨-194709, 19⟩⟩,
  ⟨⟨-194705, 19⟩, ⟨-142703, 19⟩⟩,
  ⟨⟨-285399, 20⟩, ⟨-102171, 19⟩⟩,
  ⟨⟨-204337, 20⟩, ⟨-8857, 16⟩⟩,
  ⟨⟨-35427, 18⟩, ⟨-11765, 17⟩⟩,
  ⟨⟨-188235, 21⟩, ⟨-117873, 21⟩⟩,
  ⟨⟨-471477, 23⟩, ⟨-136053, 22⟩⟩,
  ⟨⟨-8503, 18⟩, ⟨-69915, 22⟩⟩,
  ⟨⟨-8739, 19⟩, ⟨-484343, 26⟩⟩,
  ⟨⟨-484319, 26⟩, ⟨-321269, 27⟩⟩,
  ⟨⟨-160625, 26⟩, ⟨-136447, 28⟩⟩,
  ⟨⟨-136437, 28⟩, ⟨-101093, 31⟩⟩,
  ⟨⟨-404339, 33⟩, ⟨-383883, 39⟩⟩,
  ⟨⟨-383847, 39⟩, ⟨-262181, 53⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private theorem upper : upperOK (descentCoeffs 35) first gaps = true := by
  decide +kernel

private theorem lower : ∀ i : Fin (lastRepresentative 36 - 2),
    lowerOK (rows.getD i.val []) gaps = true := by
  decide +kernel

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 36) :
    StrictNegativeInterlacing (originalQuotient 36 k) (eulerian 35) 33 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N036
