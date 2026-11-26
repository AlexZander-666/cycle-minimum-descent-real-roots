import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentSweepChunkData.N039

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N039

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentSweepChunkData.N039 LongCycleBounds.DescentNecklace.SweepChunks.N039.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentSweepChunkData.N039 LongCycleBounds.DescentNecklace.SweepChunks.N039.rows

private theorem actual : RepresentativeChecks 39 previousNodes rows :=
  representativeChecks_of_sweepChunks (by decide) previousNodes rows
    (descentFrozenConst LongCycleBounds.DescentSweepChunkData.N039 LongCycleBounds.DescentNecklace.SweepChunks.N039.atAlphabet) (descentFrozenConst LongCycleBounds.DescentSweepChunkData.N039 LongCycleBounds.DescentNecklace.SweepChunks.N039.swept)
    (descentFrozenConst LongCycleBounds.DescentSweepChunkData.N039 LongCycleBounds.DescentNecklace.SweepChunks.N039.counts) (descentFrozenConst LongCycleBounds.DescentSweepChunkData.N039 LongCycleBounds.DescentNecklace.SweepChunks.N039.signs)

private def first : LongCycleFinite.Dyadic := ⟨-274877906944, 0⟩

private def gaps : List Window := [
  ⟨⟨-274868994048, 0⟩, ⟨-4862288, 0⟩⟩,
  ⟨⟨-4854080, 0⟩, ⟨-411131, 3⟩⟩,
  ⟨⟨-204785, 2⟩, ⟨-506827, 7⟩⟩,
  ⟨⟨-506551, 7⟩, ⟨-384297, 9⟩⟩,
  ⟨⟨-384217, 9⟩, ⟨-472625, 11⟩⟩,
  ⟨⟨-472571, 11⟩, ⟨-194081, 11⟩⟩,
  ⟨⟨-388133, 12⟩, ⟨-192055, 12⟩⟩,
  ⟨⟨-384089, 13⟩, ⟨-431415, 14⟩⟩,
  ⟨⟨-107849, 12⟩, ⟨-16559, 10⟩⟩,
  ⟨⟨-132467, 13⟩, ⟨-347307, 15⟩⟩,
  ⟨⟨-10853, 10⟩, ⟨-238909, 15⟩⟩,
  ⟨⟨-477805, 16⟩, ⟨-21303, 12⟩⟩,
  ⟨⟨-42605, 13⟩, ⟨-499829, 17⟩⟩,
  ⟨⟨-249909, 16⟩, ⟨-374117, 17⟩⟩,
  ⟨⟨-187055, 16⟩, ⟨-71079, 15⟩⟩,
  ⟨⟨-142155, 16⟩, ⟨-436795, 18⟩⟩,
  ⟨⟨-218393, 17⟩, ⟨-84455, 16⟩⟩,
  ⟨⟨-168907, 17⟩, ⟨-262147, 18⟩⟩,
  ⟨⟨-131071, 17⟩, ⟨-6357, 13⟩⟩,
  ⟨⟨-50855, 16⟩, ⟨-78665, 17⟩⟩,
  ⟨⟨-157327, 18⟩, ⟨-30213, 16⟩⟩,
  ⟨⟨-483399, 20⟩, ⟨-367377, 20⟩⟩,
  ⟨⟨-183685, 19⟩, ⟨-274977, 20⟩⟩,
  ⟨⟨-274971, 20⟩, ⟨-12601, 16⟩⟩,
  ⟨⟨-50403, 18⟩, ⟨-287643, 21⟩⟩,
  ⟨⟨-71909, 19⟩, ⟨-395733, 22⟩⟩,
  ⟨⟨-395723, 22⟩, ⟨-518757, 23⟩⟩,
  ⟨⟨-259371, 22⟩, ⟨-159293, 22⟩⟩,
  ⟨⟨-19911, 19⟩, ⟨-357829, 24⟩⟩,
  ⟨⟨-357815, 24⟩, ⟨-354099, 25⟩⟩,
  ⟨⟨-354083, 25⟩, ⟨-290813, 26⟩⟩,
  ⟨⟨-290797, 26⟩, ⟨-357673, 28⟩⟩,
  ⟨⟨-357651, 28⟩, ⟨-271233, 30⟩⟩,
  ⟨⟨-271213, 30⟩, ⟨-41843, 31⟩⟩,
  ⟨⟨-83679, 32⟩, ⟨-226343, 40⟩⟩,
  ⟨⟨-113161, 39⟩, ⟨-262165, 56⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private theorem upper : upperOK (descentCoeffs 38) first gaps = true := by
  decide +kernel

private theorem lower : ∀ i : Fin (lastRepresentative 39 - 2),
    lowerOK (rows.getD i.val []) gaps = true := by
  decide +kernel

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 39) :
    StrictNegativeInterlacing (originalQuotient 39 k) (eulerian 38) 36 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N039
