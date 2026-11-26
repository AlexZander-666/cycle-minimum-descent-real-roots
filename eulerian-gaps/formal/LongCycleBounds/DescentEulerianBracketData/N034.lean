import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentSweepChunkData.N034

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N034

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentSweepChunkData.N034 LongCycleBounds.DescentNecklace.SweepChunks.N034.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentSweepChunkData.N034 LongCycleBounds.DescentNecklace.SweepChunks.N034.rows

private theorem actual : RepresentativeChecks 34 previousNodes rows :=
  representativeChecks_of_sweepChunks (by decide) previousNodes rows
    (descentFrozenConst LongCycleBounds.DescentSweepChunkData.N034 LongCycleBounds.DescentNecklace.SweepChunks.N034.atAlphabet) (descentFrozenConst LongCycleBounds.DescentSweepChunkData.N034 LongCycleBounds.DescentNecklace.SweepChunks.N034.swept)
    (descentFrozenConst LongCycleBounds.DescentSweepChunkData.N034 LongCycleBounds.DescentNecklace.SweepChunks.N034.counts) (descentFrozenConst LongCycleBounds.DescentSweepChunkData.N034 LongCycleBounds.DescentNecklace.SweepChunks.N034.signs)

private def first : LongCycleFinite.Dyadic := ⟨-8589410304, 0⟩

private def gaps : List Window := [
  ⟨⟨-8589131776, 0⟩, ⟨-730712, 0⟩⟩,
  ⟨⟨-468623, 0⟩, ⟨-377041, 5⟩⟩,
  ⟨⟨-376141, 5⟩, ⟨-315051, 8⟩⟩,
  ⟨⟨-314929, 8⟩, ⟨-288315, 10⟩⟩,
  ⟨⟨-72067, 8⟩, ⟨-200961, 11⟩⟩,
  ⟨⟨-100471, 10⟩, ⟨-360133, 13⟩⟩,
  ⟨⟨-180055, 12⟩, ⟨-23697, 10⟩⟩,
  ⟨⟨-189567, 13⟩, ⟨-3477, 8⟩⟩,
  ⟨⟨-445039, 15⟩, ⟨-281889, 15⟩⟩,
  ⟨⟨-35235, 12⟩, ⟨-94271, 14⟩⟩,
  ⟨⟨-377073, 16⟩, ⟨-262371, 16⟩⟩,
  ⟨⟨-65591, 14⟩, ⟨-46959, 14⟩⟩,
  ⟨⟨-375663, 17⟩, ⟨-68605, 15⟩⟩,
  ⟨⟨-137207, 16⟩, ⟨-406315, 18⟩⟩,
  ⟨⟨-406307, 18⟩, ⟨-303125, 18⟩⟩,
  ⟨⟨-151559, 17⟩, ⟨-226707, 18⟩⟩,
  ⟨⟨-453405, 19⟩, ⟨-169129, 18⟩⟩,
  ⟨⟨-338251, 19⟩, ⟨-250425, 19⟩⟩,
  ⟨⟨-500839, 20⟩, ⟨-11433, 15⟩⟩,
  ⟨⟨-365847, 20⟩, ⟨-261923, 20⟩⟩,
  ⟨⟨-261917, 20⟩, ⟨-364491, 21⟩⟩,
  ⟨⟨-182241, 20⟩, ⟨-487577, 22⟩⟩,
  ⟨⟨-121891, 20⟩, ⟨-154407, 21⟩⟩,
  ⟨⟨-308805, 22⟩, ⟨-90629, 21⟩⟩,
  ⟨⟨-362503, 23⟩, ⟨-11927, 19⟩⟩,
  ⟨⟨-23853, 20⟩, ⟨-341991, 25⟩⟩,
  ⟨⟨-170987, 24⟩, ⟨-119191, 25⟩⟩,
  ⟨⟨-7449, 21⟩, ⟨-436395, 29⟩⟩,
  ⟨⟨-109091, 27⟩, ⟨-182473, 31⟩⟩,
  ⟨⟨-364915, 32⟩, ⟨-433797, 38⟩⟩,
  ⟨⟨-108439, 36⟩, ⟨-262181, 51⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private theorem upper : upperOK (descentCoeffs 33) first gaps = true := by
  decide +kernel

private theorem lower : ∀ i : Fin (lastRepresentative 34 - 2),
    lowerOK (rows.getD i.val []) gaps = true := by
  decide +kernel

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 34) :
    StrictNegativeInterlacing (originalQuotient 34 k) (eulerian 33) 31 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N034
