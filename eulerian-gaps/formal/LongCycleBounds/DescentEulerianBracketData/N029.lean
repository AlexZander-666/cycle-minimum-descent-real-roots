import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentSweepChunkData.N029

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N029

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentSweepChunkData.N029 LongCycleBounds.DescentNecklace.SweepChunks.N029.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentSweepChunkData.N029 LongCycleBounds.DescentNecklace.SweepChunks.N029.rows

private theorem actual : RepresentativeChecks 29 previousNodes rows :=
  representativeChecks_of_sweepChunks (by decide) previousNodes rows
    (descentFrozenConst LongCycleBounds.DescentSweepChunkData.N029 LongCycleBounds.DescentNecklace.SweepChunks.N029.atAlphabet) (descentFrozenConst LongCycleBounds.DescentSweepChunkData.N029 LongCycleBounds.DescentNecklace.SweepChunks.N029.swept)
    (descentFrozenConst LongCycleBounds.DescentSweepChunkData.N029 LongCycleBounds.DescentNecklace.SweepChunks.N029.counts) (descentFrozenConst LongCycleBounds.DescentSweepChunkData.N029 LongCycleBounds.DescentNecklace.SweepChunks.N029.signs)

private def first : LongCycleFinite.Dyadic := ⟨-268353536, 0⟩

private def gaps : List Window := [
  ⟨⟨-268344832, 0⟩, ⟨-87825, 0⟩⟩,
  ⟨⟨-159279, 1⟩, ⟨-340345, 7⟩⟩,
  ⟨⟨-339929, 7⟩, ⟨-47941, 7⟩⟩,
  ⟨⟨-191711, 9⟩, ⟨-210689, 11⟩⟩,
  ⟨⟨-105331, 10⟩, ⟨-330889, 13⟩⟩,
  ⟨⟨-330863, 13⟩, ⟨-321241, 14⟩⟩,
  ⟨⟨-321223, 14⟩, ⟨-89243, 13⟩⟩,
  ⟨⟨-356957, 15⟩, ⟨-433923, 16⟩⟩,
  ⟨⟨-433907, 16⟩, ⟨-140181, 15⟩⟩,
  ⟨⟨-280353, 16⟩, ⟨-47221, 14⟩⟩,
  ⟨⟨-377757, 17⟩, ⟨-261719, 17⟩⟩,
  ⟨⟨-523425, 18⟩, ⟨-368921, 18⟩⟩,
  ⟨⟨-23057, 14⟩, ⟨-262149, 18⟩⟩,
  ⟨⟨-524285, 19⟩, ⟨-372551, 19⟩⟩,
  ⟨⟨-186271, 18⟩, ⟨-262575, 19⟩⟩,
  ⟨⟨-262569, 19⟩, ⟨-363827, 20⟩⟩,
  ⟨⟨-363817, 20⟩, ⟨-490239, 21⟩⟩,
  ⟨⟨-490225, 21⟩, ⟨-79187, 19⟩⟩,
  ⟨⟨-158369, 20⟩, ⟨-385027, 22⟩⟩,
  ⟨⟨-192507, 21⟩, ⟨-427855, 23⟩⟩,
  ⟨⟨-213919, 22⟩, ⟨-415391, 24⟩⟩,
  ⟨⟨-103843, 22⟩, ⟨-326187, 25⟩⟩,
  ⟨⟨-40771, 22⟩, ⟨-11199, 22⟩⟩,
  ⟨⟨-358343, 27⟩, ⟨-404195, 30⟩⟩,
  ⟨⟨-202081, 29⟩, ⟨-419071, 35⟩⟩,
  ⟨⟨-52379, 32⟩, ⟨-262229, 46⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private theorem upper : upperOK (descentCoeffs 28) first gaps = true := by
  decide +kernel

private theorem lower : ∀ i : Fin (lastRepresentative 29 - 2),
    lowerOK (rows.getD i.val []) gaps = true := by
  decide +kernel

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 29) :
    StrictNegativeInterlacing (originalQuotient 29 k) (eulerian 28) 26 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N029
