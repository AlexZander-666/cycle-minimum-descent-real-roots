import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentSweepChunkData.N040

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N040

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentSweepChunkData.N040 LongCycleBounds.DescentNecklace.SweepChunks.N040.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentSweepChunkData.N040 LongCycleBounds.DescentNecklace.SweepChunks.N040.rows

private theorem actual : RepresentativeChecks 40 previousNodes rows :=
  representativeChecks_of_sweepChunks (by decide) previousNodes rows
    (descentFrozenConst LongCycleBounds.DescentSweepChunkData.N040 LongCycleBounds.DescentNecklace.SweepChunks.N040.atAlphabet) (descentFrozenConst LongCycleBounds.DescentSweepChunkData.N040 LongCycleBounds.DescentNecklace.SweepChunks.N040.swept)
    (descentFrozenConst LongCycleBounds.DescentSweepChunkData.N040 LongCycleBounds.DescentNecklace.SweepChunks.N040.counts) (descentFrozenConst LongCycleBounds.DescentSweepChunkData.N040 LongCycleBounds.DescentNecklace.SweepChunks.N040.signs)

private def first : LongCycleFinite.Dyadic := ⟨-549755813888, 0⟩

private def gaps : List Window := [
  ⟨⟨-549737988096, 0⟩, ⟨-7299328, 0⟩⟩,
  ⟨⟨-7282928, 0⟩, ⟨-275589, 2⟩⟩,
  ⟨⟨-274415, 2⟩, ⟨-79885, 4⟩⟩,
  ⟨⟨-319355, 6⟩, ⟨-466563, 9⟩⟩,
  ⟨⟨-233231, 8⟩, ⟨-279633, 10⟩⟩,
  ⟨⟨-279599, 10⟩, ⟨-451149, 12⟩⟩,
  ⟨⟨-225557, 11⟩, ⟨-440665, 13⟩⟩,
  ⟨⟨-6885, 7⟩, ⟨-245119, 13⟩⟩,
  ⟨⟨-61277, 11⟩, ⟨-298987, 14⟩⟩,
  ⟨⟨-298975, 14⟩, ⟨-194991, 14⟩⟩,
  ⟨⟨-194985, 14⟩, ⟨-267361, 15⟩⟩,
  ⟨⟨-133677, 14⟩, ⟨-380687, 16⟩⟩,
  ⟨⟨-190339, 15⟩, ⟨-278917, 16⟩⟩,
  ⟨⟨-139455, 15⟩, ⟨-417695, 17⟩⟩,
  ⟨⟨-208843, 16⟩, ⟨-39739, 14⟩⟩,
  ⟨⟨-158953, 16⟩, ⟨-244853, 17⟩⟩,
  ⟨⟨-489697, 18⟩, ⟨-95053, 16⟩⟩,
  ⟨⟨-380205, 18⟩, ⟨-148293, 17⟩⟩,
  ⟨⟨-296581, 18⟩, ⟨-463409, 19⟩⟩,
  ⟨⟨-463401, 19⟩, ⟨-361483, 19⟩⟩,
  ⟨⟨-90369, 17⟩, ⟨-70165, 17⟩⟩,
  ⟨⟨-280655, 19⟩, ⟨-216161, 19⟩⟩,
  ⟨⟨-216157, 19⟩, ⟨-329047, 20⟩⟩,
  ⟨⟨-20565, 16⟩, ⟨-246385, 20⟩⟩,
  ⟨⟨-61595, 18⟩, ⟨-361033, 21⟩⟩,
  ⟨⟨-361025, 21⟩, ⟨-257031, 21⟩⟩,
  ⟨⟨-257025, 21⟩, ⟨-88109, 20⟩⟩,
  ⟨⟨-176213, 21⟩, ⟨-57463, 20⟩⟩,
  ⟨⟨-459691, 23⟩, ⟨-280365, 23⟩⟩,
  ⟨⟨-280355, 23⟩, ⟨-311911, 24⟩⟩,
  ⟨⟨-311899, 24⟩, ⟨-304671, 25⟩⟩,
  ⟨⟨-304657, 25⟩, ⟨-30721, 23⟩⟩,
  ⟨⟨-491511, 27⟩, ⟨-147323, 27⟩⟩,
  ⟨⟨-294627, 28⟩, ⟨-430159, 31⟩⟩,
  ⟨⟨-26883, 27⟩, ⟨-62417, 32⟩⟩,
  ⟨⟨-249647, 34⟩, ⟨-150701, 40⟩⟩,
  ⟨⟨-150687, 40⟩, ⟨-262149, 57⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private theorem upper : upperOK (descentCoeffs 39) first gaps = true := by
  decide +kernel

private theorem lower : ∀ i : Fin (lastRepresentative 40 - 2),
    lowerOK (rows.getD i.val []) gaps = true := by
  decide +kernel

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 40) :
    StrictNegativeInterlacing (originalQuotient 40 k) (eulerian 39) 37 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N040
