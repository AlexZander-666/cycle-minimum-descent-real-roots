import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentSweepChunkData.N037

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N037

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentSweepChunkData.N037 LongCycleBounds.DescentNecklace.SweepChunks.N037.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentSweepChunkData.N037 LongCycleBounds.DescentNecklace.SweepChunks.N037.rows

private theorem actual : RepresentativeChecks 37 previousNodes rows :=
  representativeChecks_of_sweepChunks (by decide) previousNodes rows
    (descentFrozenConst LongCycleBounds.DescentSweepChunkData.N037 LongCycleBounds.DescentNecklace.SweepChunks.N037.atAlphabet) (descentFrozenConst LongCycleBounds.DescentSweepChunkData.N037 LongCycleBounds.DescentNecklace.SweepChunks.N037.swept)
    (descentFrozenConst LongCycleBounds.DescentSweepChunkData.N037 LongCycleBounds.DescentNecklace.SweepChunks.N037.counts) (descentFrozenConst LongCycleBounds.DescentSweepChunkData.N037 LongCycleBounds.DescentNecklace.SweepChunks.N037.signs)

private def first : LongCycleFinite.Dyadic := ⟨-68717379584, 0⟩

private def gaps : List Window := [
  ⟨⟨-68715151360, 0⟩, ⟨-2153952, 0⟩⟩,
  ⟨⟨-2151896, 0⟩, ⟨-228663, 3⟩⟩,
  ⟨⟨-56999, 1⟩, ⟨-159119, 6⟩⟩,
  ⟨⟨-318087, 7⟩, ⟨-32531, 6⟩⟩,
  ⟨⟨-260199, 9⟩, ⟨-168349, 10⟩⟩,
  ⟨⟨-336663, 11⟩, ⟨-286513, 12⟩⟩,
  ⟨⟨-71623, 10⟩, ⟨-290829, 13⟩⟩,
  ⟨⟨-290813, 13⟩, ⟨-83181, 12⟩⟩,
  ⟨⟨-166355, 13⟩, ⟨-414113, 15⟩⟩,
  ⟨⟨-414099, 15⟩, ⟨-273913, 15⟩⟩,
  ⟨⟨-17119, 11⟩, ⟨-189515, 15⟩⟩,
  ⟨⟨-94755, 14⟩, ⟨-271157, 16⟩⟩,
  ⟨⟨-135575, 15⟩, ⟨-99431, 15⟩⟩,
  ⟨⟨-397715, 17⟩, ⟨-297011, 17⟩⟩,
  ⟨⟨-74251, 15⟩, ⟨-449253, 18⟩⟩,
  ⟨⟨-449245, 18⟩, ⟨-342507, 18⟩⟩,
  ⟨⟨-85625, 16⟩, ⟨-262145, 18⟩⟩,
  ⟨⟨-65535, 16⟩, ⟨-401279, 19⟩⟩,
  ⟨⟨-50159, 16⟩, ⟨-305935, 19⟩⟩,
  ⟨⟨-305929, 19⟩, ⟨-231375, 19⟩⟩,
  ⟨⟨-462741, 20⟩, ⟨-345573, 20⟩⟩,
  ⟨⟨-345565, 20⟩, ⟨-506871, 21⟩⟩,
  ⟨⟨-126715, 19⟩, ⟨-362617, 21⟩⟩,
  ⟨⟨-362609, 21⟩, ⟨-501775, 22⟩⟩,
  ⟨⟨-250881, 21⟩, ⟨-2593, 15⟩⟩,
  ⟨⟨-165947, 21⟩, ⟨-51637, 20⟩⟩,
  ⟨⟨-413083, 23⟩, ⟨-14769, 19⟩⟩,
  ⟨⟨-236295, 23⟩, ⟨-479733, 25⟩⟩,
  ⟨⟨-479713, 25⟩, ⟨-408227, 26⟩⟩,
  ⟨⟨-204103, 25⟩, ⟨-264085, 27⟩⟩,
  ⟨⟨-264069, 27⟩, ⟨-432057, 30⟩⟩,
  ⟨⟨-216013, 29⟩, ⟨-301217, 33⟩⟩,
  ⟨⟨-37649, 30⟩, ⟨-255431, 39⟩⟩,
  ⟨⟨-255407, 39⟩, ⟨-262165, 54⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private theorem upper : upperOK (descentCoeffs 36) first gaps = true := by
  decide +kernel

private theorem lower : ∀ i : Fin (lastRepresentative 37 - 2),
    lowerOK (rows.getD i.val []) gaps = true := by
  decide +kernel

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 37) :
    StrictNegativeInterlacing (originalQuotient 37 k) (eulerian 36) 34 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N037
