import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentSweepChunkData.N038

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N038

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentSweepChunkData.N038 LongCycleBounds.DescentNecklace.SweepChunks.N038.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentSweepChunkData.N038 LongCycleBounds.DescentNecklace.SweepChunks.N038.rows

private theorem actual : RepresentativeChecks 38 previousNodes rows :=
  representativeChecks_of_sweepChunks (by decide) previousNodes rows
    (descentFrozenConst LongCycleBounds.DescentSweepChunkData.N038 LongCycleBounds.DescentNecklace.SweepChunks.N038.atAlphabet) (descentFrozenConst LongCycleBounds.DescentSweepChunkData.N038 LongCycleBounds.DescentNecklace.SweepChunks.N038.swept)
    (descentFrozenConst LongCycleBounds.DescentSweepChunkData.N038 LongCycleBounds.DescentNecklace.SweepChunks.N038.counts) (descentFrozenConst LongCycleBounds.DescentSweepChunkData.N038 LongCycleBounds.DescentNecklace.SweepChunks.N038.signs)

private def first : LongCycleFinite.Dyadic := ⟨-137438953472, 0⟩

private def gaps : List Window := [
  ⟨⟨-137434497024, 0⟩, ⟨-3234184, 0⟩⟩,
  ⟨⟨-3230080, 0⟩, ⟨-76791, 1⟩⟩,
  ⟨⟨-153063, 2⟩, ⟨-200811, 6⟩⟩,
  ⟨⟨-200709, 6⟩, ⟨-158197, 8⟩⟩,
  ⟨⟨-79083, 7⟩, ⟨-399091, 11⟩⟩,
  ⟨⟨-399047, 11⟩, ⟨-41707, 9⟩⟩,
  ⟨⟨-333631, 12⟩, ⟨-20903, 9⟩⟩,
  ⟨⟨-334429, 13⟩, ⟨-94787, 12⟩⟩,
  ⟨⟨-94783, 12⟩, ⟨-468839, 15⟩⟩,
  ⟨⟨-468823, 15⟩, ⟨-308745, 15⟩⟩,
  ⟨⟨-308735, 15⟩, ⟨-213033, 15⟩⟩,
  ⟨⟨-213027, 15⟩, ⟨-304429, 16⟩⟩,
  ⟨⟨-152211, 15⟩, ⟨-446575, 17⟩⟩,
  ⟨⟨-446565, 17⟩, ⟨-166985, 16⟩⟩,
  ⟨⟨-333963, 17⟩, ⟨-253275, 17⟩⟩,
  ⟨⟨-126635, 16⟩, ⟨-96951, 16⟩⟩,
  ⟨⟨-387797, 18⟩, ⟨-149261, 17⟩⟩,
  ⟨⟨-74629, 16⟩, ⟨-57551, 16⟩⟩,
  ⟨⟨-460399, 19⟩, ⟨-354407, 19⟩⟩,
  ⟨⟨-11075, 14⟩, ⟨-271329, 19⟩⟩,
  ⟨⟨-271323, 19⟩, ⟨-205769, 19⟩⟩,
  ⟨⟨-205765, 19⟩, ⟨-38471, 17⟩⟩,
  ⟨⟨-307761, 20⟩, ⟨-451477, 21⟩⟩,
  ⟨⟨-451467, 21⟩, ⟨-40323, 18⟩⟩,
  ⟨⟨-20161, 17⟩, ⟨-55645, 19⟩⟩,
  ⟨⟨-111287, 20⟩, ⟨-293155, 22⟩⟩,
  ⟨⟨-146573, 21⟩, ⟨-362515, 23⟩⟩,
  ⟨⟨-45313, 20⟩, ⟨-410977, 24⟩⟩,
  ⟨⟨-205481, 23⟩, ⟨-205965, 24⟩⟩,
  ⟨⟨-51489, 22⟩, ⟨-344415, 26⟩⟩,
  ⟨⟨-344397, 26⟩, ⟨-434479, 28⟩⟩,
  ⟨⟨-108613, 26⟩, ⟨-342231, 30⟩⟩,
  ⟨⟨-171103, 29⟩, ⟨-448941, 34⟩⟩,
  ⟨⟨-448903, 34⟩, ⟨-170007, 39⟩⟩,
  ⟨⟨-169991, 39⟩, ⟨-262181, 55⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private theorem upper : upperOK (descentCoeffs 37) first gaps = true := by
  decide +kernel

private theorem lower : ∀ i : Fin (lastRepresentative 38 - 2),
    lowerOK (rows.getD i.val []) gaps = true := by
  decide +kernel

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 38) :
    StrictNegativeInterlacing (originalQuotient 38 k) (eulerian 37) 35 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N038
