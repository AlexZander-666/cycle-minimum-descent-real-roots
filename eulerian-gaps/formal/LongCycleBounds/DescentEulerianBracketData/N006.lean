import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentFiniteData.N006

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N006

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentFiniteData.N006 LongCycleBounds.DescentNecklace.N006.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentFiniteData.N006 LongCycleBounds.DescentNecklace.N006.rows

private theorem actual : RepresentativeChecks 6 previousNodes rows :=
  descentFrozenConst LongCycleBounds.DescentFiniteData.N006 LongCycleBounds.DescentNecklace.N006.checks

private def first : LongCycleFinite.Dyadic := ⟨-51028459783979, 41⟩

private def gaps : List Window := [
  ⟨⟨-408203947861533, 44⟩, ⟨-40860746239557, 44⟩⟩,
  ⟨⟨-20425595352023, 43⟩, ⟨-3787458666651, 43⟩⟩,
  ⟨⟨-7573952012437, 44⟩, ⟨-379108567035, 43⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private theorem upper : upperOK (descentCoeffs 5) first gaps = true := by
  decide +kernel

private theorem lower : ∀ i : Fin (lastRepresentative 6 - 2),
    lowerOK (rows.getD i.val []) gaps = true := by
  decide +kernel

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 6) :
    StrictNegativeInterlacing (originalQuotient 6 k) (eulerian 5) 3 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N006
