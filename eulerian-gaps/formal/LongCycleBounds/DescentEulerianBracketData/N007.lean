import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentFiniteData.N007

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N007

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentFiniteData.N007 LongCycleBounds.DescentNecklace.N007.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentFiniteData.N007 LongCycleBounds.DescentNecklace.N007.rows

private theorem actual : RepresentativeChecks 7 previousNodes rows :=
  descentFrozenConst LongCycleBounds.DescentFiniteData.N007 LongCycleBounds.DescentNecklace.N007.checks

private def first : LongCycleFinite.Dyadic := ⟨-29525743240715287793, 59⟩

private def gaps : List Window := [
  ⟨⟨-14762153936263867955, 58⟩, ⟨-654662518363139239, 57⟩⟩,
  ⟨⟨-1308957676881683597, 58⟩, ⟨-18015253898539157, 54⟩⟩,
  ⟨⟨-72052695210706895, 56⟩, ⟨-495796749789399, 51⟩⟩,
  ⟨⟨-31727583850634213, 57⟩, ⟨-11255686387026081, 59⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private theorem upper : upperOK (descentCoeffs 6) first gaps = true := by
  decide +kernel

private theorem lower : ∀ i : Fin (lastRepresentative 7 - 2),
    lowerOK (rows.getD i.val []) gaps = true := by
  decide +kernel

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 7) :
    StrictNegativeInterlacing (originalQuotient 7 k) (eulerian 6) 4 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N007
