import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentFiniteData.N008

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N008

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentFiniteData.N008 LongCycleBounds.DescentNecklace.N008.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentFiniteData.N008 LongCycleBounds.DescentNecklace.N008.rows

private theorem actual : RepresentativeChecks 8 previousNodes rows :=
  descentFrozenConst LongCycleBounds.DescentFiniteData.N008 LongCycleBounds.DescentNecklace.N008.checks

private def first : LongCycleFinite.Dyadic := ⟨-2064729796239765559793827, 74⟩

private def gaps : List Window := [
  ⟨⟨-1032320636169144563202301, 73⟩, ⟨-77069507390380058852955, 73⟩⟩,
  ⟨⟨-154085201295074090606357, 74⟩, ⟨-1102788554924236493941, 69⟩⟩,
  ⟨⟨-17642575050917395395073, 73⟩, ⟨-2527899834376154349053, 72⟩⟩,
  ⟨⟨-631918766382595444439, 70⟩, ⟨-1157582692133955968447, 73⟩⟩,
  ⟨⟨-2314934059821011569613, 74⟩, ⟨-86415338904853689885, 73⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private theorem upper : upperOK (descentCoeffs 7) first gaps = true := by
  decide +kernel

private theorem lower : ∀ i : Fin (lastRepresentative 8 - 2),
    lowerOK (rows.getD i.val []) gaps = true := by
  decide +kernel

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 8) :
    StrictNegativeInterlacing (originalQuotient 8 k) (eulerian 7) 5 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N008
