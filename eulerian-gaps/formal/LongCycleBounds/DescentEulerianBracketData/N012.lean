import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentFiniteData.N012

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N012

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentFiniteData.N012 LongCycleBounds.DescentNecklace.N012.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentFiniteData.N012 LongCycleBounds.DescentNecklace.N012.rows

private theorem actual : RepresentativeChecks 12 previousNodes rows :=
  descentFrozenConst LongCycleBounds.DescentFiniteData.N012 LongCycleBounds.DescentNecklace.N012.checks

private def first : LongCycleFinite.Dyadic := ⟨-21328012504735109106174034587269667778713391, 133⟩

private def gaps : List Window := [
  ⟨⟨-42654583923997928561925311124635070825978979, 134⟩, ⟨-653768582434227530769062355217669159245339, 133⟩⟩,
  ⟨⟨-1306305886946886241402064068485920826644521, 134⟩, ⟨-30332924011525537371858336214927794217249, 131⟩⟩,
  ⟨⟨-121311753457981421609678310078804718563071, 133⟩, ⟨-40007974483079394272518926143090639015663, 133⟩⟩,
  ⟨⟨-5000580141028338965981268003869651125087, 130⟩, ⟨-8233588485540035955023553966544882793077, 132⟩⟩,
  ⟨⟨-16466169774934525543571805376959858867845, 133⟩, ⟨-900088172574069994206538517859832444461, 130⟩⟩,
  ⟨⟨-3600152482994040955201307716470659147143, 132⟩, ⟨-1481911183574596070278591538135296155191, 132⟩⟩,
  ⟨⟨-2963646405629454213046703698931587858143, 133⟩, ⟨-488719245073606322027014464093528930633, 132⟩⟩,
  ⟨⟨-244341984387136596610890606341982386961, 131⟩, ⟨-363032933886985497321896141111500241925, 134⟩⟩,
  ⟨⟨-90749726804996227599276516553085583285, 132⟩, ⟨-11120153844806619702746435371111451625, 134⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private theorem upper : upperOK (descentCoeffs 11) first gaps = true := by
  decide +kernel

private theorem lower : ∀ i : Fin (lastRepresentative 12 - 2),
    lowerOK (rows.getD i.val []) gaps = true := by
  decide +kernel

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 12) :
    StrictNegativeInterlacing (originalQuotient 12 k) (eulerian 11) 9 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N012
