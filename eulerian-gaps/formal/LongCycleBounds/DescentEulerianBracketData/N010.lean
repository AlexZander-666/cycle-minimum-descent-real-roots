import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentFiniteData.N010

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N010

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentFiniteData.N010 LongCycleBounds.DescentNecklace.N010.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentFiniteData.N010 LongCycleBounds.DescentNecklace.N010.rows

private theorem actual : RepresentativeChecks 10 previousNodes rows :=
  descentFrozenConst LongCycleBounds.DescentFiniteData.N010 LongCycleBounds.DescentNecklace.N010.checks

private def first : LongCycleFinite.Dyadic := ⟨-9561624667040884498347387420807057, 104⟩

private def gaps : List Window := [
  ⟨⟨-4780636860375446775664373112271837, 103⟩, ⟨-469297698010647066397659253201887, 104⟩⟩,
  ⟨⟨-117258024706643030830792005581509, 102⟩, ⟨-100543134005862838560479302545539, 104⟩⟩,
  ⟨⟨-50264869169782683161206016115873, 103⟩, ⟨-16679881191410955072184245618489, 103⟩⟩,
  ⟨⟨-33357116139947106358969017272915, 104⟩, ⟨-6166163013584612229939436395751, 103⟩⟩,
  ⟨⟨-12331482646724881962717798179997, 104⟩, ⟨-1023002381234357431182831912483, 102⟩⟩,
  ⟨⟨-4091703687473466767087130847677, 104⟩, ⟨-876684192061665031822922343993, 104⟩⟩,
  ⟨⟨-219150227572912886363257005345, 102⟩, ⟨-43028800772254142596770194175, 104⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private theorem upper : upperOK (descentCoeffs 9) first gaps = true := by
  decide +kernel

private theorem lower : ∀ i : Fin (lastRepresentative 10 - 2),
    lowerOK (rows.getD i.val []) gaps = true := by
  decide +kernel

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 10) :
    StrictNegativeInterlacing (originalQuotient 10 k) (eulerian 9) 7 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N010
