import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentFiniteData.N011

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N011

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentFiniteData.N011 LongCycleBounds.DescentNecklace.N011.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentFiniteData.N011 LongCycleBounds.DescentNecklace.N011.rows

private theorem actual : RepresentativeChecks 11 previousNodes rows :=
  descentFrozenConst LongCycleBounds.DescentFiniteData.N011 LongCycleBounds.DescentNecklace.N011.checks

private def first : LongCycleFinite.Dyadic := ⟨-640597939277168885895962761513201326941, 119⟩

private def gaps : List Window := [
  ⟨⟨-80071940475086049881623024209526614613, 116⟩, ⟨-3119607879851756465447810067393263781, 116⟩⟩,
  ⟨⟨-1558667404388943572795157827048517965, 115⟩, ⟨-2502775631126471292305070473736634119, 118⟩⟩,
  ⟨⟨-156400437666514087300790719110391175, 114⟩, ⟨-1632709921001038427665819944322277, 109⟩⟩,
  ⟨⟨-6530314855903283948208672145155251, 111⟩, ⟨-83081582762088747811011760823116105, 116⟩⟩,
  ⟨⟨-332305304513430553789006672873695223, 118⟩, ⟨-132112635565736518472654583965567593, 118⟩⟩,
  ⟨⟨-16513049439750722108461149357416331, 115⟩, ⟨-11032340819983726706365463884314015, 116⟩⟩,
  ⟨⟨-22063074032939939017752292141594971, 117⟩, ⟨-2212968287002022201678893613043213, 116⟩⟩,
  ⟨⟨-553189970721817849234252889997483, 114⟩, ⟨-344811102677942719373640438073875, 118⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private theorem upper : upperOK (descentCoeffs 10) first gaps = true := by
  decide +kernel

private theorem lower : ∀ i : Fin (lastRepresentative 11 - 2),
    lowerOK (rows.getD i.val []) gaps = true := by
  decide +kernel

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 11) :
    StrictNegativeInterlacing (originalQuotient 11 k) (eulerian 10) 8 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N011
