import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentSweepData.N025

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N025

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentSweepData.N025 LongCycleBounds.DescentNecklace.Sweep.N025.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentSweepData.N025 LongCycleBounds.DescentNecklace.Sweep.N025.rows

private theorem actual : RepresentativeChecks 25 previousNodes rows :=
  representativeChecks_of_shared (by decide) previousNodes rows
    (descentFrozenConst LongCycleBounds.DescentSweepData.N025 LongCycleBounds.DescentNecklace.Sweep.N025.counts) (descentFrozenConst LongCycleBounds.DescentSweepData.N025 LongCycleBounds.DescentNecklace.Sweep.N025.signs)

private def first : LongCycleFinite.Dyadic := ⟨-16760832, 0⟩

private def gaps : List Window := [
  ⟨⟨-16760288, 0⟩, ⟨-511029, 5⟩⟩,
  ⟨⟨-247343, 4⟩, ⟨-406385, 9⟩⟩,
  ⟨⟨-203039, 8⟩, ⟨-72309, 9⟩⟩,
  ⟨⟨-36147, 8⟩, ⟨-365327, 13⟩⟩,
  ⟨⟨-365289, 13⟩, ⟨-156541, 13⟩⟩,
  ⟨⟨-78265, 12⟩, ⟨-321165, 15⟩⟩,
  ⟨⟨-321149, 15⟩, ⟨-184305, 15⟩⟩,
  ⟨⟨-368595, 16⟩, ⟨-14209, 12⟩⟩,
  ⟨⟨-454673, 17⟩, ⟨-73413, 15⟩⟩,
  ⟨⟨-293643, 17⟩, ⟨-389861, 18⟩⟩,
  ⟨⟨-194925, 17⟩, ⟨-131075, 17⟩⟩,
  ⟨⟨-131071, 17⟩, ⟨-352549, 19⟩⟩,
  ⟨⟨-352539, 19⟩, ⟨-468055, 20⟩⟩,
  ⟨⟨-234021, 19⟩, ⟨-75571, 18⟩⟩,
  ⟨⟨-302275, 20⟩, ⟨-186441, 20⟩⟩,
  ⟨⟨-372869, 21⟩, ⟨-106985, 20⟩⟩,
  ⟨⟨-106981, 20⟩, ⟨-109751, 21⟩⟩,
  ⟨⟨-54873, 20⟩, ⟨-376249, 24⟩⟩,
  ⟨⟨-376229, 24⟩, ⟨-475191, 26⟩⟩,
  ⟨⟨-59395, 23⟩, ⟨-169185, 27⟩⟩,
  ⟨⟨-338343, 28⟩, ⟨-135917, 31⟩⟩,
  ⟨⟨-4247, 26⟩, ⟨-262421, 42⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private theorem upper : upperOK (descentCoeffs 24) first gaps = true := by
  decide +kernel

private theorem lower : ∀ i : Fin (lastRepresentative 25 - 2),
    lowerOK (rows.getD i.val []) gaps = true := by
  decide +kernel

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 25) :
    StrictNegativeInterlacing (originalQuotient 25 k) (eulerian 24) 22 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N025
