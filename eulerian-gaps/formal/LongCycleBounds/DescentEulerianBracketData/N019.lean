import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentSweepData.N019

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N019

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentSweepData.N019 LongCycleBounds.DescentNecklace.Sweep.N019.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentSweepData.N019 LongCycleBounds.DescentNecklace.Sweep.N019.rows

private theorem actual : RepresentativeChecks 19 previousNodes rows :=
  representativeChecks_of_shared (by decide) previousNodes rows
    (descentFrozenConst LongCycleBounds.DescentSweepData.N019 LongCycleBounds.DescentNecklace.Sweep.N019.counts) (descentFrozenConst LongCycleBounds.DescentSweepData.N019 LongCycleBounds.DescentNecklace.Sweep.N019.signs)

private def first : LongCycleFinite.Dyadic := ⟨-260661, 0⟩

private def gaps : List Window := [
  ⟨⟨-521305, 1⟩, ⟨-330657, 8⟩⟩,
  ⟨⟨-328637, 8⟩, ⟨-125517, 10⟩⟩,
  ⟨⟨-501879, 12⟩, ⟨-497233, 14⟩⟩,
  ⟨⟨-497167, 14⟩, ⟨-377913, 15⟩⟩,
  ⟨⟨-94471, 13⟩, ⟨-358801, 16⟩⟩,
  ⟨⟨-179391, 15⟩, ⟨-385403, 17⟩⟩,
  ⟨⟨-192693, 16⟩, ⟨-110705, 16⟩⟩,
  ⟨⟨-442803, 18⟩, ⟨-262151, 18⟩⟩,
  ⟨⟨-524283, 19⟩, ⟨-155195, 18⟩⟩,
  ⟨⟨-310379, 19⟩, ⟨-178313, 19⟩⟩,
  ⟨⟨-89153, 18⟩, ⟨-191535, 20⟩⟩,
  ⟨⟨-383053, 21⟩, ⟨-363691, 22⟩⟩,
  ⟨⟨-363673, 22⟩, ⟨-69111, 21⟩⟩,
  ⟨⟨-138213, 22⟩, ⟨-136901, 24⟩⟩,
  ⟨⟨-68445, 23⟩, ⟨-416359, 29⟩⟩,
  ⟨⟨-6505, 23⟩, ⟨-263641, 36⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private theorem upper : upperOK (descentCoeffs 18) first gaps = true := by
  decide +kernel

private theorem lower : ∀ i : Fin (lastRepresentative 19 - 2),
    lowerOK (rows.getD i.val []) gaps = true := by
  decide +kernel

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 19) :
    StrictNegativeInterlacing (originalQuotient 19 k) (eulerian 18) 16 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N019
