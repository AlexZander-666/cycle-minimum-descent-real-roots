import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentSweepData.N028

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N028

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentSweepData.N028 LongCycleBounds.DescentNecklace.Sweep.N028.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentSweepData.N028 LongCycleBounds.DescentNecklace.Sweep.N028.rows

private theorem actual : RepresentativeChecks 28 previousNodes rows :=
  representativeChecks_of_shared (by decide) previousNodes rows
    (descentFrozenConst LongCycleBounds.DescentSweepData.N028 LongCycleBounds.DescentNecklace.Sweep.N028.counts) (descentFrozenConst LongCycleBounds.DescentSweepData.N028 LongCycleBounds.DescentNecklace.Sweep.N028.signs)

private def first : LongCycleFinite.Dyadic := ⟨-134164480, 0⟩

private def gaps : List Window := [
  ⟨⟨-134160128, 0⟩, ⟨-114259, 1⟩⟩,
  ⟨⟨-53038, 0⟩, ⟨-504191, 8⟩⟩,
  ⟨⟨-62955, 5⟩, ⟨-301321, 10⟩⟩,
  ⟨⟨-301243, 10⟩, ⟨-21437, 8⟩⟩,
  ⟨⟨-171475, 11⟩, ⟨-275511, 13⟩⟩,
  ⟨⟨-137745, 12⟩, ⟨-67865, 12⟩⟩,
  ⟨⟨-271445, 14⟩, ⟨-152235, 14⟩⟩,
  ⟨⟨-304457, 15⟩, ⟨-46501, 13⟩⟩,
  ⟨⟨-371995, 16⟩, ⟨-481569, 17⟩⟩,
  ⟨⟨-481555, 17⟩, ⟨-162017, 16⟩⟩,
  ⟨⟨-40503, 14⟩, ⟨-447061, 18⟩⟩,
  ⟨⟨-223525, 17⟩, ⟨-156365, 17⟩⟩,
  ⟨⟨-156361, 17⟩, ⟨-109873, 17⟩⟩,
  ⟨⟨-439481, 19⟩, ⟨-19215, 15⟩⟩,
  ⟨⟨-38429, 16⟩, ⟨-106041, 18⟩⟩,
  ⟨⟨-424153, 20⟩, ⟨-8919, 15⟩⟩,
  ⟨⟨-35675, 17⟩, ⟨-369463, 21⟩⟩,
  ⟨⟨-92363, 19⟩, ⟨-112859, 20⟩⟩,
  ⟨⟨-451421, 22⟩, ⟨-253159, 22⟩⟩,
  ⟨⟨-253149, 22⟩, ⟨-498885, 24⟩⟩,
  ⟨⟨-249431, 23⟩, ⟨-400737, 25⟩⟩,
  ⟨⟨-200357, 24⟩, ⟨-114051, 25⟩⟩,
  ⟨⟨-456173, 27⟩, ⟨-272883, 29⟩⟩,
  ⟨⟨-68215, 27⟩, ⟨-78973, 32⟩⟩,
  ⟨⟨-157931, 33⟩, ⟨-262277, 45⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private theorem upper : upperOK (descentCoeffs 27) first gaps = true := by
  decide +kernel

private theorem lower : ∀ i : Fin (lastRepresentative 28 - 2),
    lowerOK (rows.getD i.val []) gaps = true := by
  decide +kernel

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 28) :
    StrictNegativeInterlacing (originalQuotient 28 k) (eulerian 27) 25 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N028
