import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentSweepData.N026

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N026

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentSweepData.N026 LongCycleBounds.DescentNecklace.Sweep.N026.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentSweepData.N026 LongCycleBounds.DescentNecklace.Sweep.N026.rows

private theorem actual : RepresentativeChecks 26 previousNodes rows :=
  representativeChecks_of_shared (by decide) previousNodes rows
    (descentFrozenConst LongCycleBounds.DescentSweepData.N026 LongCycleBounds.DescentNecklace.Sweep.N026.counts) (descentFrozenConst LongCycleBounds.DescentSweepData.N026 LongCycleBounds.DescentNecklace.Sweep.N026.signs)

private def first : LongCycleFinite.Dyadic := ⟨-33529856, 0⟩

private def gaps : List Window := [
  ⟨⟨-33528768, 0⟩, ⟨-382249, 4⟩⟩,
  ⟨⟨-365895, 4⟩, ⟨-275389, 8⟩⟩,
  ⟨⟨-275155, 8⟩, ⟨-11565, 6⟩⟩,
  ⟨⟨-369997, 11⟩, ⟨-56473, 10⟩⟩,
  ⟨⟨-225867, 12⟩, ⟨-189577, 13⟩⟩,
  ⟨⟨-379127, 14⟩, ⟨-192019, 14⟩⟩,
  ⟨⟨-384019, 15⟩, ⟨-437799, 16⟩⟩,
  ⟨⟨-218891, 15⟩, ⟨-134747, 15⟩⟩,
  ⟨⟨-67371, 14⟩, ⟨-348875, 17⟩⟩,
  ⟨⟨-5451, 11⟩, ⟨-466209, 18⟩⟩,
  ⟨⟨-116549, 16⟩, ⟨-158507, 17⟩⟩,
  ⟨⟨-317005, 18⟩, ⟨-216777, 18⟩⟩,
  ⟨⟨-433543, 19⟩, ⟨-294811, 19⟩⟩,
  ⟨⟨-294803, 19⟩, ⟨-393957, 20⟩⟩,
  ⟨⟨-196973, 19⟩, ⟨-255007, 20⟩⟩,
  ⟨⟨-509999, 21⟩, ⟨-313935, 21⟩⟩,
  ⟨⟨-78481, 19⟩, ⟨-178943, 21⟩⟩,
  ⟨⟨-22367, 18⟩, ⟨-181255, 22⟩⟩,
  ⟨⟨-181247, 22⟩, ⟨-304257, 24⟩⟩,
  ⟨⟨-304241, 24⟩, ⟨-371403, 26⟩⟩,
  ⟨⟨-185689, 25⟩, ⟨-249659, 28⟩⟩,
  ⟨⟨-249639, 28⟩, ⟨-22485, 29⟩⟩,
  ⟨⟨-179863, 32⟩, ⟨-262373, 43⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private theorem upper : upperOK (descentCoeffs 25) first gaps = true := by
  decide +kernel

private theorem lower : ∀ i : Fin (lastRepresentative 26 - 2),
    lowerOK (rows.getD i.val []) gaps = true := by
  decide +kernel

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 26) :
    StrictNegativeInterlacing (originalQuotient 26 k) (eulerian 25) 23 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N026
