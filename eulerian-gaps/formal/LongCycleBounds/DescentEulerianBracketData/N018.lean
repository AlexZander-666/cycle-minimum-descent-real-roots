import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentSweepData.N018

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N018

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentSweepData.N018 LongCycleBounds.DescentNecklace.Sweep.N018.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentSweepData.N018 LongCycleBounds.DescentNecklace.Sweep.N018.rows

private theorem actual : RepresentativeChecks 18 previousNodes rows :=
  representativeChecks_of_shared (by decide) previousNodes rows
    (descentFrozenConst LongCycleBounds.DescentSweepData.N018 LongCycleBounds.DescentNecklace.Sweep.N018.counts) (descentFrozenConst LongCycleBounds.DescentSweepData.N018 LongCycleBounds.DescentNecklace.Sweep.N018.signs)

private def first : LongCycleFinite.Dyadic := ⟨-520329, 2⟩

private def gaps : List Window := [
  ⟨⟨-130078, 0⟩, ⟨-216057, 8⟩⟩,
  ⟨⟨-215051, 8⟩, ⟨-181961, 11⟩⟩,
  ⟨⟨-363799, 12⟩, ⟨-379139, 14⟩⟩,
  ⟨⟨-94773, 12⟩, ⟨-147841, 14⟩⟩,
  ⟨⟨-73915, 13⟩, ⟨-283599, 16⟩⟩,
  ⟨⟨-283583, 16⟩, ⟨-9505, 12⟩⟩,
  ⟨⟨-304147, 17⟩, ⟨-86269, 16⟩⟩,
  ⟨⟨-172531, 17⟩, ⟨-398301, 19⟩⟩,
  ⟨⟨-199143, 18⟩, ⟨-451883, 20⟩⟩,
  ⟨⟨-451865, 20⟩, ⟨-484649, 21⟩⟩,
  ⟨⟨-484629, 21⟩, ⟨-464857, 22⟩⟩,
  ⟨⟨-232417, 21⟩, ⟨-181257, 22⟩⟩,
  ⟨⟨-362491, 23⟩, ⟨-377783, 25⟩⟩,
  ⟨⟨-188877, 24⟩, ⟨-159183, 27⟩⟩,
  ⟨⟨-2487, 21⟩, ⟨-132087, 34⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private theorem upper : upperOK (descentCoeffs 17) first gaps = true := by
  decide +kernel

private theorem lower : ∀ i : Fin (lastRepresentative 18 - 2),
    lowerOK (rows.getD i.val []) gaps = true := by
  decide +kernel

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 18) :
    StrictNegativeInterlacing (originalQuotient 18 k) (eulerian 17) 15 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N018
