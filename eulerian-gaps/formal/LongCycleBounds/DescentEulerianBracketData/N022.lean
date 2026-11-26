import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentSweepData.N022

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N022

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentSweepData.N022 LongCycleBounds.DescentNecklace.Sweep.N022.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentSweepData.N022 LongCycleBounds.DescentNecklace.Sweep.N022.rows

private theorem actual : RepresentativeChecks 22 previousNodes rows :=
  representativeChecks_of_shared (by decide) previousNodes rows
    (descentFrozenConst LongCycleBounds.DescentSweepData.N022 LongCycleBounds.DescentNecklace.Sweep.N022.counts) (descentFrozenConst LongCycleBounds.DescentSweepData.N022 LongCycleBounds.DescentNecklace.Sweep.N022.signs)

private def first : LongCycleFinite.Dyadic := ⟨-2092212, 0⟩

private def gaps : List Window := [
  ⟨⟨-2092144, 0⟩, ⟨-293283, 6⟩⟩,
  ⟨⟨-144605, 5⟩, ⟨-322925, 10⟩⟩,
  ⟨⟨-322751, 10⟩, ⟨-136141, 11⟩⟩,
  ⟨⟨-68059, 10⟩, ⟨-189569, 13⟩⟩,
  ⟨⟨-11847, 9⟩, ⟨-344213, 15⟩⟩,
  ⟨⟨-344193, 15⟩, ⟨-364331, 16⟩⟩,
  ⟨⟨-182157, 15⟩, ⟨-423061, 17⟩⟩,
  ⟨⟨-423045, 17⟩, ⟨-519213, 18⟩⟩,
  ⟨⟨-129799, 16⟩, ⟨-164095, 17⟩⟩,
  ⟨⟨-328179, 18⟩, ⟨-52349, 16⟩⟩,
  ⟨⟨-418779, 19⟩, ⟨-132357, 18⟩⟩,
  ⟨⟨-264705, 19⟩, ⟨-324877, 20⟩⟩,
  ⟨⟨-162433, 19⟩, ⟨-377247, 21⟩⟩,
  ⟨⟨-377233, 21⟩, ⟨-399313, 22⟩⟩,
  ⟨⟨-6239, 16⟩, ⟨-181255, 22⟩⟩,
  ⟨⟨-362491, 23⟩, ⟨-63109, 22⟩⟩,
  ⟨⟨-63105, 22⟩, ⟨-425749, 27⟩⟩,
  ⟨⟨-425715, 27⟩, ⟨-236131, 30⟩⟩,
  ⟨⟨-472217, 31⟩, ⟨-262789, 39⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private theorem upper : upperOK (descentCoeffs 21) first gaps = true := by
  decide +kernel

private theorem lower : ∀ i : Fin (lastRepresentative 22 - 2),
    lowerOK (rows.getD i.val []) gaps = true := by
  decide +kernel

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 22) :
    StrictNegativeInterlacing (originalQuotient 22 k) (eulerian 21) 19 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N022
