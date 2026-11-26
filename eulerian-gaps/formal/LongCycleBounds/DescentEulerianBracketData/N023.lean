import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentSweepData.N023

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N023

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentSweepData.N023 LongCycleBounds.DescentNecklace.Sweep.N023.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentSweepData.N023 LongCycleBounds.DescentNecklace.Sweep.N023.rows

private theorem actual : RepresentativeChecks 23 previousNodes rows :=
  representativeChecks_of_shared (by decide) previousNodes rows
    (descentFrozenConst LongCycleBounds.DescentSweepData.N023 LongCycleBounds.DescentNecklace.Sweep.N023.counts) (descentFrozenConst LongCycleBounds.DescentSweepData.N023 LongCycleBounds.DescentNecklace.Sweep.N023.signs)

private def first : LongCycleFinite.Dyadic := ⟨-4186864, 0⟩

private def gaps : List Window := [
  ⟨⟨-4186728, 0⟩, ⟨-111547, 4⟩⟩,
  ⟨⟨-27377, 2⟩, ⟨-110027, 8⟩⟩,
  ⟨⟨-219921, 9⟩, ⟨-351005, 12⟩⟩,
  ⟨⟨-175471, 11⟩, ⟨-236747, 13⟩⟩,
  ⟨⟨-473449, 14⟩, ⟨-422139, 15⟩⟩,
  ⟨⟨-422113, 15⟩, ⟨-110693, 14⟩⟩,
  ⟨⟨-3459, 9⟩, ⟨-256515, 16⟩⟩,
  ⟨⟨-256505, 16⟩, ⟨-158039, 16⟩⟩,
  ⟨⟨-316067, 17⟩, ⟨-403711, 18⟩⟩,
  ⟨⟨-403699, 18⟩, ⟨-65537, 16⟩⟩,
  ⟨⟨-524279, 19⟩, ⟨-340441, 19⟩⟩,
  ⟨⟨-340431, 19⟩, ⟨-108709, 18⟩⟩,
  ⟨⟨-434823, 20⟩, ⟨-133949, 19⟩⟩,
  ⟨⟨-267889, 20⟩, ⟨-155209, 20⟩⟩,
  ⟨⟨-155203, 20⟩, ⟨-325587, 22⟩⟩,
  ⟨⟨-81393, 20⟩, ⟨-290277, 23⟩⟩,
  ⟨⟨-290261, 23⟩, ⟨-391633, 25⟩⟩,
  ⟨⟨-391607, 25⟩, ⟨-156193, 26⟩⟩,
  ⟨⟨-312361, 27⟩, ⟨-155691, 30⟩⟩,
  ⟨⟨-38919, 28⟩, ⟨-262645, 40⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private theorem upper : upperOK (descentCoeffs 22) first gaps = true := by
  decide +kernel

private theorem lower : ∀ i : Fin (lastRepresentative 23 - 2),
    lowerOK (rows.getD i.val []) gaps = true := by
  decide +kernel

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 23) :
    StrictNegativeInterlacing (originalQuotient 23 k) (eulerian 22) 20 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N023
