import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentPackedData.C127L048.N042

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N042

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L048.N042 LongCycleBounds.DescentNecklace.Packed.C127L048.N042.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L048.N042 LongCycleBounds.DescentNecklace.Packed.C127L048.N042.rows

private theorem actual : RepresentativeChecks 42 previousNodes rows :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L048.N042 LongCycleBounds.DescentNecklace.Packed.C127L048.N042.dataChecks

private def first : LongCycleFinite.Dyadic := ⟨-2199023255552, 0⟩

private def gaps : List Window := [
  ⟨⟨-2198951952384, 0⟩, ⟨-16515104, 0⟩⟩,
  ⟨⟨-16449536, 0⟩, ⟨-496513, 2⟩⟩,
  ⟨⟨-493863, 2⟩, ⟨-507621, 6⟩⟩,
  ⟨⟨-126821, 4⟩, ⟨-85795, 6⟩⟩,
  ⟨⟨-171549, 7⟩, ⟨-390693, 10⟩⟩,
  ⟨⟨-390643, 10⟩, ⟨-151951, 10⟩⟩,
  ⟨⟨-303877, 11⟩, ⟨-144549, 11⟩⟩,
  ⟨⟨-289081, 12⟩, ⟨-157693, 12⟩⟩,
  ⟨⟨-78843, 11⟩, ⟨-189569, 13⟩⟩,
  ⟨⟨-94781, 12⟩, ⟨-489321, 15⟩⟩,
  ⟨⟨-244653, 14⟩, ⟨-332977, 15⟩⟩,
  ⟨⟨-41621, 12⟩, ⟨-471821, 16⟩⟩,
  ⟨⟨-235905, 15⟩, ⟨-86203, 14⟩⟩,
  ⟨⟨-86201, 14⟩, ⟨-516163, 17⟩⟩,
  ⟨⟨-516153, 17⟩, ⟨-393487, 17⟩⟩,
  ⟨⟨-393479, 17⟩, ⟨-304157, 17⟩⟩,
  ⟨⟨-304151, 17⟩, ⟨-237501, 17⟩⟩,
  ⟨⟨-237497, 17⟩, ⟨-373485, 18⟩⟩,
  ⟨⟨-373479, 18⟩, ⟨-147423, 17⟩⟩,
  ⟨⟨-294841, 18⟩, ⟨-466149, 19⟩⟩,
  ⟨⟨-466141, 19⟩, ⟨-91999, 17⟩⟩,
  ⟨⟨-183995, 18⟩, ⟨-144673, 18⟩⟩,
  ⟨⟨-72335, 17⟩, ⟨-56485, 17⟩⟩,
  ⟨⟨-14121, 15⟩, ⟨-174645, 19⟩⟩,
  ⟨⟨-349283, 20⟩, ⟨-266275, 20⟩⟩,
  ⟨⟨-133135, 19⟩, ⟨-398603, 21⟩⟩,
  ⟨⟨-398595, 21⟩, ⟨-291301, 21⟩⟩,
  ⟨⟨-145647, 20⟩, ⟨-206387, 21⟩⟩,
  ⟨⟨-103191, 20⟩, ⟨-280883, 22⟩⟩,
  ⟨⟨-280875, 22⟩, ⟨-362513, 23⟩⟩,
  ⟨⟨-181251, 22⟩, ⟨-108953, 22⟩⟩,
  ⟨⟨-435797, 24⟩, ⟨-118859, 23⟩⟩,
  ⟨⟨-237709, 24⟩, ⟨-452277, 26⟩⟩,
  ⟨⟨-452257, 26⟩, ⟨-351807, 27⟩⟩,
  ⟨⟨-87947, 25⟩, ⟨-400587, 29⟩⟩,
  ⟨⟨-400561, 29⟩, ⟨-135443, 30⟩⟩,
  ⟨⟨-270865, 31⟩, ⟨-69523, 33⟩⟩,
  ⟨⟨-69517, 33⟩, ⟨-33415, 39⟩⟩,
  ⟨⟨-133647, 41⟩, ⟨-262149, 59⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private theorem upper : upperOK (descentCoeffs 41) first gaps = true := by
  decide +kernel

private theorem lower : ∀ i : Fin (lastRepresentative 42 - 2),
    lowerOK (rows.getD i.val []) gaps = true := by
  decide +kernel

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 42) :
    StrictNegativeInterlacing (originalQuotient 42 k) (eulerian 41) 39 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N042
