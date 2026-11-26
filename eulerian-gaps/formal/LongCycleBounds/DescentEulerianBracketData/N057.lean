import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentPackedData.C127L064.N057

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N057

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L064.N057 LongCycleBounds.DescentNecklace.Packed.C127L064.N057.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L064.N057 LongCycleBounds.DescentNecklace.Packed.C127L064.N057.rows

private theorem actual : RepresentativeChecks 57 previousNodes rows :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L064.N057 LongCycleBounds.DescentNecklace.Packed.C127L064.N057.dataChecks

private def first : LongCycleFinite.Dyadic := ⟨-72057594037927936, 0⟩

private def gaps : List Window := [
  ⟨⟨-72055257575718912, 0⟩, ⟨-9337077760, 0⟩⟩,
  ⟨⟨-7189610496, 0⟩, ⟨-9920576, 0⟩⟩,
  ⟨⟨-9613216, 0⟩, ⟨-244389, 0⟩⟩,
  ⟨⟨-487927, 1⟩, ⟨-368521, 4⟩⟩,
  ⟨⟨-92087, 2⟩, ⟨-17627, 2⟩⟩,
  ⟨⟨-281971, 6⟩, ⟨-330163, 8⟩⟩,
  ⟨⟨-330121, 8⟩, ⟨-508615, 10⟩⟩,
  ⟨⟨-508571, 10⟩, ⟨-118153, 9⟩⟩,
  ⟨⟨-236291, 10⟩, ⟨-125501, 10⟩⟩,
  ⟨⟨-501979, 12⟩, ⟨-294215, 12⟩⟩,
  ⟨⟨-294203, 12⟩, ⟨-371595, 13⟩⟩,
  ⟨⟨-185791, 12⟩, ⟨-497207, 14⟩⟩,
  ⟨⟨-497193, 14⟩, ⟨-348103, 14⟩⟩,
  ⟨⟨-174047, 13⟩, ⟨-252735, 14⟩⟩,
  ⟨⟨-252729, 14⟩, ⟨-377911, 15⟩⟩,
  ⟨⟨-377903, 15⟩, ⟨-144699, 14⟩⟩,
  ⟨⟨-18087, 11⟩, ⟨-452027, 16⟩⟩,
  ⟨⟨-452019, 16⟩, ⟨-89699, 14⟩⟩,
  ⟨⟨-179395, 15⟩, ⟨-288635, 16⟩⟩,
  ⟨⟨-144315, 15⟩, ⟨-234771, 16⟩⟩,
  ⟨⟨-469535, 17⟩, ⟨-385395, 17⟩⟩,
  ⟨⟨-385389, 17⟩, ⟨-4979, 11⟩⟩,
  ⟨⟨-318651, 17⟩, ⟨-66255, 15⟩⟩,
  ⟨⟨-33127, 14⟩, ⟨-442807, 18⟩⟩,
  ⟨⟨-442801, 18⟩, ⟨-371151, 18⟩⟩,
  ⟨⟨-185573, 17⟩, ⟨-311759, 18⟩⟩,
  ⟨⟨-155877, 17⟩, ⟨-262145, 18⟩⟩,
  ⟨⟨-262141, 18⟩, ⟨-440859, 19⟩⟩,
  ⟨⟨-440853, 19⟩, ⟨-370307, 19⟩⟩,
  ⟨⟨-185151, 18⟩, ⟨-19399, 15⟩⟩,
  ⟨⟨-77595, 17⟩, ⟨-518607, 20⟩⟩,
  ⟨⟨-518601, 20⟩, ⟨-107829, 18⟩⟩,
  ⟨⟨-215655, 19⟩, ⟨-22289, 16⟩⟩,
  ⟨⟨-356619, 20⟩, ⟨-292713, 20⟩⟩,
  ⟨⟨-73177, 18⟩, ⟨-29761, 17⟩⟩,
  ⟨⟨-476169, 21⟩, ⟨-95765, 19⟩⟩,
  ⟨⟨-191527, 20⟩, ⟨-38007, 18⟩⟩,
  ⟨⟨-304051, 21⟩, ⟨-237463, 21⟩⟩,
  ⟨⟨-474917, 22⟩, ⟨-363685, 22⟩⟩,
  ⟨⟨-181839, 21⟩, ⟨-33989, 19⟩⟩,
  ⟨⟨-135953, 21⟩, ⟨-394833, 23⟩⟩,
  ⟨⟨-49353, 20⟩, ⟨-276431, 23⟩⟩,
  ⟨⟨-34553, 20⟩, ⟨-184939, 23⟩⟩,
  ⟨⟨-92467, 22⟩, ⟨-233577, 24⟩⟩,
  ⟨⟨-467141, 25⟩, ⟨-136895, 24⟩⟩,
  ⟨⟨-68445, 23⟩, ⟨-145409, 25⟩⟩,
  ⟨⟨-145403, 25⟩, ⟨-135115, 26⟩⟩,
  ⟨⟨-135109, 26⟩, ⟨-416315, 29⟩⟩,
  ⟨⟨-208147, 28⟩, ⟨-243679, 30⟩⟩,
  ⟨⟨-487329, 31⟩, ⟨-373117, 33⟩⟩,
  ⟨⟨-373091, 33⟩, ⟨-140689, 35⟩⟩,
  ⟨⟨-70339, 34⟩, ⟨-455267, 42⟩⟩,
  ⟨⟨-455229, 42⟩, ⟨-310467, 51⟩⟩,
  ⟨⟨-310437, 51⟩, ⟨-262165, 74⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private theorem upper : upperOK (descentCoeffs 56) first gaps = true := by
  decide +kernel

private theorem lower : ∀ i : Fin (lastRepresentative 57 - 2),
    lowerOK (rows.getD i.val []) gaps = true := by
  decide +kernel

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 57) :
    StrictNegativeInterlacing (originalQuotient 57 k) (eulerian 56) 54 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N057
