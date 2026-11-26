import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentPackedData.C127L064.N059

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N059

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L064.N059 LongCycleBounds.DescentNecklace.Packed.C127L064.N059.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L064.N059 LongCycleBounds.DescentNecklace.Packed.C127L064.N059.rows

private theorem actual : RepresentativeChecks 59 previousNodes rows :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L064.N059 LongCycleBounds.DescentNecklace.Packed.C127L064.N059.dataChecks

private def first : LongCycleFinite.Dyadic := ⟨-288230376151711744, 0⟩

private def gaps : List Window := [
  ⟨⟨-288221030302875648, 0⟩, ⟨-19000655872, 0⟩⟩,
  ⟨⟨-10410786816, 0⟩, ⟨-17483776, 0⟩⟩,
  ⟨⟨-16849088, 0⟩, ⟨-384384, 0⟩⟩,
  ⟨⟨-383606, 0⟩, ⟨-33491, 0⟩⟩,
  ⟨⟨-267791, 3⟩, ⟨-194345, 5⟩⟩,
  ⟨⟨-48575, 3⟩, ⟨-218823, 7⟩⟩,
  ⟨⟨-437587, 8⟩, ⟨-1279, 1⟩⟩,
  ⟨⟨-163697, 8⟩, ⟨-297471, 10⟩⟩,
  ⟨⟨-297451, 10⟩, ⟨-310405, 11⟩⟩,
  ⟨⟨-77597, 9⟩, ⟨-22421, 8⟩⟩,
  ⟨⟨-358721, 12⟩, ⟨-447945, 13⟩⟩,
  ⟨⟨-223965, 12⟩, ⟨-296929, 13⟩⟩,
  ⟨⟨-37115, 10⟩, ⟨-412681, 14⟩⟩,
  ⟨⟨-206335, 13⟩, ⟨-297827, 14⟩⟩,
  ⟨⟨-297819, 14⟩, ⟨-443215, 15⟩⟩,
  ⟨⟨-443205, 15⟩, ⟨-169073, 14⟩⟩,
  ⟨⟨-338139, 15⟩, ⟨-263359, 15⟩⟩,
  ⟨⟨-131677, 14⟩, ⟨-417289, 16⟩⟩,
  ⟨⟨-208641, 15⟩, ⟨-335315, 16⟩⟩,
  ⟨⟨-335309, 16⟩, ⟨-272637, 16⟩⟩,
  ⟨⟨-272633, 16⟩, ⟨-111927, 15⟩⟩,
  ⟨⟨-223851, 16⟩, ⟨-370573, 17⟩⟩,
  ⟨⟨-46321, 14⟩, ⟨-308739, 17⟩⟩,
  ⟨⟨-154367, 16⟩, ⟨-517151, 18⟩⟩,
  ⟨⟨-64643, 15⟩, ⟨-434873, 18⟩⟩,
  ⟨⟨-108717, 16⟩, ⟨-22923, 14⟩⟩,
  ⟨⟨-366763, 18⟩, ⟨-38741, 15⟩⟩,
  ⟨⟨-77481, 16⟩, ⟨-131073, 17⟩⟩,
  ⟨⟨-131071, 17⟩, ⟨-443459, 19⟩⟩,
  ⟨⟨-221727, 18⟩, ⟨-187367, 18⟩⟩,
  ⟨⟨-374729, 19⟩, ⟨-19753, 15⟩⟩,
  ⟨⟨-79011, 17⟩, ⟨-132883, 18⟩⟩,
  ⟨⟨-132881, 18⟩, ⟨-445167, 20⟩⟩,
  ⟨⟨-445161, 20⟩, ⟨-185445, 19⟩⟩,
  ⟨⟨-92721, 18⟩, ⟨-306987, 20⟩⟩,
  ⟨⟨-306983, 20⟩, ⟨-504117, 21⟩⟩,
  ⟨⟨-252055, 20⟩, ⟨-204945, 20⟩⟩,
  ⟨⟨-102471, 19⟩, ⟨-41171, 18⟩⟩,
  ⟨⟨-164681, 20⟩, ⟨-521881, 22⟩⟩,
  ⟨⟨-521873, 22⟩, ⟨-203229, 21⟩⟩,
  ⟨⟨-406451, 22⟩, ⟨-310101, 22⟩⟩,
  ⟨⟨-310095, 22⟩, ⟨-230743, 22⟩⟩,
  ⟨⟨-461477, 23⟩, ⟨-333041, 23⟩⟩,
  ⟨⟨-166517, 22⟩, ⟨-14465, 19⟩⟩,
  ⟨⟨-462869, 24⟩, ⟨-153413, 23⟩⟩,
  ⟨⟨-306817, 24⟩, ⟨-191563, 24⟩⟩,
  ⟨⟨-191557, 24⟩, ⟨-221399, 25⟩⟩,
  ⟨⟨-442783, 26⟩, ⟨-115515, 25⟩⟩,
  ⟨⟨-231021, 26⟩, ⟨-209899, 27⟩⟩,
  ⟨⟨-419779, 28⟩, ⟨-78517, 27⟩⟩,
  ⟨⟨-78513, 27⟩, ⟨-353649, 31⟩⟩,
  ⟨⟨-88407, 29⟩, ⟨-513087, 34⟩⟩,
  ⟨⟨-513051, 34⟩, ⟨-178815, 36⟩⟩,
  ⟨⟨-178801, 36⟩, ⟨-510525, 43⟩⟩,
  ⟨⟨-510483, 43⟩, ⟨-34489, 49⟩⟩,
  ⟨⟨-275885, 52⟩, ⟨-262165, 76⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private theorem upper : upperOK (descentCoeffs 58) first gaps = true := by
  decide +kernel

private theorem lower : ∀ i : Fin (lastRepresentative 59 - 2),
    lowerOK (rows.getD i.val []) gaps = true := by
  decide +kernel

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 59) :
    StrictNegativeInterlacing (originalQuotient 59 k) (eulerian 58) 56 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N059
