import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentPackedData.C127L048.N044

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N044

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L048.N044 LongCycleBounds.DescentNecklace.Packed.C127L048.N044.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L048.N044 LongCycleBounds.DescentNecklace.Packed.C127L048.N044.rows

private theorem actual : RepresentativeChecks 44 previousNodes rows :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L048.N044 LongCycleBounds.DescentNecklace.Packed.C127L048.N044.dataChecks

private def first : LongCycleFinite.Dyadic := ⟨-8796093022208, 0⟩

private def gaps : List Window := [
  ⟨⟨-8795807809536, 0⟩, ⟨-37256832, 0⟩⟩,
  ⟨⟨-36994560, 0⟩, ⟨-222077, 0⟩⟩,
  ⟨⟨-441161, 1⟩, ⟨-402247, 5⟩⟩,
  ⟨⟨-401943, 5⟩, ⟨-503671, 8⟩⟩,
  ⟨⟨-503539, 8⟩, ⟨-272265, 9⟩⟩,
  ⟨⟨-68057, 7⟩, ⟨-102053, 9⟩⟩,
  ⟨⟨-25511, 7⟩, ⟨-47245, 9⟩⟩,
  ⟨⟨-23621, 8⟩, ⟨-3157, 6⟩⟩,
  ⟨⟨-101019, 11⟩, ⟨-119623, 12⟩⟩,
  ⟨⟨-239237, 13⟩, ⟨-305285, 14⟩⟩,
  ⟨⟨-305275, 14⟩, ⟨-412037, 15⟩⟩,
  ⟨⟨-412025, 15⟩, ⟨-4535, 9⟩⟩,
  ⟨⟨-36279, 12⟩, ⟨-26417, 12⟩⟩,
  ⟨⟨-211331, 15⟩, ⟨-315825, 16⟩⟩,
  ⟨⟨-157909, 15⟩, ⟨-15049, 12⟩⟩,
  ⟨⟨-481559, 17⟩, ⟨-186463, 16⟩⟩,
  ⟨⟨-372919, 17⟩, ⟨-146123, 16⟩⟩,
  ⟨⟨-292241, 17⟩, ⟨-115517, 16⟩⟩,
  ⟨⟨-115515, 16⟩, ⟨-367477, 18⟩⟩,
  ⟨⟨-367471, 18⟩, ⟨-293273, 18⟩⟩,
  ⟨⟨-73317, 16⟩, ⟨-468645, 19⟩⟩,
  ⟨⟨-468637, 19⟩, ⟨-93503, 17⟩⟩,
  ⟨⟨-187003, 18⟩, ⟨-297451, 19⟩⟩,
  ⟨⟨-148723, 18⟩, ⟨-470289, 20⟩⟩,
  ⟨⟨-470281, 20⟩, ⟨-184275, 19⟩⟩,
  ⟨⟨-368543, 20⟩, ⟨-142703, 19⟩⟩,
  ⟨⟨-35675, 17⟩, ⟨-217595, 20⟩⟩,
  ⟨⟨-435181, 21⟩, ⟨-162585, 20⟩⟩,
  ⟨⟨-325163, 21⟩, ⟨-473543, 22⟩⟩,
  ⟨⟨-118383, 20⟩, ⟨-166783, 21⟩⟩,
  ⟨⟨-166779, 21⟩, ⟨-56277, 20⟩⟩,
  ⟨⟨-112551, 21⟩, ⟨-17953, 19⟩⟩,
  ⟨⟨-287239, 23⟩, ⟨-340131, 24⟩⟩,
  ⟨⟨-340119, 24⟩, ⟨-181827, 24⟩⟩,
  ⟨⟨-45455, 22⟩, ⟨-336703, 26⟩⟩,
  ⟨⟨-336687, 26⟩, ⟨-252433, 27⟩⟩,
  ⟨⟨-504839, 28⟩, ⟨-136441, 28⟩⟩,
  ⟨⟨-8527, 24⟩, ⟨-341733, 32⟩⟩,
  ⟨⟨-341707, 32⟩, ⟨-155085, 35⟩⟩,
  ⟨⟨-2423, 29⟩, ⟨-59305, 41⟩⟩,
  ⟨⟨-118599, 42⟩, ⟨-262149, 61⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private theorem upper : upperOK (descentCoeffs 43) first gaps = true := by
  decide +kernel

private theorem lower : ∀ i : Fin (lastRepresentative 44 - 2),
    lowerOK (rows.getD i.val []) gaps = true := by
  decide +kernel

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 44) :
    StrictNegativeInterlacing (originalQuotient 44 k) (eulerian 43) 41 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N044
