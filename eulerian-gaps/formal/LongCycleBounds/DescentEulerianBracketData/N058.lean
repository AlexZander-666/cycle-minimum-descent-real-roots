import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentPackedData.C127L064.N058

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N058

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L064.N058 LongCycleBounds.DescentNecklace.Packed.C127L064.N058.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L064.N058 LongCycleBounds.DescentNecklace.Packed.C127L064.N058.rows

private theorem actual : RepresentativeChecks 58 previousNodes rows :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L064.N058 LongCycleBounds.DescentNecklace.Packed.C127L064.N058.dataChecks

private def first : LongCycleFinite.Dyadic := ⟨-144115188075855872, 0⟩

private def gaps : List Window := [
  ⟨⟨-144110515151437824, 0⟩, ⟨-12558270464, 0⟩⟩,
  ⟨⟨-8263335936, 0⟩, ⟨-13293216, 0⟩⟩,
  ⟨⟨-12789440, 0⟩, ⟨-306949, 0⟩⟩,
  ⟨⟨-306366, 0⟩, ⟨-444455, 4⟩⟩,
  ⟨⟨-222119, 3⟩, ⟨-331173, 6⟩⟩,
  ⟨⟨-331099, 6⟩, ⟨-95051, 6⟩⟩,
  ⟨⟨-190077, 7⟩, ⟨-18037, 5⟩⟩,
  ⟨⟨-144283, 8⟩, ⟨-8287, 5⟩⟩,
  ⟨⟨-132583, 9⟩, ⟨-279183, 11⟩⟩,
  ⟨⟨-279169, 11⟩, ⟨-324951, 12⟩⟩,
  ⟨⟨-324937, 12⟩, ⟨-408089, 13⟩⟩,
  ⟨⟨-408075, 13⟩, ⟨-271773, 13⟩⟩,
  ⟨⟨-271765, 13⟩, ⟨-94785, 12⟩⟩,
  ⟨⟨-189565, 13⟩, ⟨-274449, 14⟩⟩,
  ⟨⟨-274443, 14⟩, ⟨-409423, 15⟩⟩,
  ⟨⟨-204707, 14⟩, ⟨-312955, 15⟩⟩,
  ⟨⟨-78237, 13⟩, ⟨-488179, 16⟩⟩,
  ⟨⟨-244085, 15⟩, ⟨-387143, 16⟩⟩,
  ⟨⟨-6049, 10⟩, ⟨-155641, 15⟩⟩,
  ⟨⟨-77819, 14⟩, ⟨-31645, 13⟩⟩,
  ⟨⟨-63289, 14⟩, ⟨-415679, 17⟩⟩,
  ⟨⟨-415673, 17⟩, ⟨-343905, 17⟩⟩,
  ⟨⟨-85975, 15⟩, ⟨-286297, 17⟩⟩,
  ⟨⟨-286293, 17⟩, ⟨-479009, 18⟩⟩,
  ⟨⟨-479003, 18⟩, ⟨-25137, 14⟩⟩,
  ⟨⟨-402187, 18⟩, ⟨-84641, 16⟩⟩,
  ⟨⟨-338559, 18⟩, ⟨-285433, 18⟩⟩,
  ⟨⟨-285429, 18⟩, ⟨-481517, 19⟩⟩,
  ⟨⟨-481511, 19⟩, ⟨-405951, 19⟩⟩,
  ⟨⟨-405945, 19⟩, ⟨-170863, 18⟩⟩,
  ⟨⟨-341721, 19⟩, ⟨-17933, 15⟩⟩,
  ⟨⟨-71731, 17⟩, ⟨-480063, 20⟩⟩,
  ⟨⟨-480057, 20⟩, ⟨-99911, 18⟩⟩,
  ⟨⟨-199819, 19⟩, ⟨-165321, 19⟩⟩,
  ⟨⟨-330637, 20⟩, ⟨-135725, 19⟩⟩,
  ⟨⟨-135723, 19⟩, ⟨-441533, 21⟩⟩,
  ⟨⟨-441527, 21⟩, ⟨-177509, 20⟩⟩,
  ⟨⟨-88753, 19⟩, ⟨-281541, 21⟩⟩,
  ⟨⟨-4399, 15⟩, ⟨-3431, 15⟩⟩,
  ⟨⟨-54895, 19⟩, ⟨-167849, 21⟩⟩,
  ⟨⟨-335691, 22⟩, ⟨-500797, 23⟩⟩,
  ⟨⟨-500787, 23⟩, ⟨-362511, 23⟩⟩,
  ⟨⟨-362503, 23⟩, ⟨-252863, 23⟩⟩,
  ⟨⟨-252857, 23⟩, ⟨-336797, 24⟩⟩,
  ⟨⟨-84197, 22⟩, ⟨-211481, 24⟩⟩,
  ⟨⟨-422949, 25⟩, ⟨-246157, 25⟩⟩,
  ⟨⟨-492297, 26⟩, ⟨-259157, 26⟩⟩,
  ⟨⟨-259147, 26⟩, ⟨-14883, 23⟩⟩,
  ⟨⟨-476235, 28⟩, ⟨-361541, 29⟩⟩,
  ⟨⟨-180761, 28⟩, ⟨-103779, 29⟩⟩,
  ⟨⟨-415091, 31⟩, ⟨-309371, 33⟩⟩,
  ⟨⟨-309349, 33⟩, ⟨-14019, 32⟩⟩,
  ⟨⟨-448573, 37⟩, ⟨-340895, 42⟩⟩,
  ⟨⟨-170433, 41⟩, ⟨-413911, 52⟩⟩,
  ⟨⟨-25867, 48⟩, ⟨-262149, 75⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private theorem upper : upperOK (descentCoeffs 57) first gaps = true := by
  decide +kernel

private theorem lower : ∀ i : Fin (lastRepresentative 58 - 2),
    lowerOK (rows.getD i.val []) gaps = true := by
  decide +kernel

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 58) :
    StrictNegativeInterlacing (originalQuotient 58 k) (eulerian 57) 55 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N058
