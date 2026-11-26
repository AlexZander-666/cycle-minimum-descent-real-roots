import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentFiniteData.N014

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N014

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentFiniteData.N014 LongCycleBounds.DescentNecklace.N014.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentFiniteData.N014 LongCycleBounds.DescentNecklace.N014.rows

private theorem actual : RepresentativeChecks 14 previousNodes rows :=
  descentFrozenConst LongCycleBounds.DescentFiniteData.N014 LongCycleBounds.DescentNecklace.N014.checks

private def first : LongCycleFinite.Dyadic := ⟨-730181354393262189181606454716041239453156906890661, 156⟩

private def gaps : List Window := [
  ⟨⟨-186920390896701733728845025680761658744471274645638199, 164⟩, ⟨-868417884783345084271638455990205825553908818760417, 162⟩⟩,
  ⟨⟨-3468150539780004810521443144531619917050144847336347, 164⟩, ⟨-270583461200923970149873650211237039622601982547695, 163⟩⟩,
  ⟨⟨-541054818130973063384814844185790892546929443073077, 164⟩, ⟨-168362879077940062598799241492522605841079441707605, 164⟩⟩,
  ⟨⟨-21043402607767809742498711471635176110628689360561, 161⟩, ⟨-8775033502048781563372987258120012306769873892009, 161⟩⟩,
  ⟨⟨-2193623143360945286693554740161957366451005119673, 159⟩, ⟨-16658477924751298821321726474222597715767081939773, 163⟩⟩,
  ⟨⟨-260275681345870754359330036456456175088684486377, 157⟩, ⟨-2051676322369917869411992882614290658167729753507, 161⟩⟩,
  ⟨⟨-1025790083242171436238866636325427082029045634821, 160⟩, ⟨-1947421224419984877612399875916533999666059696837, 162⟩⟩,
  ⟨⟨-973662668621420651852112126084160218084478856683, 161⟩, ⟨-203007614765169116754019369401423718460381987725, 160⟩⟩,
  ⟨⟨-3247935674204980665641223847611084406239494978015, 164⟩, ⟨-505262936184058276292554778462469784601029226775, 163⟩⟩,
  ⟨⟨-1010452671117915774457377437204554799928022624695, 164⟩, ⟨-78787214634851617911388576433736242784301107855, 163⟩⟩,
  ⟨⟨-157559729368861908039723180687854486149158823365, 164⟩, ⟨-2925575192559691901768821386146069734551796875, 164⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private theorem upper : upperOK (descentCoeffs 13) first gaps = true := by
  decide +kernel

private theorem lower : ∀ i : Fin (lastRepresentative 14 - 2),
    lowerOK (rows.getD i.val []) gaps = true := by
  decide +kernel

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 14) :
    StrictNegativeInterlacing (originalQuotient 14 k) (eulerian 13) 11 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N014
