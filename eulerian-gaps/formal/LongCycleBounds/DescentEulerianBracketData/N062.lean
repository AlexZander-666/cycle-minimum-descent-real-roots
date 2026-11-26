import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentPackedData.C127L064.N062

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N062

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L064.N062 LongCycleBounds.DescentNecklace.Packed.C127L064.N062.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L064.N062 LongCycleBounds.DescentNecklace.Packed.C127L064.N062.rows

private theorem actual : RepresentativeChecks 62 previousNodes rows :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L064.N062 LongCycleBounds.DescentNecklace.Packed.C127L064.N062.dataChecks

private def first : LongCycleFinite.Dyadic := ⟨-2305843009213693952, 0⟩

private def gaps : List Window := [
  ⟨⟨-2305768242423005184, 0⟩, ⟨-55121412096, 0⟩⟩,
  ⟨⟨-55054172160, 0⟩, ⟨-42007168, 0⟩⟩,
  ⟨⟨-39766784, 0⟩, ⟨-757792, 0⟩⟩,
  ⟨⟨-755946, 0⟩, ⟨-469217, 3⟩⟩,
  ⟨⟨-58618, 0⟩, ⟨-313947, 5⟩⟩,
  ⟨⟨-78467, 3⟩, ⟨-20833, 3⟩⟩,
  ⟨⟨-333279, 7⟩, ⟨-477249, 9⟩⟩,
  ⟨⟨-477203, 9⟩, ⟨-419051, 10⟩⟩,
  ⟨⟨-419021, 10⟩, ⟨-425679, 11⟩⟩,
  ⟨⟨-53207, 8⟩, ⟨-240737, 11⟩⟩,
  ⟨⟨-481453, 12⟩, ⟨-295393, 12⟩⟩,
  ⟨⟨-147691, 11⟩, ⟨-386073, 13⟩⟩,
  ⟨⟨-386061, 13⟩, ⟨-66297, 11⟩⟩,
  ⟨⟨-66295, 11⟩, ⟨-379141, 14⟩⟩,
  ⟨⟨-379131, 14⟩, ⟨-139979, 13⟩⟩,
  ⟨⟨-279951, 14⟩, ⟨-106145, 13⟩⟩,
  ⟨⟨-424571, 15⟩, ⟨-164553, 14⟩⟩,
  ⟨⟨-329099, 15⟩, ⟨-519617, 16⟩⟩,
  ⟨⟨-64951, 13⟩, ⟨-416529, 16⟩⟩,
  ⟨⟨-416523, 16⟩, ⟨-338203, 16⟩⟩,
  ⟨⟨-169099, 15⟩, ⟨-277571, 16⟩⟩,
  ⟨⟨-138783, 15⟩, ⟨-229869, 16⟩⟩,
  ⟨⟨-459731, 17⟩, ⟨-383595, 17⟩⟩,
  ⟨⟨-191795, 16⟩, ⟨-322041, 17⟩⟩,
  ⟨⟨-322037, 17⟩, ⟨-271721, 17⟩⟩,
  ⟨⟨-271717, 17⟩, ⟨-57543, 15⟩⟩,
  ⟨⟨-460339, 18⟩, ⟨-391119, 18⟩⟩,
  ⟨⟨-195557, 17⟩, ⟨-41625, 15⟩⟩,
  ⟨⟨-332995, 18⟩, ⟨-283869, 18⟩⟩,
  ⟨⟨-283865, 18⟩, ⟨-484169, 19⟩⟩,
  ⟨⟨-484163, 19⟩, ⟨-412735, 19⟩⟩,
  ⟨⟨-206365, 18⟩, ⟨-351405, 19⟩⟩,
  ⟨⟨-351401, 19⟩, ⟨-298563, 19⟩⟩,
  ⟨⟨-298559, 19⟩, ⟨-63227, 17⟩⟩,
  ⟨⟨-252905, 19⟩, ⟨-213391, 19⟩⟩,
  ⟨⟨-53347, 17⟩, ⟨-358299, 20⟩⟩,
  ⟨⟨-179147, 19⟩, ⟨-298953, 20⟩⟩,
  ⟨⟨-298949, 20⟩, ⟨-495155, 21⟩⟩,
  ⟨⟨-123787, 19⟩, ⟨-203195, 20⟩⟩,
  ⟨⟨-25399, 17⟩, ⟨-329967, 21⟩⟩,
  ⟨⟨-329961, 21⟩, ⟨-33063, 18⟩⟩,
  ⟨⟨-264499, 21⟩, ⟨-208811, 21⟩⟩,
  ⟨⟨-417615, 22⟩, ⟨-80929, 20⟩⟩,
  ⟨⟨-161855, 21⟩, ⟨-490937, 23⟩⟩,
  ⟨⟨-30683, 19⟩, ⟨-181255, 22⟩⟩,
  ⟨⟨-181251, 22⟩, ⟨-518289, 24⟩⟩,
  ⟨⟨-518277, 24⟩, ⟨-356003, 24⟩⟩,
  ⟨⟨-177997, 23⟩, ⟨-58161, 22⟩⟩,
  ⟨⟨-465275, 25⟩, ⟨-285469, 25⟩⟩,
  ⟨⟨-71365, 23⟩, ⟨-40361, 23⟩⟩,
  ⟨⟨-80719, 24⟩, ⟨-327991, 27⟩⟩,
  ⟨⟨-163989, 26⟩, ⟨-288005, 28⟩⟩,
  ⟨⟨-35999, 25⟩, ⟨-412343, 30⟩⟩,
  ⟨⟨-412321, 30⟩, ⟨-437885, 32⟩⟩,
  ⟨⟨-218929, 31⟩, ⟨-292937, 34⟩⟩,
  ⟨⟨-73229, 32⟩, ⟨-362765, 38⟩⟩,
  ⟨⟨-362737, 38⟩, ⟨-429011, 44⟩⟩,
  ⟨⟨-428975, 44⟩, ⟨-326901, 54⟩⟩,
  ⟨⟨-163435, 53⟩, ⟨-262149, 79⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private theorem upper : upperOK (descentCoeffs 61) first gaps = true := by
  decide +kernel

private theorem lower : ∀ i : Fin (lastRepresentative 62 - 2),
    lowerOK (rows.getD i.val []) gaps = true := by
  decide +kernel

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 62) :
    StrictNegativeInterlacing (originalQuotient 62 k) (eulerian 61) 59 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N062
