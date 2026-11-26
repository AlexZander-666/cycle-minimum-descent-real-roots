import LongCycleBounds.DescentPackedData.C127Q001
import LongCycleBounds.DescentPackedData.C127Q002
import LongCycleBounds.DescentPackedData.C127Q003
import LongCycleBounds.DescentPackedData.C127Q004
import LongCycleBounds.DescentPackedData.C127Q005
import LongCycleBounds.DescentPackedData.C127Q006
import LongCycleBounds.DescentPackedData.C127Q007
import LongCycleBounds.DescentPackedData.C127Q008
import LongCycleBounds.DescentPackedData.C127Q009
import LongCycleBounds.DescentPackedData.C127Q010
import LongCycleBounds.DescentPackedData.C127Q011
import LongCycleBounds.DescentPackedData.C127Q012
import LongCycleBounds.DescentPackedData.C127Q013
import LongCycleBounds.DescentPackedData.C127Q014
import LongCycleBounds.DescentPackedData.C127Q015
import LongCycleBounds.DescentPackedData.C127Q016
import LongCycleBounds.DescentPackedData.C127Q017
import LongCycleBounds.DescentPackedData.C127Q018
import LongCycleBounds.DescentPackedData.C127Q019
import LongCycleBounds.DescentPackedData.C127Q020
import LongCycleBounds.DescentPackedData.C127Q021
import LongCycleBounds.DescentPackedData.C127Q022
import LongCycleBounds.DescentPackedData.C127Q023
import LongCycleBounds.DescentPackedData.C127Q024
import LongCycleBounds.DescentPackedData.C127Q025
import LongCycleBounds.DescentPackedData.C127Q026
import LongCycleBounds.DescentPackedData.C127Q027
import LongCycleBounds.DescentPackedData.C127Q028
import LongCycleBounds.DescentPackedData.C127Q029
import LongCycleBounds.DescentPackedData.C127Q030
import LongCycleBounds.DescentPackedData.C127Q031
import LongCycleBounds.DescentPackedData.C127Q032
import LongCycleBounds.DescentPackedData.C127Q033
import LongCycleBounds.DescentPackedData.C127Q034
import LongCycleBounds.DescentPackedData.C127Q035
import LongCycleBounds.DescentPackedData.C127Q036
import LongCycleBounds.DescentPackedData.C127Q037
import LongCycleBounds.DescentPackedData.C127Q038
import LongCycleBounds.DescentPackedData.C127Q039
import LongCycleBounds.DescentPackedData.C127Q040
import LongCycleBounds.DescentPackedData.C127Q041
import LongCycleBounds.DescentPackedData.C127Q042
import LongCycleBounds.DescentPackedData.C127Q043
import LongCycleBounds.DescentPackedData.C127Q044
import LongCycleBounds.DescentPackedData.C127Q045
import LongCycleBounds.DescentPackedData.C127Q046
import LongCycleBounds.DescentPackedData.C127Q047
import LongCycleBounds.DescentPackedData.C127Q048
import LongCycleBounds.DescentPackedData.C127Q049
import LongCycleBounds.DescentPackedData.C127Q050
import LongCycleBounds.DescentPackedData.C127Q051
import LongCycleBounds.DescentPackedData.C127Q052
import LongCycleBounds.DescentPackedData.C127Q053
import LongCycleBounds.DescentPackedData.C127Q054
import LongCycleBounds.DescentPackedData.C127Q055
import LongCycleBounds.DescentPackedData.C127Q056
import LongCycleBounds.DescentPackedData.C127Q057
import LongCycleBounds.DescentPackedData.C127Q058
import LongCycleBounds.DescentPackedData.C127Q059
import LongCycleBounds.DescentPackedData.C127Q060
import LongCycleBounds.DescentPackedData.C127Q061
import LongCycleBounds.DescentPackedData.C127Q062
import LongCycleBounds.DescentPackedData.C127Q063
import LongCycleBounds.DescentPackedData.C127Q064
import LongCycleBounds.DescentPackedData.C127Q065
import LongCycleBounds.DescentPackedData.C127Q066
import LongCycleBounds.DescentPackedData.C127Q067
import LongCycleBounds.DescentPackedData.C127Q068
import LongCycleBounds.DescentPackedData.C127Q069
import LongCycleBounds.DescentPackedData.C127Q070
import LongCycleBounds.DescentPackedData.C127Q071
import LongCycleBounds.DescentPackedData.C127Q072

/-! A verified array of the first 72 alphabets, all at degree cap 127. -/

namespace LongCycleBounds.DescentNecklace.Packed.C127L072

private structure Entry where
  letters : ℕ
  code : ℕ → ℕ
  accepted : PackedCutoffChecks 127 letters 3 code

private def table : Array Entry := #[
  ⟨1, C127Q001.code, C127Q001.checked⟩,
  ⟨2, C127Q002.code, C127Q002.checked⟩,
  ⟨3, C127Q003.code, C127Q003.checked⟩,
  ⟨4, C127Q004.code, C127Q004.checked⟩,
  ⟨5, C127Q005.code, C127Q005.checked⟩,
  ⟨6, C127Q006.code, C127Q006.checked⟩,
  ⟨7, C127Q007.code, C127Q007.checked⟩,
  ⟨8, C127Q008.code, C127Q008.checked⟩,
  ⟨9, C127Q009.code, C127Q009.checked⟩,
  ⟨10, C127Q010.code, C127Q010.checked⟩,
  ⟨11, C127Q011.code, C127Q011.checked⟩,
  ⟨12, C127Q012.code, C127Q012.checked⟩,
  ⟨13, C127Q013.code, C127Q013.checked⟩,
  ⟨14, C127Q014.code, C127Q014.checked⟩,
  ⟨15, C127Q015.code, C127Q015.checked⟩,
  ⟨16, C127Q016.code, C127Q016.checked⟩,
  ⟨17, C127Q017.code, C127Q017.checked⟩,
  ⟨18, C127Q018.code, C127Q018.checked⟩,
  ⟨19, C127Q019.code, C127Q019.checked⟩,
  ⟨20, C127Q020.code, C127Q020.checked⟩,
  ⟨21, C127Q021.code, C127Q021.checked⟩,
  ⟨22, C127Q022.code, C127Q022.checked⟩,
  ⟨23, C127Q023.code, C127Q023.checked⟩,
  ⟨24, C127Q024.code, C127Q024.checked⟩,
  ⟨25, C127Q025.code, C127Q025.checked⟩,
  ⟨26, C127Q026.code, C127Q026.checked⟩,
  ⟨27, C127Q027.code, C127Q027.checked⟩,
  ⟨28, C127Q028.code, C127Q028.checked⟩,
  ⟨29, C127Q029.code, C127Q029.checked⟩,
  ⟨30, C127Q030.code, C127Q030.checked⟩,
  ⟨31, C127Q031.code, C127Q031.checked⟩,
  ⟨32, C127Q032.code, C127Q032.checked⟩,
  ⟨33, C127Q033.code, C127Q033.checked⟩,
  ⟨34, C127Q034.code, C127Q034.checked⟩,
  ⟨35, C127Q035.code, C127Q035.checked⟩,
  ⟨36, C127Q036.code, C127Q036.checked⟩,
  ⟨37, C127Q037.code, C127Q037.checked⟩,
  ⟨38, C127Q038.code, C127Q038.checked⟩,
  ⟨39, C127Q039.code, C127Q039.checked⟩,
  ⟨40, C127Q040.code, C127Q040.checked⟩,
  ⟨41, C127Q041.code, C127Q041.checked⟩,
  ⟨42, C127Q042.code, C127Q042.checked⟩,
  ⟨43, C127Q043.code, C127Q043.checked⟩,
  ⟨44, C127Q044.code, C127Q044.checked⟩,
  ⟨45, C127Q045.code, C127Q045.checked⟩,
  ⟨46, C127Q046.code, C127Q046.checked⟩,
  ⟨47, C127Q047.code, C127Q047.checked⟩,
  ⟨48, C127Q048.code, C127Q048.checked⟩,
  ⟨49, C127Q049.code, C127Q049.checked⟩,
  ⟨50, C127Q050.code, C127Q050.checked⟩,
  ⟨51, C127Q051.code, C127Q051.checked⟩,
  ⟨52, C127Q052.code, C127Q052.checked⟩,
  ⟨53, C127Q053.code, C127Q053.checked⟩,
  ⟨54, C127Q054.code, C127Q054.checked⟩,
  ⟨55, C127Q055.code, C127Q055.checked⟩,
  ⟨56, C127Q056.code, C127Q056.checked⟩,
  ⟨57, C127Q057.code, C127Q057.checked⟩,
  ⟨58, C127Q058.code, C127Q058.checked⟩,
  ⟨59, C127Q059.code, C127Q059.checked⟩,
  ⟨60, C127Q060.code, C127Q060.checked⟩,
  ⟨61, C127Q061.code, C127Q061.checked⟩,
  ⟨62, C127Q062.code, C127Q062.checked⟩,
  ⟨63, C127Q063.code, C127Q063.checked⟩,
  ⟨64, C127Q064.code, C127Q064.checked⟩,
  ⟨65, C127Q065.code, C127Q065.checked⟩,
  ⟨66, C127Q066.code, C127Q066.checked⟩,
  ⟨67, C127Q067.code, C127Q067.checked⟩,
  ⟨68, C127Q068.code, C127Q068.checked⟩,
  ⟨69, C127Q069.code, C127Q069.checked⟩,
  ⟨70, C127Q070.code, C127Q070.checked⟩,
  ⟨71, C127Q071.code, C127Q071.checked⟩,
  ⟨72, C127Q072.code, C127Q072.checked⟩
]

private def entry (i : Fin 72) : Entry :=
  table.getD i.val ⟨1, C127Q001.code, C127Q001.checked⟩

def codes (i : Fin 72) : ℕ → ℕ := (entry i).code

set_option maxRecDepth 32768 in
private theorem sizeIndex : ∀ i : Fin 72, (entry i).letters = i.val + 1 := by
  decide +kernel

theorem checked (i : Fin 72) : PackedCutoffChecks 127 (i.val + 1) 3 (codes i) :=
  sizeIndex i ▸ (entry i).accepted

#print axioms sizeIndex
#print axioms checked

end LongCycleBounds.DescentNecklace.Packed.C127L072
