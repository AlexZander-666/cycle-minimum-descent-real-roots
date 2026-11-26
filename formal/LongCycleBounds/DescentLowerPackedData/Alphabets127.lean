import LongCycleBounds.DescentLowerPackedData.Q001To008
import LongCycleBounds.DescentLowerPackedData.Q009To016
import LongCycleBounds.DescentLowerPackedData.Q017To024
import LongCycleBounds.DescentLowerPackedData.Q025To032
import LongCycleBounds.DescentLowerPackedData.Q033To040
import LongCycleBounds.DescentLowerPackedData.Q041To048
import LongCycleBounds.DescentLowerPackedData.Q049To056
import LongCycleBounds.DescentLowerPackedData.Q057To064
import LongCycleBounds.DescentLowerPackedData.Q065To072
import LongCycleBounds.DescentLowerPackedData.Q073To080
import LongCycleBounds.DescentLowerPackedData.Q081To088
import LongCycleBounds.DescentLowerPackedData.Q089To096
import LongCycleBounds.DescentLowerPackedData.Q097To104
import LongCycleBounds.DescentLowerPackedData.Q105To112
import LongCycleBounds.DescentLowerPackedData.Q113To120
import LongCycleBounds.DescentLowerPackedData.Q121To127

/-! The independently checked low-cutoff states for every required alphabet. -/

namespace LongCycleBounds.DescentNecklace.LowerPacked.Alphabets127

private structure Entry where
  alphabet : ℕ
  code : ℕ → ℕ
  verified : PackedCutoffChecks 127 alphabet 1 code

private def table : Array Entry := #[
  ⟨1, Q001.code, Q001.checked⟩,
  ⟨2, Q002.code, Q002.checked⟩,
  ⟨3, Q003.code, Q003.checked⟩,
  ⟨4, Q004.code, Q004.checked⟩,
  ⟨5, Q005.code, Q005.checked⟩,
  ⟨6, Q006.code, Q006.checked⟩,
  ⟨7, Q007.code, Q007.checked⟩,
  ⟨8, Q008.code, Q008.checked⟩,
  ⟨9, Q009.code, Q009.checked⟩,
  ⟨10, Q010.code, Q010.checked⟩,
  ⟨11, Q011.code, Q011.checked⟩,
  ⟨12, Q012.code, Q012.checked⟩,
  ⟨13, Q013.code, Q013.checked⟩,
  ⟨14, Q014.code, Q014.checked⟩,
  ⟨15, Q015.code, Q015.checked⟩,
  ⟨16, Q016.code, Q016.checked⟩,
  ⟨17, Q017.code, Q017.checked⟩,
  ⟨18, Q018.code, Q018.checked⟩,
  ⟨19, Q019.code, Q019.checked⟩,
  ⟨20, Q020.code, Q020.checked⟩,
  ⟨21, Q021.code, Q021.checked⟩,
  ⟨22, Q022.code, Q022.checked⟩,
  ⟨23, Q023.code, Q023.checked⟩,
  ⟨24, Q024.code, Q024.checked⟩,
  ⟨25, Q025.code, Q025.checked⟩,
  ⟨26, Q026.code, Q026.checked⟩,
  ⟨27, Q027.code, Q027.checked⟩,
  ⟨28, Q028.code, Q028.checked⟩,
  ⟨29, Q029.code, Q029.checked⟩,
  ⟨30, Q030.code, Q030.checked⟩,
  ⟨31, Q031.code, Q031.checked⟩,
  ⟨32, Q032.code, Q032.checked⟩,
  ⟨33, Q033.code, Q033.checked⟩,
  ⟨34, Q034.code, Q034.checked⟩,
  ⟨35, Q035.code, Q035.checked⟩,
  ⟨36, Q036.code, Q036.checked⟩,
  ⟨37, Q037.code, Q037.checked⟩,
  ⟨38, Q038.code, Q038.checked⟩,
  ⟨39, Q039.code, Q039.checked⟩,
  ⟨40, Q040.code, Q040.checked⟩,
  ⟨41, Q041.code, Q041.checked⟩,
  ⟨42, Q042.code, Q042.checked⟩,
  ⟨43, Q043.code, Q043.checked⟩,
  ⟨44, Q044.code, Q044.checked⟩,
  ⟨45, Q045.code, Q045.checked⟩,
  ⟨46, Q046.code, Q046.checked⟩,
  ⟨47, Q047.code, Q047.checked⟩,
  ⟨48, Q048.code, Q048.checked⟩,
  ⟨49, Q049.code, Q049.checked⟩,
  ⟨50, Q050.code, Q050.checked⟩,
  ⟨51, Q051.code, Q051.checked⟩,
  ⟨52, Q052.code, Q052.checked⟩,
  ⟨53, Q053.code, Q053.checked⟩,
  ⟨54, Q054.code, Q054.checked⟩,
  ⟨55, Q055.code, Q055.checked⟩,
  ⟨56, Q056.code, Q056.checked⟩,
  ⟨57, Q057.code, Q057.checked⟩,
  ⟨58, Q058.code, Q058.checked⟩,
  ⟨59, Q059.code, Q059.checked⟩,
  ⟨60, Q060.code, Q060.checked⟩,
  ⟨61, Q061.code, Q061.checked⟩,
  ⟨62, Q062.code, Q062.checked⟩,
  ⟨63, Q063.code, Q063.checked⟩,
  ⟨64, Q064.code, Q064.checked⟩,
  ⟨65, Q065.code, Q065.checked⟩,
  ⟨66, Q066.code, Q066.checked⟩,
  ⟨67, Q067.code, Q067.checked⟩,
  ⟨68, Q068.code, Q068.checked⟩,
  ⟨69, Q069.code, Q069.checked⟩,
  ⟨70, Q070.code, Q070.checked⟩,
  ⟨71, Q071.code, Q071.checked⟩,
  ⟨72, Q072.code, Q072.checked⟩,
  ⟨73, Q073.code, Q073.checked⟩,
  ⟨74, Q074.code, Q074.checked⟩,
  ⟨75, Q075.code, Q075.checked⟩,
  ⟨76, Q076.code, Q076.checked⟩,
  ⟨77, Q077.code, Q077.checked⟩,
  ⟨78, Q078.code, Q078.checked⟩,
  ⟨79, Q079.code, Q079.checked⟩,
  ⟨80, Q080.code, Q080.checked⟩,
  ⟨81, Q081.code, Q081.checked⟩,
  ⟨82, Q082.code, Q082.checked⟩,
  ⟨83, Q083.code, Q083.checked⟩,
  ⟨84, Q084.code, Q084.checked⟩,
  ⟨85, Q085.code, Q085.checked⟩,
  ⟨86, Q086.code, Q086.checked⟩,
  ⟨87, Q087.code, Q087.checked⟩,
  ⟨88, Q088.code, Q088.checked⟩,
  ⟨89, Q089.code, Q089.checked⟩,
  ⟨90, Q090.code, Q090.checked⟩,
  ⟨91, Q091.code, Q091.checked⟩,
  ⟨92, Q092.code, Q092.checked⟩,
  ⟨93, Q093.code, Q093.checked⟩,
  ⟨94, Q094.code, Q094.checked⟩,
  ⟨95, Q095.code, Q095.checked⟩,
  ⟨96, Q096.code, Q096.checked⟩,
  ⟨97, Q097.code, Q097.checked⟩,
  ⟨98, Q098.code, Q098.checked⟩,
  ⟨99, Q099.code, Q099.checked⟩,
  ⟨100, Q100.code, Q100.checked⟩,
  ⟨101, Q101.code, Q101.checked⟩,
  ⟨102, Q102.code, Q102.checked⟩,
  ⟨103, Q103.code, Q103.checked⟩,
  ⟨104, Q104.code, Q104.checked⟩,
  ⟨105, Q105.code, Q105.checked⟩,
  ⟨106, Q106.code, Q106.checked⟩,
  ⟨107, Q107.code, Q107.checked⟩,
  ⟨108, Q108.code, Q108.checked⟩,
  ⟨109, Q109.code, Q109.checked⟩,
  ⟨110, Q110.code, Q110.checked⟩,
  ⟨111, Q111.code, Q111.checked⟩,
  ⟨112, Q112.code, Q112.checked⟩,
  ⟨113, Q113.code, Q113.checked⟩,
  ⟨114, Q114.code, Q114.checked⟩,
  ⟨115, Q115.code, Q115.checked⟩,
  ⟨116, Q116.code, Q116.checked⟩,
  ⟨117, Q117.code, Q117.checked⟩,
  ⟨118, Q118.code, Q118.checked⟩,
  ⟨119, Q119.code, Q119.checked⟩,
  ⟨120, Q120.code, Q120.checked⟩,
  ⟨121, Q121.code, Q121.checked⟩,
  ⟨122, Q122.code, Q122.checked⟩,
  ⟨123, Q123.code, Q123.checked⟩,
  ⟨124, Q124.code, Q124.checked⟩,
  ⟨125, Q125.code, Q125.checked⟩,
  ⟨126, Q126.code, Q126.checked⟩,
  ⟨127, Q127.code, Q127.checked⟩
]

private def entry (i : Fin 127) : Entry := table.getD i.val ⟨1, Q001.code, Q001.checked⟩

def codes (i : Fin 127) : ℕ → ℕ := (entry i).code

set_option maxRecDepth 32768 in
private theorem index_verified : ∀ i : Fin 127, (entry i).alphabet = i.val + 1 := by
  decide +kernel

theorem checked (i : Fin 127) : PackedCutoffChecks 127 (i.val + 1) 1 (codes i) :=
  index_verified i ▸ (entry i).verified

#print axioms checked
end LongCycleBounds.DescentNecklace.LowerPacked.Alphabets127
