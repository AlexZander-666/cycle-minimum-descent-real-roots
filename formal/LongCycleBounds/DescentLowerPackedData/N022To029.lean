import LongCycleBounds.DescentLowerPackedData.Alphabets127
import LongCycleBounds.DescentSweepData.N022
import LongCycleBounds.DescentSweepData.N023
import LongCycleBounds.DescentSweepData.N024
import LongCycleBounds.DescentSweepData.N025
import LongCycleBounds.DescentSweepData.N026
import LongCycleBounds.DescentSweepData.N027
import LongCycleBounds.DescentSweepData.N028
import LongCycleBounds.DescentSweepChunkData.N029

/-! Original cutoffs one and two on the unchanged meshes at sizes 22 through 29. -/

namespace LongCycleBounds.DescentNecklace.LowerPacked
set_option maxRecDepth 65536
set_option maxHeartbeats 25000000
set_option Elab.async false

namespace N022

private def nodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentSweepData.N022
    LongCycleBounds.DescentNecklace.Sweep.N022.nodes

private def rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentSweepData.N022
    LongCycleBounds.DescentNecklace.Sweep.N022.rows

private theorem originalChecks : RepresentativeChecks 22 nodes rows := by
  let counts := descentFrozenConst LongCycleBounds.DescentSweepData.N022
    LongCycleBounds.DescentNecklace.Sweep.N022.counts
  let signs := descentFrozenConst LongCycleBounds.DescentSweepData.N022
    LongCycleBounds.DescentNecklace.Sweep.N022.signs
  exact representativeChecks_of_shared (n := 22) (by decide) nodes rows counts signs

private def codes (i : Fin 22) : ℕ → ℕ := Alphabets127.codes ⟨i.val, by omega⟩

private theorem checkedCodes (i : Fin 22) : PackedCutoffChecks 127 (i.val + 1) 1 (codes i) :=
  Alphabets127.checked ⟨i.val, by omega⟩

private def one : List ℤ :=
  [1, 4194281, 31284590870, 16871482830550, 1987497491971605, 81180715002105741,
  1454842842001939656, 13093713503185076040, 64276307695970022450, 181134082346647020610,
  301958232385734088196, 301958232385734088196, 181134082346647020610, 64276307695970022450,
  13093713503185076040, 1454842842001939656, 81180715002105741, 1987497491971605,
  16871482830550, 31284590870, 4194281, 1]

private def two : List ℤ :=
  [0, 1048576, 9273974488, 5352686795416, 655576175021944, 27502902905426872,
  503057677516936168, 4604138187328622888, 22931200638124847240, 65467873291379045192,
  110464702295866844144, 111748307882825828720, 67799005781035890992, 24336058536997584048,
  5016885257300362704, 564604235488737360, 31959306812206608, 795764467047840, 6901736685000,
  13196009560, 1864120, 1]

private theorem oneCount : descentRowDP 22 1 = one := by
  rw [← cachedLowerNumerator_eq (bound := 127) (n := 22) (k := 1)
    (by decide) (by decide) (by decide) codes checkedCodes]
  decide +kernel

private theorem twoCount : descentRowDP 22 2 = two := by
  rw [← cachedLowerNumerator_eq (bound := 127) (n := 22) (k := 2)
    (by decide) (by decide) (by decide) codes checkedCodes]
  decide +kernel

private theorem oneSigns : rawMeshOK one nodes = true := by
  decide +kernel

private theorem twoSigns : rawMeshOK two nodes = true := by
  decide +kernel

theorem lower_cutoff_mesh : LowerCutoffMeshCertificate 22 := by
  refine ⟨nodes, rows, by decide, originalChecks, ?_⟩
  intro k hk
  rcases hk with rfl | rfl
  · exact rawSharedSigns_of_numerator (by decide) oneCount oneSigns
  · exact rawSharedSigns_of_numerator (by decide) twoCount twoSigns

#print axioms lower_cutoff_mesh
end N022

namespace N023

private def nodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentSweepData.N023
    LongCycleBounds.DescentNecklace.Sweep.N023.nodes

private def rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentSweepData.N023
    LongCycleBounds.DescentNecklace.Sweep.N023.rows

private theorem originalChecks : RepresentativeChecks 23 nodes rows := by
  let counts := descentFrozenConst LongCycleBounds.DescentSweepData.N023
    LongCycleBounds.DescentNecklace.Sweep.N023.counts
  let signs := descentFrozenConst LongCycleBounds.DescentSweepData.N023
    LongCycleBounds.DescentNecklace.Sweep.N023.signs
  exact representativeChecks_of_shared (n := 23) (by decide) nodes rows counts signs

private def codes (i : Fin 23) : ℕ → ℕ := Alphabets127.codes ⟨i.val, by omega⟩

private theorem checkedCodes (i : Fin 23) : PackedCutoffChecks 127 (i.val + 1) 1 (codes i) :=
  Alphabets127.checked ⟨i.val, by omega⟩

private def one : List ℤ :=
  [1, 8388584, 93941852511, 68111623139600, 10258045633638475, 522859244868123336,
  11563972049049375189, 128027193497511642816, 774892471811506342650, 2711209131210050520400,
  5676283626749486238086, 7246997577257618116704, 5676283626749486238086,
  2711209131210050520400, 774892471811506342650, 128027193497511642816, 11563972049049375189,
  522859244868123336, 10258045633638475, 68111623139600, 93941852511, 8388584, 1]

private def two : List ℤ :=
  [0, 2097152, 27843943560, 21596226671424, 3379581924222624, 176817788582956224,
  3988953092010810000, 44882028338899961792, 275442878553052968480, 975715541847538313280,
  2066194078042462873080, 2666556122144312074368, 2110618461864550698816,
  1018694877328325086592, 294277805692483696992, 49168749826222699392, 4495537864228673856,
  206079601280100768, 4109955332254200, 27870866931200, 39627175200, 3728262, 0]

private theorem oneCount : descentRowDP 23 1 = one := by
  rw [← cachedLowerNumerator_eq (bound := 127) (n := 23) (k := 1)
    (by decide) (by decide) (by decide) codes checkedCodes]
  decide +kernel

private theorem twoCount : descentRowDP 23 2 = two := by
  rw [← cachedLowerNumerator_eq (bound := 127) (n := 23) (k := 2)
    (by decide) (by decide) (by decide) codes checkedCodes]
  decide +kernel

private theorem oneSigns : rawMeshOK one nodes = true := by
  decide +kernel

private theorem twoSigns : rawMeshOK two nodes = true := by
  decide +kernel

theorem lower_cutoff_mesh : LowerCutoffMeshCertificate 23 := by
  refine ⟨nodes, rows, by decide, originalChecks, ?_⟩
  intro k hk
  rcases hk with rfl | rfl
  · exact rawSharedSigns_of_numerator (by decide) oneCount oneSigns
  · exact rawSharedSigns_of_numerator (by decide) twoCount twoSigns

#print axioms lower_cutoff_mesh
end N023

namespace N024

private def nodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentSweepData.N024
    LongCycleBounds.DescentNecklace.Sweep.N024.nodes

private def rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentSweepData.N024
    LongCycleBounds.DescentNecklace.Sweep.N024.rows

private theorem originalChecks : RepresentativeChecks 24 nodes rows := by
  let counts := descentFrozenConst LongCycleBounds.DescentSweepData.N024
    LongCycleBounds.DescentNecklace.Sweep.N024.counts
  let signs := descentFrozenConst LongCycleBounds.DescentSweepData.N024
    LongCycleBounds.DescentNecklace.Sweep.N024.signs
  exact representativeChecks_of_shared (n := 24) (by decide) nodes rows counts signs

private def codes (i : Fin 24) : ℕ → ℕ := Alphabets127.codes ⟨i.val, by omega⟩

private theorem checkedCodes (i : Fin 24) : PackedCutoffChecks 127 (i.val + 1) 1 (codes i) :=
  Alphabets127.checked ⟨i.val, by omega⟩

private def one : List ℤ :=
  [1, 16777191, 282010106381, 274419271461131, 52652460630984375, 3332058336247871041,
  90359270750971846371, 1220805072813932520741, 9022467342263743368906, 38735478389273100343750,
  100396047731185055904546, 160755658074834738495566, 160755658074834738495566,
  100396047731185055904546, 38735478389273100343750, 9022467342263743368906,
  1220805072813932520741, 90359270750971846371, 3332058336247871041, 52652460630984375,
  274419271461131, 282010106381, 16777191, 1]

private def two : List ℤ :=
  [0, 4194304, 83577968024, 86969629500456, 17329834154541600, 1125118788057967200,
  31105391838568882032, 426868429275383464336, 3197098360399876104992, 13888798596771177660000,
  36388152444332627989800, 58859196480283762242456, 59436713469970903977024,
  37478531363106608899264, 14601115858670506320800, 3435200248451916463200,
  469774142301669050688, 35178197872642530816, 1314566758993434408, 21107193999895000,
  112315638404000, 118963547364, 7456524, 1]

private theorem oneCount : descentRowDP 24 1 = one := by
  rw [← cachedLowerNumerator_eq (bound := 127) (n := 24) (k := 1)
    (by decide) (by decide) (by decide) codes checkedCodes]
  decide +kernel

private theorem twoCount : descentRowDP 24 2 = two := by
  rw [← cachedLowerNumerator_eq (bound := 127) (n := 24) (k := 2)
    (by decide) (by decide) (by decide) codes checkedCodes]
  decide +kernel

private theorem oneSigns : rawMeshOK one nodes = true := by
  decide +kernel

private theorem twoSigns : rawMeshOK two nodes = true := by
  decide +kernel

theorem lower_cutoff_mesh : LowerCutoffMeshCertificate 24 := by
  refine ⟨nodes, rows, by decide, originalChecks, ?_⟩
  intro k hk
  rcases hk with rfl | rfl
  · exact rawSharedSigns_of_numerator (by decide) oneCount oneSigns
  · exact rawSharedSigns_of_numerator (by decide) twoCount twoSigns

#print axioms lower_cutoff_mesh
end N024

namespace N025

private def nodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentSweepData.N025
    LongCycleBounds.DescentNecklace.Sweep.N025.nodes

private def rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentSweepData.N025
    LongCycleBounds.DescentNecklace.Sweep.N025.rows

private theorem originalChecks : RepresentativeChecks 25 nodes rows := by
  let counts := descentFrozenConst LongCycleBounds.DescentSweepData.N025
    LongCycleBounds.DescentNecklace.Sweep.N025.counts
  let signs := descentFrozenConst LongCycleBounds.DescentSweepData.N025
    LongCycleBounds.DescentNecklace.Sweep.N025.signs
  exact representativeChecks_of_shared (n := 25) (by decide) nodes rows counts signs

private def codes (i : Fin 25) : ℕ → ℕ := Alphabets127.codes ⟨i.val, by omega⟩

private theorem checkedCodes (i : Fin 25) : PackedCutoffChecks 127 (i.val + 1) 1 (codes i) :=
  Alphabets127.checked ⟨i.val, by omega⟩

private def one : List ℤ :=
  [1, 33554406, 846416194536, 1103881308184906, 269025107855605626, 21045399230106913746,
  695824003645512474376, 11392907456028953400606, 101955892318210543172751,
  531714261368950897339996, 1685388700882132120106256, 3334612565134607644610436,
  4179647109945703200884716, 3334612565134607644610436, 1685388700882132120106256,
  531714261368950897339996, 101955892318210543172751, 11392907456028953400606,
  695824003645512474376, 21045399230106913746, 269025107855605626, 1103881308184906,
  846416194536, 33554406, 1]

private def two : List ℤ :=
  [0, 8388608, 250830373064, 349717233298352, 88475532992217576, 7097309411438635200,
  239114999843083551024, 3974844487297307591264, 36030648541280403838640,
  190041559734109794279872, 608601655839226572787800, 1215744491984061938766672,
  1537846829353310660853240, 1237940000723143372313984, 631280582874230292703904,
  200974362561935726619200, 38902962655195622030496, 4391400700120917960192,
  271224153529372969464, 8309544433958506448, 107894598405959000, 451879751658008, 357062142144,
  14913072, 0]

private theorem oneCount : descentRowDP 25 1 = one := by
  rw [← cachedLowerNumerator_eq (bound := 127) (n := 25) (k := 1)
    (by decide) (by decide) (by decide) codes checkedCodes]
  decide +kernel

private theorem twoCount : descentRowDP 25 2 = two := by
  rw [← cachedLowerNumerator_eq (bound := 127) (n := 25) (k := 2)
    (by decide) (by decide) (by decide) codes checkedCodes]
  decide +kernel

private theorem oneSigns : rawMeshOK one nodes = true := by
  decide +kernel

private theorem twoSigns : rawMeshOK two nodes = true := by
  decide +kernel

theorem lower_cutoff_mesh : LowerCutoffMeshCertificate 25 := by
  refine ⟨nodes, rows, by decide, originalChecks, ?_⟩
  intro k hk
  rcases hk with rfl | rfl
  · exact rawSharedSigns_of_numerator (by decide) oneCount oneSigns
  · exact rawSharedSigns_of_numerator (by decide) twoCount twoSigns

#print axioms lower_cutoff_mesh
end N025

namespace N026

private def nodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentSweepData.N026
    LongCycleBounds.DescentNecklace.Sweep.N026.nodes

private def rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentSweepData.N026
    LongCycleBounds.DescentNecklace.Sweep.N026.rows

private theorem originalChecks : RepresentativeChecks 26 nodes rows := by
  let counts := descentFrozenConst LongCycleBounds.DescentSweepData.N026
    LongCycleBounds.DescentNecklace.Sweep.N026.counts
  let signs := descentFrozenConst LongCycleBounds.DescentSweepData.N026
    LongCycleBounds.DescentNecklace.Sweep.N026.signs
  exact representativeChecks_of_shared (n := 26) (by decide) nodes rows counts signs

private def codes (i : Fin 26) : ℕ → ℕ := Alphabets127.codes ⟨i.val, by omega⟩

private theorem checkedCodes (i : Fin 26) : PackedCutoffChecks 127 (i.val + 1) 1 (codes i) :=
  Alphabets127.checked ⟨i.val, by omega⟩

private def one : List ℤ :=
  [1, 67108837, 2540053889352, 4434992805213952, 1369410928058096062, 131921922645609200622,
  5291676010120725595552, 104363915717496364217992, 1122675365072416049765667,
  7050392783099088207336727, 27046703891606667678608752, 65296181294847273536919072,
  101019988341178648636047412, 101019988341178648636047412, 65296181294847273536919072,
  27046703891606667678608752, 7050392783099088207336727, 1122675365072416049765667,
  104363915717496364217992, 5291676010120725595552, 131921922645609200622, 1369410928058096062,
  4434992805213952, 2540053889352, 67108837, 1]

private def two : List ℤ :=
  [0, 16777216, 752692445784, 1404638031773880, 450071444093651624, 44441842661468380296,
  1815751187130357561168, 36341940895397048199568, 395823037642875171190512,
  2512936622542864808055600, 9735283169977249009143752, 23717958741397141857017064,
  37012431669369905733825528, 37323168791717045803487896, 24324488751791174858326368,
  10159676212607504845650144, 2671093990757682840710432, 429171876498937121557920,
  40284464518025430101352, 2064759963384780915208, 52123053170276177688, 549414346566271176,
  1815731435901344, 1071544340160, 29826144, 1]

private theorem oneCount : descentRowDP 26 1 = one := by
  rw [← cachedLowerNumerator_eq (bound := 127) (n := 26) (k := 1)
    (by decide) (by decide) (by decide) codes checkedCodes]
  decide +kernel

private theorem twoCount : descentRowDP 26 2 = two := by
  rw [← cachedLowerNumerator_eq (bound := 127) (n := 26) (k := 2)
    (by decide) (by decide) (by decide) codes checkedCodes]
  decide +kernel

private theorem oneSigns : rawMeshOK one nodes = true := by
  decide +kernel

private theorem twoSigns : rawMeshOK two nodes = true := by
  decide +kernel

theorem lower_cutoff_mesh : LowerCutoffMeshCertificate 26 := by
  refine ⟨nodes, rows, by decide, originalChecks, ?_⟩
  intro k hk
  rcases hk with rfl | rfl
  · exact rawSharedSigns_of_numerator (by decide) oneCount oneSigns
  · exact rawSharedSigns_of_numerator (by decide) twoCount twoSigns

#print axioms lower_cutoff_mesh
end N026

namespace N027

private def nodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentSweepData.N027
    LongCycleBounds.DescentNecklace.Sweep.N027.nodes

private def rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentSweepData.N027
    LongCycleBounds.DescentNecklace.Sweep.N027.rows

private theorem originalChecks : RepresentativeChecks 27 nodes rows := by
  let counts := descentFrozenConst LongCycleBounds.DescentSweepData.N027
    LongCycleBounds.DescentNecklace.Sweep.N027.counts
  let signs := descentFrozenConst LongCycleBounds.DescentSweepData.N027
    LongCycleBounds.DescentNecklace.Sweep.N027.signs
  exact representativeChecks_of_shared (n := 27) (by decide) nodes rows counts signs

private def codes (i : Fin 27) : ℕ → ℕ := Alphabets127.codes ⟨i.val, by omega⟩

private theorem checkedCodes (i : Fin 27) : PackedCutoffChecks 127 (i.val + 1) 1 (codes i) :=
  Alphabets127.checked ⟨i.val, by omega⟩

private def one : List ℤ :=
  [1, 134217700, 7621839388981, 17800932514200256, 6949059474810401206, 821658576290933317096,
  39812092446402872381926, 940744845942385425654976, 12086992684284175368032851,
  90712084402294370969149276, 417370420120357843989420631, 1216301437803873965300768896,
  2292702567858031535322402436, 2828559673553002161809327536, 2292702567858031535322402436,
  1216301437803873965300768896, 417370420120357843989420631, 90712084402294370969149276,
  12086992684284175368032851, 940744845942385425654976, 39812092446402872381926,
  821658576290933317096, 6949059474810401206, 17800932514200256, 7621839388981, 134217700, 1]

private def two : List ℤ :=
  [0, 33554432, 2258496767752, 5636616745794336, 2282663895199057360, 276552627738870617504,
  13643537005803338914392, 327050550905783536819904, 4252904215798420456506400,
  32254180903000401161985216, 149808037452978440837526472, 440380035616401686430504800,
  836930992822765902394987824, 1040698406455217321522387936, 850068525569189218320238168,
  454448684423214175830318720, 157165036181563161594228928, 34436033684557696595146880,
  4627951714332917265946968, 363570915411899059114976, 15547903860269266137904,
  324825434646115032000, 2788833555857086792, 7288642807769216, 3215378674080, 59652314, 0]

private theorem oneCount : descentRowDP 27 1 = one := by
  rw [← cachedLowerNumerator_eq (bound := 127) (n := 27) (k := 1)
    (by decide) (by decide) (by decide) codes checkedCodes]
  decide +kernel

private theorem twoCount : descentRowDP 27 2 = two := by
  rw [← cachedLowerNumerator_eq (bound := 127) (n := 27) (k := 2)
    (by decide) (by decide) (by decide) codes checkedCodes]
  decide +kernel

private theorem oneSigns : rawMeshOK one nodes = true := by
  decide +kernel

private theorem twoSigns : rawMeshOK two nodes = true := by
  decide +kernel

theorem lower_cutoff_mesh : LowerCutoffMeshCertificate 27 := by
  refine ⟨nodes, rows, by decide, originalChecks, ?_⟩
  intro k hk
  rcases hk with rfl | rfl
  · exact rawSharedSigns_of_numerator (by decide) oneCount oneSigns
  · exact rawSharedSigns_of_numerator (by decide) twoCount twoSigns

#print axioms lower_cutoff_mesh
end N027

namespace N028

private def nodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentSweepData.N028
    LongCycleBounds.DescentNecklace.Sweep.N028.nodes

private def rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentSweepData.N028
    LongCycleBounds.DescentNecklace.Sweep.N028.rows

private theorem originalChecks : RepresentativeChecks 28 nodes rows := by
  let counts := descentFrozenConst LongCycleBounds.DescentSweepData.N028
    LongCycleBounds.DescentNecklace.Sweep.N028.counts
  let signs := descentFrozenConst LongCycleBounds.DescentSweepData.N028
    LongCycleBounds.DescentNecklace.Sweep.N028.signs
  exact representativeChecks_of_shared (n := 28) (by decide) nodes rows counts signs

private def codes (i : Fin 28) : ℕ → ℕ := Alphabets127.codes ⟨i.val, by omega⟩

private theorem checkedCodes (i : Fin 28) : PackedCutoffChecks 127 (i.val + 1) 1 (codes i) :=
  Alphabets127.checked ⟨i.val, by omega⟩

private def one : List ℤ :=
  [1, 268435427, 22869007827143, 71394276041525549, 35172519754392812174,
  5089779825666239130314, 296761135803220639649594, 8362012708913543725260254,
  127597831077405286825395179, 1136773705024343041684116929, 6223892140565234961328313909,
  21690914395692570931429377479, 49265956387016393404003534004, 73990373947612503295166622044,
  73990373947612503295166622044, 49265956387016393404003534004, 21690914395692570931429377479,
  6223892140565234961328313909, 1136773705024343041684116929, 127597831077405286825395179,
  8362012708913543725260254, 296761135803220639649594, 5089779825666239130314,
  35172519754392812174, 71394276041525549, 22869007827143, 268435427, 1]

private def two : List ℤ :=
  [0, 67108864, 6776362718488, 22602929402371144, 11548598277894350864, 1711817036022802024304,
  101588916850878525985832, 2902918684368138411761464, 44817148960301454844955680,
  403346989130174000293473760, 2228463668236770070128525080, 7831297064097453731404007624,
  17926183476558383714022918512, 27123742582714531037238248464, 27320805573910880776117003624,
  18322069783170886651448195704, 8125189828165143857065716416, 2348664004319233316249162048,
  432291419417902394004461192, 48922983737234236575822232, 3235073304360847061815792,
  115981486584099393669328, 2013095779661403188216, 14119095206671895144, 29234955697928864,
  9647686982404, 119304628, 1]

private theorem oneCount : descentRowDP 28 1 = one := by
  rw [← cachedLowerNumerator_eq (bound := 127) (n := 28) (k := 1)
    (by decide) (by decide) (by decide) codes checkedCodes]
  decide +kernel

private theorem twoCount : descentRowDP 28 2 = two := by
  rw [← cachedLowerNumerator_eq (bound := 127) (n := 28) (k := 2)
    (by decide) (by decide) (by decide) codes checkedCodes]
  decide +kernel

private theorem oneSigns : rawMeshOK one nodes = true := by
  decide +kernel

private theorem twoSigns : rawMeshOK two nodes = true := by
  decide +kernel

theorem lower_cutoff_mesh : LowerCutoffMeshCertificate 28 := by
  refine ⟨nodes, rows, by decide, originalChecks, ?_⟩
  intro k hk
  rcases hk with rfl | rfl
  · exact rawSharedSigns_of_numerator (by decide) oneCount oneSigns
  · exact rawSharedSigns_of_numerator (by decide) twoCount twoSigns

#print axioms lower_cutoff_mesh
end N028

namespace N029

private def nodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentSweepChunkData.N029
    LongCycleBounds.DescentNecklace.SweepChunks.N029.nodes

private def rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentSweepChunkData.N029
    LongCycleBounds.DescentNecklace.SweepChunks.N029.rows

private theorem originalChecks : RepresentativeChecks 29 nodes rows := by
  let atAlphabet := descentFrozenConst LongCycleBounds.DescentSweepChunkData.N029
    LongCycleBounds.DescentNecklace.SweepChunks.N029.atAlphabet
  let swept := descentFrozenConst LongCycleBounds.DescentSweepChunkData.N029
    LongCycleBounds.DescentNecklace.SweepChunks.N029.swept
  let counts := descentFrozenConst LongCycleBounds.DescentSweepChunkData.N029
    LongCycleBounds.DescentNecklace.SweepChunks.N029.counts
  let signs := descentFrozenConst LongCycleBounds.DescentSweepChunkData.N029
    LongCycleBounds.DescentNecklace.SweepChunks.N029.signs
  exact representativeChecks_of_sweepChunks (n := 29) (by decide) nodes rows atAlphabet swept counts signs

private def codes (i : Fin 29) : ℕ → ℕ := Alphabets127.codes ⟨i.val, by omega⟩

private theorem checkedCodes (i : Fin 29) : PackedCutoffChecks 127 (i.val + 1) 1 (codes i) :=
  Alphabets127.checked ⟨i.val, by omega⟩

private def one : List ℤ :=
  [1, 536870882, 68614271237958, 286171698369607914, 177647455673002199595,
  31382819428102862274060, 2194392886612867977544380, 73424846658979203874373100,
  1323982746583831999659021945, 13919693671791536153349072870, 90061513941680102366609674650,
  372321031278485080481062180110, 1009202977757986820086345359195,
  1824120537458837340596389252680, 2219711218428375098854998661320,
  1824120537458837340596389252680, 1009202977757986820086345359195,
  372321031278485080481062180110, 90061513941680102366609674650, 13919693671791536153349072870,
  1323982746583831999659021945, 73424846658979203874373100, 2194392886612867977544380,
  31382819428102862274060, 177647455673002199595, 286171698369607914, 68614271237958, 536870882,
  1]

private def two : List ℤ :=
  [0, 134217728, 20330900094792, 90587903040165264, 58308064624531032920,
  10548068574806276566560, 750494209784674128459816, 25458305645664434865780016,
  464315633014444000251591864, 4929812870507769099833851200, 32176693144077776776989777320,
  134087910797431306039161542928, 366172435284915701716166070264,
  666551331782937573945702174688, 816668222349381177200328781320,
  675644394565486517288809182000, 376315134260028972038943723224,
  139778230015727925977273513856, 34048841016451711964825545176, 5301373868923708671561056560,
  508243393026685917480531720, 28432179139736963155251552, 858171609020908029014264,
  12417432962928544612752, 71326349925807697320, 117190662653257960, 28946282172168, 238609284,
  0]

private theorem oneCount : descentRowDP 29 1 = one := by
  rw [← cachedLowerNumerator_eq (bound := 127) (n := 29) (k := 1)
    (by decide) (by decide) (by decide) codes checkedCodes]
  decide +kernel

private theorem twoCount : descentRowDP 29 2 = two := by
  rw [← cachedLowerNumerator_eq (bound := 127) (n := 29) (k := 2)
    (by decide) (by decide) (by decide) codes checkedCodes]
  decide +kernel

private theorem oneSigns : rawMeshOK one nodes = true := by
  decide +kernel

private theorem twoSigns : rawMeshOK two nodes = true := by
  decide +kernel

theorem lower_cutoff_mesh : LowerCutoffMeshCertificate 29 := by
  refine ⟨nodes, rows, by decide, originalChecks, ?_⟩
  intro k hk
  rcases hk with rfl | rfl
  · exact rawSharedSigns_of_numerator (by decide) oneCount oneSigns
  · exact rawSharedSigns_of_numerator (by decide) twoCount twoSigns

#print axioms lower_cutoff_mesh
end N029

end LongCycleBounds.DescentNecklace.LowerPacked
