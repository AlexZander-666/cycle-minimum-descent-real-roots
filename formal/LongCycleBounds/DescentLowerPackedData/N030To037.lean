import LongCycleBounds.DescentLowerPackedData.Alphabets127
import LongCycleBounds.DescentSweepChunkData.N030
import LongCycleBounds.DescentSweepChunkData.N031
import LongCycleBounds.DescentSweepChunkData.N032
import LongCycleBounds.DescentSweepChunkData.N033
import LongCycleBounds.DescentSweepChunkData.N034
import LongCycleBounds.DescentSweepChunkData.N035
import LongCycleBounds.DescentSweepChunkData.N036
import LongCycleBounds.DescentSweepChunkData.N037

/-! Original cutoffs one and two on the unchanged meshes at sizes 30 through 37. -/

namespace LongCycleBounds.DescentNecklace.LowerPacked
set_option maxRecDepth 65536
set_option maxHeartbeats 25000000
set_option Elab.async false

namespace N030

private def nodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentSweepChunkData.N030
    LongCycleBounds.DescentNecklace.SweepChunks.N030.nodes

private def rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentSweepChunkData.N030
    LongCycleBounds.DescentNecklace.SweepChunks.N030.rows

private theorem originalChecks : RepresentativeChecks 30 nodes rows := by
  let atAlphabet := descentFrozenConst LongCycleBounds.DescentSweepChunkData.N030
    LongCycleBounds.DescentNecklace.SweepChunks.N030.atAlphabet
  let swept := descentFrozenConst LongCycleBounds.DescentSweepChunkData.N030
    LongCycleBounds.DescentNecklace.SweepChunks.N030.swept
  let counts := descentFrozenConst LongCycleBounds.DescentSweepChunkData.N030
    LongCycleBounds.DescentNecklace.SweepChunks.N030.counts
  let signs := descentFrozenConst LongCycleBounds.DescentSweepChunkData.N030
    LongCycleBounds.DescentNecklace.SweepChunks.N030.signs
  exact representativeChecks_of_sweepChunks (n := 30) (by decide) nodes rows atAlphabet swept counts signs

private def codes (i : Fin 30) : ℕ → ℕ := Alphabets127.codes ⟨i.val, by omega⟩

private theorem checkedCodes (i : Fin 30) : PackedCutoffChecks 127 (i.val + 1) 1 (codes i) :=
  Alphabets127.checked ⟨i.val, by omega⟩

private def one : List ℤ :=
  [1, 1073741793, 205857846098570, 1146539378801856522, 895677742522620803739,
  192738102960442228634235, 16113937872564544537388100, 637869809663929594478505540,
  13531191345752030482167405705, 167000574396175833526330189545,
  1269070526794311849099687878550, 6179021140233742910738329979670,
  19821417273866560109781608911515, 42694138146309498709817320643835,
  62481596875767023932367207962680, 62481596875767023932367207962680,
  42694138146309498709817320643835, 19821417273866560109781608911515,
  6179021140233742910738329979670, 1269070526794311849099687878550,
  167000574396175833526330189545, 13531191345752030482167405705, 637869809663929594478505540,
  16113937872564544537388100, 192738102960442228634235, 895677742522620803739,
  1146539378801856522, 205857846098570, 1073741793, 1]

private def two : List ℤ :=
  [0, 268435456, 60996458380760, 362900546463220440, 293895608601699461464,
  64746113064450935222360, 5506613114288069536816152, 220927811990362983880815896,
  4738923421334613569311487128, 59048756998381015003621941144, 452539881995010926543564574520,
  2220412099306653431232744284216, 7173824053057667631015066686136,
  15556650044804692964414653640120, 22914844643767718841136166514808,
  23060333648288501934625878631800, 15856378806337303766705371842808,
  7408104885663479304097191651320, 2324266739501317639058967524616,
  480564728559443005044302128136, 63686849942797490982701731720, 5199698478314386446740319624,
  247195380125376589909340488, 6305219654256641273805896, 76287756525716460109512,
  359678706858023193560, 469544200231680376, 86845527576456, 477218568, 1]

private theorem oneCount : descentRowDP 30 1 = one := by
  rw [← cachedLowerNumerator_eq (bound := 127) (n := 30) (k := 1)
    (by decide) (by decide) (by decide) codes checkedCodes]
  decide +kernel

private theorem twoCount : descentRowDP 30 2 = two := by
  rw [← cachedLowerNumerator_eq (bound := 127) (n := 30) (k := 2)
    (by decide) (by decide) (by decide) codes checkedCodes]
  decide +kernel

private theorem oneSigns : rawMeshOK one nodes = true := by
  decide +kernel

private theorem twoSigns : rawMeshOK two nodes = true := by
  decide +kernel

theorem lower_cutoff_mesh : LowerCutoffMeshCertificate 30 := by
  refine ⟨nodes, rows, by decide, originalChecks, ?_⟩
  intro k hk
  rcases hk with rfl | rfl
  · exact rawSharedSigns_of_numerator (by decide) oneCount oneSigns
  · exact rawSharedSigns_of_numerator (by decide) twoCount twoSigns

#print axioms lower_cutoff_mesh
end N030

namespace N031

private def nodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentSweepChunkData.N031
    LongCycleBounds.DescentNecklace.SweepChunks.N031.nodes

private def rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentSweepChunkData.N031
    LongCycleBounds.DescentNecklace.SweepChunks.N031.rows

private theorem originalChecks : RepresentativeChecks 31 nodes rows := by
  let atAlphabet := descentFrozenConst LongCycleBounds.DescentSweepChunkData.N031
    LongCycleBounds.DescentNecklace.SweepChunks.N031.atAlphabet
  let swept := descentFrozenConst LongCycleBounds.DescentSweepChunkData.N031
    LongCycleBounds.DescentNecklace.SweepChunks.N031.swept
  let counts := descentFrozenConst LongCycleBounds.DescentSweepChunkData.N031
    LongCycleBounds.DescentNecklace.SweepChunks.N031.counts
  let signs := descentFrozenConst LongCycleBounds.DescentSweepChunkData.N031
    LongCycleBounds.DescentNecklace.SweepChunks.N031.signs
  exact representativeChecks_of_sweepChunks (n := 31) (by decide) nodes rows atAlphabet swept counts signs

private def codes (i : Fin 31) : ℕ → ℕ := Alphabets127.codes ⟨i.val, by omega⟩

private theorem checkedCodes (i : Fin 31) : PackedCutoffChecks 127 (i.val + 1) 1 (codes i) :=
  Alphabets127.checked ⟨i.val, by omega⟩

private def one : List ℤ :=
  [1, 2147483616, 617604676807707, 4591921534898186048, 4509345275840754144789,
  1179716239068241512702624, 117616017681962867477572575, 5489692986252985824725358720,
  136451727734038655012512278765, 1967691953568303005870984820960,
  17466787857057122844149500644495, 99529664218691151910853717327040,
  375079826224706396731189185463425, 954503444977931063913511449420960,
  1663024301623766837052402570385395, 1999411100024544765835750654805760,
  1663024301623766837052402570385395, 954503444977931063913511449420960,
  375079826224706396731189185463425, 99529664218691151910853717327040,
  17466787857057122844149500644495, 1967691953568303005870984820960,
  136451727734038655012512278765, 5489692986252985824725358720, 117616017681962867477572575,
  1179716239068241512702624, 4509345275840754144789, 4591921534898186048, 617604676807707,
  2147483616, 1]

private def two : List ℤ :=
  [0, 536870912, 182997159770504, 1453310086687543040, 1479276357763004259200,
  396117964210349797332224, 40164944626627760138272064, 1899581210665817539930114816,
  47731650467789870753062149760, 694743885253171648561072128256,
  6217962598911121507055271083744, 35695742831580059705664222900992,
  135447542576576094396618008319872, 346921933582303718860076351312128,
  608185720418195563012091609604160, 735602852672899532412192722345728,
  615463444432061693053379500804736, 355335191230664880207624655523072,
  140466431564150266095383874434864, 37502495445204671769593652858112,
  6623635862952620366124059775616, 751261865950891411655304348928,
  52482780047713139588577707840, 2128888312705172109846065408, 46043731492939400419379072,
  467078185532607363689632, 1811071227696371337952, 1880608475698862272, 260550422067840,
  954437166, 0]

private theorem oneCount : descentRowDP 31 1 = one := by
  rw [← cachedLowerNumerator_eq (bound := 127) (n := 31) (k := 1)
    (by decide) (by decide) (by decide) codes checkedCodes]
  decide +kernel

private theorem twoCount : descentRowDP 31 2 = two := by
  rw [← cachedLowerNumerator_eq (bound := 127) (n := 31) (k := 2)
    (by decide) (by decide) (by decide) codes checkedCodes]
  decide +kernel

private theorem oneSigns : rawMeshOK one nodes = true := by
  decide +kernel

private theorem twoSigns : rawMeshOK two nodes = true := by
  decide +kernel

theorem lower_cutoff_mesh : LowerCutoffMeshCertificate 31 := by
  refine ⟨nodes, rows, by decide, originalChecks, ?_⟩
  intro k hk
  rcases hk with rfl | rfl
  · exact rawSharedSigns_of_numerator (by decide) oneCount oneSigns
  · exact rawSharedSigns_of_numerator (by decide) twoCount twoSigns

#print axioms lower_cutoff_mesh
end N031

namespace N032

private def nodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentSweepChunkData.N032
    LongCycleBounds.DescentNecklace.SweepChunks.N032.nodes

private def rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentSweepChunkData.N032
    LongCycleBounds.DescentNecklace.SweepChunks.N032.rows

private theorem originalChecks : RepresentativeChecks 32 nodes rows := by
  let atAlphabet := descentFrozenConst LongCycleBounds.DescentSweepChunkData.N032
    LongCycleBounds.DescentNecklace.SweepChunks.N032.atAlphabet
  let swept := descentFrozenConst LongCycleBounds.DescentSweepChunkData.N032
    LongCycleBounds.DescentNecklace.SweepChunks.N032.swept
  let counts := descentFrozenConst LongCycleBounds.DescentSweepChunkData.N032
    LongCycleBounds.DescentNecklace.SweepChunks.N032.counts
  let signs := descentFrozenConst LongCycleBounds.DescentSweepChunkData.N032
    LongCycleBounds.DescentNecklace.SweepChunks.N032.signs
  exact representativeChecks_of_sweepChunks (n := 32) (by decide) nodes rows atAlphabet swept counts signs

private def codes (i : Fin 32) : ℕ → ℕ := Alphabets127.codes ⟨i.val, by omega⟩

private theorem checkedCodes (i : Fin 32) : PackedCutoffChecks 127 (i.val + 1) 1 (codes i) :=
  Alphabets127.checked ⟨i.val, by omega⟩

private def one : List ℤ :=
  [1, 4294967263, 1852878454931601, 18385596675220167695, 22675300182180919933289,
  7200049756857149438125047, 853984745989514351673276249, 46857944332072958284742184135,
  1359818181276419554906019118165, 22815309273565919123997630621195,
  235423889406131017414806173150565, 1561158515622493402657384121458875,
  6866631025295006195722533757565325, 20489564927960456432681754815698515,
  42126426533959261706229244645358205, 60261990727996752483262854173443875,
  60261990727996752483262854173443875, 42126426533959261706229244645358205,
  20489564927960456432681754815698515, 6866631025295006195722533757565325,
  1561158515622493402657384121458875, 235423889406131017414806173150565,
  22815309273565919123997630621195, 1359818181276419554906019118165,
  46857944332072958284742184135, 853984745989514351673276249, 7200049756857149438125047,
  22675300182180919933289, 18385596675220167695, 1852878454931601, 4294967263, 1]

private def two : List ℤ :=
  [0, 1073741824, 549007585438872, 5818547264383516776, 7437074471242272501120,
  2416648246921699898991744, 291453679455863415698542272, 16200773300992234322897720128,
  475174803266088457735882103424, 8045266813290883512931150727040,
  83681954063592112845951568742816, 558926128556094268116131367570528,
  2474732910127090421269318566178176, 7430410379107197857576811076447360,
  15367380610754400384662748467680704, 22108802889875717089800640920802368,
  22232524198111441300502535071212160, 15627985108632893239537936311486336,
  7643554876948163378719038791585424, 2576113519238046894631863424815472,
  589126298464461088923729089585280, 89387755543398435083781353208192,
  8719722600606316327090330769600, 523438339934342386933504940352,
  18182199788964861889253000064, 334450153274423594391583936, 2851368036343446208262496,
  9108013175801424833376, 7529989865035416448, 781679899318500, 1908874332, 1]

private theorem oneCount : descentRowDP 32 1 = one := by
  rw [← cachedLowerNumerator_eq (bound := 127) (n := 32) (k := 1)
    (by decide) (by decide) (by decide) codes checkedCodes]
  decide +kernel

private theorem twoCount : descentRowDP 32 2 = two := by
  rw [← cachedLowerNumerator_eq (bound := 127) (n := 32) (k := 2)
    (by decide) (by decide) (by decide) codes checkedCodes]
  decide +kernel

private theorem oneSigns : rawMeshOK one nodes = true := by
  decide +kernel

private theorem twoSigns : rawMeshOK two nodes = true := by
  decide +kernel

theorem lower_cutoff_mesh : LowerCutoffMeshCertificate 32 := by
  refine ⟨nodes, rows, by decide, originalChecks, ?_⟩
  intro k hk
  rcases hk with rfl | rfl
  · exact rawSharedSigns_of_numerator (by decide) oneCount oneSigns
  · exact rawSharedSigns_of_numerator (by decide) twoCount twoSigns

#print axioms lower_cutoff_mesh
end N032

namespace N033

private def nodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentSweepChunkData.N033
    LongCycleBounds.DescentNecklace.SweepChunks.N033.nodes

private def rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentSweepChunkData.N033
    LongCycleBounds.DescentNecklace.SweepChunks.N033.rows

private theorem originalChecks : RepresentativeChecks 33 nodes rows := by
  let atAlphabet := descentFrozenConst LongCycleBounds.DescentSweepChunkData.N033
    LongCycleBounds.DescentNecklace.SweepChunks.N033.atAlphabet
  let swept := descentFrozenConst LongCycleBounds.DescentSweepChunkData.N033
    LongCycleBounds.DescentNecklace.SweepChunks.N033.swept
  let counts := descentFrozenConst LongCycleBounds.DescentSweepChunkData.N033
    LongCycleBounds.DescentNecklace.SweepChunks.N033.counts
  let signs := descentFrozenConst LongCycleBounds.DescentSweepChunkData.N033
    LongCycleBounds.DescentNecklace.SweepChunks.N033.signs
  exact representativeChecks_of_sweepChunks (n := 33) (by decide) nodes rows atAlphabet swept counts signs

private def codes (i : Fin 33) : ℕ → ℕ := Alphabets127.codes ⟨i.val, by omega⟩

private theorem checkedCodes (i : Fin 33) : PackedCutoffChecks 127 (i.val + 1) 1 (codes i) :=
  Alphabets127.checked ⟨i.val, by omega⟩

private def one : List ℤ :=
  [1, 8589934558, 5558768508779956, 73597973054528618810, 113909683214485984529600,
  43835206946243962386882374, 6172294565361743496542310012, 397067158052311039421442655554,
  13409812239789599951272726666860, 260788729086293260557720765047910,
  3114414896759457331414813408943700, 23913227754404803215014345266818930,
  122050532156907442000198005398985600, 424186529497346513971995242571085710,
  1021198131640637597814392011178644860, 1722467529259214750444332070391549690,
  2048907684751889584430937041897091750, 1722467529259214750444332070391549690,
  1021198131640637597814392011178644860, 424186529497346513971995242571085710,
  122050532156907442000198005398985600, 23913227754404803215014345266818930,
  3114414896759457331414813408943700, 260788729086293260557720765047910,
  13409812239789599951272726666860, 397067158052311039421442655554,
  6172294565361743496542310012, 43835206946243962386882374, 113909683214485984529600,
  73597973054528618810, 5558768508779956, 8589934558, 1]

private def two : List ℤ :=
  [0, 2147483648, 1647056042313160, 23290659285097233264, 37354110226878484492104,
  14708127566724983023981824, 2105425258857929807162572992, 137183982073790323391343860096,
  4681592561919601977695381934016, 91856863411294958114972677752576,
  1105542631405203562102883722892896, 8548116532072157700004510923188288,
  43908976531330155106939900079297376, 153520403510042578431461726393826560,
  371688506364352765063900637467710400, 630353697231590680360739727151090560,
  753802560495781692635153991864246976, 637024119125175139119723414746148608,
  379647319291508502788730781712418096, 158532038662035225194703811578505376,
  45861128017848292497612535403892016, 9036046203528298638927938845603584,
  1183818930791328061444672492990912, 99759746164487380557307426264448,
  5165500054133203029632869464768, 154153302296853908568205182848, 2418138009902238208364174944,
  17363232586983117144909504, 45758435585093151243872, 30143409857121220792, 2345098873059792,
  3817748696, 0]

private theorem oneCount : descentRowDP 33 1 = one := by
  rw [← cachedLowerNumerator_eq (bound := 127) (n := 33) (k := 1)
    (by decide) (by decide) (by decide) codes checkedCodes]
  decide +kernel

private theorem twoCount : descentRowDP 33 2 = two := by
  rw [← cachedLowerNumerator_eq (bound := 127) (n := 33) (k := 2)
    (by decide) (by decide) (by decide) codes checkedCodes]
  decide +kernel

private theorem oneSigns : rawMeshOK one nodes = true := by
  decide +kernel

private theorem twoSigns : rawMeshOK two nodes = true := by
  decide +kernel

theorem lower_cutoff_mesh : LowerCutoffMeshCertificate 33 := by
  refine ⟨nodes, rows, by decide, originalChecks, ?_⟩
  intro k hk
  rcases hk with rfl | rfl
  · exact rawSharedSigns_of_numerator (by decide) oneCount oneSigns
  · exact rawSharedSigns_of_numerator (by decide) twoCount twoSigns

#print axioms lower_cutoff_mesh
end N033

namespace N034

private def nodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentSweepChunkData.N034
    LongCycleBounds.DescentNecklace.SweepChunks.N034.nodes

private def rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentSweepChunkData.N034
    LongCycleBounds.DescentNecklace.SweepChunks.N034.rows

private theorem originalChecks : RepresentativeChecks 34 nodes rows := by
  let atAlphabet := descentFrozenConst LongCycleBounds.DescentSweepChunkData.N034
    LongCycleBounds.DescentNecklace.SweepChunks.N034.atAlphabet
  let swept := descentFrozenConst LongCycleBounds.DescentSweepChunkData.N034
    LongCycleBounds.DescentNecklace.SweepChunks.N034.swept
  let counts := descentFrozenConst LongCycleBounds.DescentSweepChunkData.N034
    LongCycleBounds.DescentNecklace.SweepChunks.N034.counts
  let signs := descentFrozenConst LongCycleBounds.DescentSweepChunkData.N034
    LongCycleBounds.DescentNecklace.SweepChunks.N034.signs
  exact representativeChecks_of_sweepChunks (n := 34) (by decide) nodes rows atAlphabet swept counts signs

private def codes (i : Fin 34) : ℕ → ℕ := Alphabets127.codes ⟨i.val, by omega⟩

private theorem checkedCodes (i : Fin 34) : PackedCutoffChecks 127 (i.val + 1) 1 (codes i) :=
  Alphabets127.checked ⟨i.val, by omega⟩

private def one : List ℤ :=
  [1, 17179869149, 16676580404245724, 294564214041886653876, 571756355264065781212300,
  266314622490683867872652644, 44433447752027035422628876556, 3343189217683255389778183614756,
  131012056267466486586412049046144, 2943132596857672604359025817150600,
  40517493362425068898948245859530540, 358590275678325157202712851607532260,
  2112747928636702416732889666056829260, 8501672588257907477612091509373897540,
  23801702564556494246655785019101387100, 46962244969319550365582761338659047380,
  65835846167447988443323906979298454170, 65835846167447988443323906979298454170,
  46962244969319550365582761338659047380, 23801702564556494246655785019101387100,
  8501672588257907477612091509373897540, 2112747928636702416732889666056829260,
  358590275678325157202712851607532260, 40517493362425068898948245859530540,
  2943132596857672604359025817150600, 131012056267466486586412049046144,
  3343189217683255389778183614756, 44433447752027035422628876556, 266314622490683867872652644,
  571756355264065781212300, 294564214041886653876, 16676580404245724, 17179869149, 1]

private def two : List ℤ :=
  [0, 4294967296, 4941236846416216, 93213695877700641016, 187469270912945339458440,
  89332034596929374194161960, 15149804383873808174809502016, 1154318338579486691924140351552,
  45701116591194966207433377768640, 1035608448160939630592111325876160,
  14365533667328318177891065217883680, 128004878907185574328420456704796064,
  758875258612879485790317941341008224, 3071374156298529355286202071178816736,
  8645735665666143044587744089892187200, 17147740776628153421985947746303946560,
  24161010078596921021290932950411828672, 24281077672681441278952639327122873536,
  17405684972541463778901459488474321552, 8865350562613332045725037957256378960,
  3182532229643307295175716605580807600, 794987680709650372525377614853875056,
  135660389850540129080362733486033984, 15416242146652305809266775653246784,
  1126734962998203881313895999263680, 50497486346917028889469159936960,
  1298516144642191700171474186272, 17413136581751194738606690720, 105506390153866404255529312,
  229696480221179392843120, 120646337493549736720, 7035418787137648, 7635497392, 1]

private theorem oneCount : descentRowDP 34 1 = one := by
  rw [← cachedLowerNumerator_eq (bound := 127) (n := 34) (k := 1)
    (by decide) (by decide) (by decide) codes checkedCodes]
  decide +kernel

private theorem twoCount : descentRowDP 34 2 = two := by
  rw [← cachedLowerNumerator_eq (bound := 127) (n := 34) (k := 2)
    (by decide) (by decide) (by decide) codes checkedCodes]
  decide +kernel

private theorem oneSigns : rawMeshOK one nodes = true := by
  decide +kernel

private theorem twoSigns : rawMeshOK two nodes = true := by
  decide +kernel

theorem lower_cutoff_mesh : LowerCutoffMeshCertificate 34 := by
  refine ⟨nodes, rows, by decide, originalChecks, ?_⟩
  intro k hk
  rcases hk with rfl | rfl
  · exact rawSharedSigns_of_numerator (by decide) oneCount oneSigns
  · exact rawSharedSigns_of_numerator (by decide) twoCount twoSigns

#print axioms lower_cutoff_mesh
end N034

namespace N035

private def nodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentSweepChunkData.N035
    LongCycleBounds.DescentNecklace.SweepChunks.N035.nodes

private def rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentSweepChunkData.N035
    LongCycleBounds.DescentNecklace.SweepChunks.N035.rows

private theorem originalChecks : RepresentativeChecks 35 nodes rows := by
  let atAlphabet := descentFrozenConst LongCycleBounds.DescentSweepChunkData.N035
    LongCycleBounds.DescentNecklace.SweepChunks.N035.atAlphabet
  let swept := descentFrozenConst LongCycleBounds.DescentSweepChunkData.N035
    LongCycleBounds.DescentNecklace.SweepChunks.N035.swept
  let counts := descentFrozenConst LongCycleBounds.DescentSweepChunkData.N035
    LongCycleBounds.DescentNecklace.SweepChunks.N035.counts
  let signs := descentFrozenConst LongCycleBounds.DescentSweepChunkData.N035
    LongCycleBounds.DescentNecklace.SweepChunks.N035.signs
  exact representativeChecks_of_sweepChunks (n := 35) (by decide) nodes rows atAlphabet swept counts signs

private def codes (i : Fin 35) : ℕ → ℕ := Alphabets127.codes ⟨i.val, by omega⟩

private theorem checkedCodes (i : Fin 35) : PackedCutoffChecks 127 (i.val + 1) 1 (codes i) :=
  Alphabets127.checked ⟨i.val, by omega⟩

private def one : List ℤ :=
  [1, 34359738332, 50030308148419089, 1178790506740482478672, 2867913266955627392331656,
  1615040425602025180672284864, 318757258316419080126709062568,
  27989650278522800110059077461616, 1269374615284646274801719399013708,
  32837639431530854694836971446705744, 519270741908117572997406349883600940,
  5275503148838103540007312119919120080, 35713299412878610033189961245712022360,
  165503870665618157854692853784484809280, 535560662821763470729690696983372654840,
  1227429970800242690782439881800572500080, 2011492039263687260482578884082595621110,
  2370090462028127583959660651254744350120, 2011492039263687260482578884082595621110,
  1227429970800242690782439881800572500080, 535560662821763470729690696983372654840,
  165503870665618157854692853784484809280, 35713299412878610033189961245712022360,
  5275503148838103540007312119919120080, 519270741908117572997406349883600940,
  32837639431530854694836971446705744, 1269374615284646274801719399013708,
  27989650278522800110059077461616, 318757258316419080126709062568,
  1615040425602025180672284864, 2867913266955627392331656, 1178790506740482478672,
  50030308148419089, 34359738332, 1]

private def two : List ℤ :=
  [0, 8589934592, 14823852273169416, 373012903089887882976, 940235979136935417163696,
  541616285708964605348724960, 108639259690427609075297210952, 9658741231384360164287788868864,
  442476644462400836548852189409664, 11544313512980465427314381080746240,
  183911081544634990721604500543624480, 1880831354902106528210431045686761088,
  12809490576832701524827803741643416384, 59694493877662759661393823706005615232,
  194184892267261262129826404843137959456, 447278565739373315643530045738706888960,
  736544246092082572379678867336776072064, 871957579523010521404384300995624639744,
  743486334913872313541322598842100959600, 455797970812930061376924110960716724032,
  199813435261709433884565618076042644000, 62045180190618610328018340004916557632,
  13455028815787877811678251863279157360, 1997914489726136888386755417510330624,
  197747037688130460934781932167306624, 12580284275001881564265158150997760,
  489537313027592435909852242461984, 10875696981426567054052780830336,
  124951641386720488893657185088, 639929235329833807318469472, 1152222437568197006053920,
  482810483375387351616, 21106508332826880, 15270994818, 0]

private theorem oneCount : descentRowDP 35 1 = one := by
  rw [← cachedLowerNumerator_eq (bound := 127) (n := 35) (k := 1)
    (by decide) (by decide) (by decide) codes checkedCodes]
  decide +kernel

private theorem twoCount : descentRowDP 35 2 = two := by
  rw [← cachedLowerNumerator_eq (bound := 127) (n := 35) (k := 2)
    (by decide) (by decide) (by decide) codes checkedCodes]
  decide +kernel

private theorem oneSigns : rawMeshOK one nodes = true := by
  decide +kernel

private theorem twoSigns : rawMeshOK two nodes = true := by
  decide +kernel

theorem lower_cutoff_mesh : LowerCutoffMeshCertificate 35 := by
  refine ⟨nodes, rows, by decide, originalChecks, ?_⟩
  intro k hk
  rcases hk with rfl | rfl
  · exact rawSharedSigns_of_numerator (by decide) oneCount oneSigns
  · exact rawSharedSigns_of_numerator (by decide) twoCount twoSigns

#print axioms lower_cutoff_mesh
end N035

namespace N036

private def nodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentSweepChunkData.N036
    LongCycleBounds.DescentNecklace.SweepChunks.N036.nodes

private def rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentSweepChunkData.N036
    LongCycleBounds.DescentNecklace.SweepChunks.N036.rows

private theorem originalChecks : RepresentativeChecks 36 nodes rows := by
  let atAlphabet := descentFrozenConst LongCycleBounds.DescentSweepChunkData.N036
    LongCycleBounds.DescentNecklace.SweepChunks.N036.atAlphabet
  let swept := descentFrozenConst LongCycleBounds.DescentSweepChunkData.N036
    LongCycleBounds.DescentNecklace.SweepChunks.N036.swept
  let counts := descentFrozenConst LongCycleBounds.DescentSweepChunkData.N036
    LongCycleBounds.DescentNecklace.SweepChunks.N036.counts
  let signs := descentFrozenConst LongCycleBounds.DescentSweepChunkData.N036
    LongCycleBounds.DescentNecklace.SweepChunks.N036.signs
  exact representativeChecks_of_sweepChunks (n := 36) (by decide) nodes rows atAlphabet swept counts signs

private def codes (i : Fin 36) : ℕ → ℕ := Alphabets127.codes ⟨i.val, by omega⟩

private theorem checkedCodes (i : Fin 36) : PackedCutoffChecks 127 (i.val + 1) 1 (codes i) :=
  Alphabets127.checked ⟨i.val, by omega⟩

private def one : List ℤ :=
  [1, 68719476699, 150092092676360555, 4716813027130827744625, 14377287630993832400975784,
  9779147864887775533195990520, 2279752020982994316307131983896,
  233161162719358554204147182507400, 12208081745360454876297128760048620,
  362649508927993996368016138240427556, 6565756786209095525037231106333959684,
  76287806333760181805022904186119464460, 590884967939536415391644987072315172600,
  3138460075814862240729069061634163844200, 11674495096970051533748603238009255626760,
  30885653452060915937842542745459985752920, 58743964083487537243852638665415575560470,
  80879977062516354460442890520154715103250, 80879977062516354460442890520154715103250,
  58743964083487537243852638665415575560470, 30885653452060915937842542745459985752920,
  11674495096970051533748603238009255626760, 3138460075814862240729069061634163844200,
  590884967939536415391644987072315172600, 76287806333760181805022904186119464460,
  6565756786209095525037231106333959684, 362649508927993996368016138240427556,
  12208081745360454876297128760048620, 233161162719358554204147182507400,
  2279752020982994316307131983896, 9779147864887775533195990520, 14377287630993832400975784,
  4716813027130827744625, 150092092676360555, 68719476699, 1]

private def two : List ℤ :=
  [0, 17179869184, 44471848877284376, 1492540799484566122632, 4713116308583553498073712,
  3278845029607032630024424336, 776723306404262201687542225464,
  80420468382097281977485930068520, 4252734554640369613539727793015168,
  127390004530289476859962819921523328, 2323174048328476999047823414079271520,
  27167753297441153106565285061831745056, 211663330016475676499811793737846679104,
  1130341197554430770330553017941877190080, 4226052249317499644498060194179192926944,
  11234339789442459555022835233525207371936, 21466823498352870043325141659499331004288,
  29689577107163758260492815897319988884608, 29821476794777763342564046795921161747792,
  21755227109794430557740966399530050793840, 11488849673502779093606663754968363108512,
  4362195493119250935484887751248803927904, 1178098185431781734260856552924252426128,
  222865322358669696873099404242876980656, 28918649818916904184010613314306633088,
  2502304805719483990953495365766314624, 139020350201763811412217592056451168,
  4710355332728275800702148045407264, 90629173451627430610338305010240,
  893859366766938436475154379776, 3875294307543616951098488352, 5776562123308997425521312,
  1931938448276532693504, 63320044212304452, 30541989636, 1]

private theorem oneCount : descentRowDP 36 1 = one := by
  rw [← cachedLowerNumerator_eq (bound := 127) (n := 36) (k := 1)
    (by decide) (by decide) (by decide) codes checkedCodes]
  decide +kernel

private theorem twoCount : descentRowDP 36 2 = two := by
  rw [← cachedLowerNumerator_eq (bound := 127) (n := 36) (k := 2)
    (by decide) (by decide) (by decide) codes checkedCodes]
  decide +kernel

private theorem oneSigns : rawMeshOK one nodes = true := by
  decide +kernel

private theorem twoSigns : rawMeshOK two nodes = true := by
  decide +kernel

theorem lower_cutoff_mesh : LowerCutoffMeshCertificate 36 := by
  refine ⟨nodes, rows, by decide, originalChecks, ?_⟩
  intro k hk
  rcases hk with rfl | rfl
  · exact rawSharedSigns_of_numerator (by decide) oneCount oneSigns
  · exact rawSharedSigns_of_numerator (by decide) twoCount twoSigns

#print axioms lower_cutoff_mesh
end N036

namespace N037

private def nodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentSweepChunkData.N037
    LongCycleBounds.DescentNecklace.SweepChunks.N037.nodes

private def rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentSweepChunkData.N037
    LongCycleBounds.DescentNecklace.SweepChunks.N037.rows

private theorem originalChecks : RepresentativeChecks 37 nodes rows := by
  let atAlphabet := descentFrozenConst LongCycleBounds.DescentSweepChunkData.N037
    LongCycleBounds.DescentNecklace.SweepChunks.N037.atAlphabet
  let swept := descentFrozenConst LongCycleBounds.DescentSweepChunkData.N037
    LongCycleBounds.DescentNecklace.SweepChunks.N037.swept
  let counts := descentFrozenConst LongCycleBounds.DescentSweepChunkData.N037
    LongCycleBounds.DescentNecklace.SweepChunks.N037.counts
  let signs := descentFrozenConst LongCycleBounds.DescentSweepChunkData.N037
    LongCycleBounds.DescentNecklace.SweepChunks.N037.signs
  exact representativeChecks_of_sweepChunks (n := 37) (by decide) nodes rows atAlphabet swept counts signs

private def codes (i : Fin 37) : ℕ → ℕ := Alphabets127.codes ⟨i.val, by omega⟩

private theorem checkedCodes (i : Fin 37) : PackedCutoffChecks 127 (i.val + 1) 1 (codes i) :=
  Alphabets127.checked ⟨i.val, by omega⟩

private def one : List ℤ :=
  [1, 137438953434, 450278683210766130, 18872355239674307237370, 72042092984864479320451545,
  59134960393518455836007168208, 16261417730692481255678999593392,
  1933681862384358263122391419576080, 116634409427105491958594427133152180,
  3968321378150032700216480987685636920, 82014861389355888677345977902165100536,
  1086163352446558665311242858998116525304, 9588699741557977945216957436593083855300,
  58119680291956945339606446552613857961200, 247302008198292604542997636987724602818000,
  751009347366315788747949955163563395835440, 1647246111912567367840188254966724485339310,
  2630718868795045125165024802671096383067900, 3073439128375621469496829839765879173923500,
  2630718868795045125165024802671096383067900, 1647246111912567367840188254966724485339310,
  751009347366315788747949955163563395835440, 247302008198292604542997636987724602818000,
  58119680291956945339606446552613857961200, 9588699741557977945216957436593083855300,
  1086163352446558665311242858998116525304, 82014861389355888677345977902165100536,
  3968321378150032700216480987685636920, 116634409427105491958594427133152180,
  1933681862384358263122391419576080, 16261417730692481255678999593392,
  59134960393518455836007168208, 72042092984864479320451545, 18872355239674307237370,
  450278683210766130, 137438953434, 1]

private def two : List ℤ :=
  [0, 34359738368, 133416147927274568, 5971675240800092159312, 23614835389300758172415416,
  19823889899516869492084904800, 5538707340747653423343552732664,
  666665446248906121870513707312080, 40606804574844147699204642109123592,
  1392976612832825117778740577419657984, 28994444653931062864745053692753116576,
  386415564825834239254026829508042000192, 3430817122650212622161685445137800454752,
  20904696686157447020623225300894600959616, 89388631283514402385073622325351069276000,
  272722586116064345059322688008345562343744, 600857135050290441392006948115517981883552,
  963748857896005049555373519341746420008704, 1130710024136888910458080391171581862015600,
  971891124501888351320972170317181927337056, 611104704010063680447336367646346488774032,
  279789895624667986078374150606967496150080, 92529190661719743920273016985989864719504,
  21842142332653017004606377442768581501536, 3620215436135628663950557588015066575728,
  412083722775709433972918239281603777280, 31278902318361946808618324008953642400,
  1522093451334029836541836065835915072, 45021444024651677694019143253962336,
  751849168616027597976961071475200, 6377149690902421180810133797344,
  23436615833207589624207612096, 28946564585338112706492192, 7729906674609349125384,
  189961201606550616, 61083979308, 0]

private theorem oneCount : descentRowDP 37 1 = one := by
  rw [← cachedLowerNumerator_eq (bound := 127) (n := 37) (k := 1)
    (by decide) (by decide) (by decide) codes checkedCodes]
  decide +kernel

private theorem twoCount : descentRowDP 37 2 = two := by
  rw [← cachedLowerNumerator_eq (bound := 127) (n := 37) (k := 2)
    (by decide) (by decide) (by decide) codes checkedCodes]
  decide +kernel

private theorem oneSigns : rawMeshOK one nodes = true := by
  decide +kernel

private theorem twoSigns : rawMeshOK two nodes = true := by
  decide +kernel

theorem lower_cutoff_mesh : LowerCutoffMeshCertificate 37 := by
  refine ⟨nodes, rows, by decide, originalChecks, ?_⟩
  intro k hk
  rcases hk with rfl | rfl
  · exact rawSharedSigns_of_numerator (by decide) oneCount oneSigns
  · exact rawSharedSigns_of_numerator (by decide) twoCount twoSigns

#print axioms lower_cutoff_mesh
end N037

end LongCycleBounds.DescentNecklace.LowerPacked
