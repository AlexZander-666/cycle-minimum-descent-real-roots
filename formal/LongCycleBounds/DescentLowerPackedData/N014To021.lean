import LongCycleBounds.DescentLowerPackedData.Alphabets127
import LongCycleBounds.DescentFiniteData.N014
import LongCycleBounds.DescentFiniteData.N015
import LongCycleBounds.DescentFiniteData.N016
import LongCycleBounds.DescentSweepData.N017
import LongCycleBounds.DescentSweepData.N018
import LongCycleBounds.DescentSweepData.N019
import LongCycleBounds.DescentSweepData.N020
import LongCycleBounds.DescentSweepData.N021

/-! Original cutoffs one and two on the unchanged meshes at sizes 14 through 21. -/

namespace LongCycleBounds.DescentNecklace.LowerPacked
set_option maxRecDepth 65536
set_option maxHeartbeats 25000000
set_option Elab.async false

namespace N014

private def nodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentFiniteData.N014
    LongCycleBounds.DescentNecklace.N014.nodes

private def rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentFiniteData.N014
    LongCycleBounds.DescentNecklace.N014.rows

private theorem originalChecks : RepresentativeChecks 14 nodes rows := 
  descentFrozenConst LongCycleBounds.DescentFiniteData.N014
    LongCycleBounds.DescentNecklace.N014.checks

private def codes (i : Fin 14) : ℕ → ℕ := Alphabets127.codes ⟨i.val, by omega⟩

private theorem checkedCodes (i : Fin 14) : PackedCutoffChecks 127 (i.val + 1) 1 (codes i) :=
  Alphabets127.checked ⟨i.val, by omega⟩

private def one : List ℤ :=
  [1, 16369, 4537314, 198410786, 2571742175, 12843262863, 27971176092, 27971176092, 12843262863,
  2571742175, 198410786, 4537314, 16369, 1]

private def two : List ℤ :=
  [0, 4096, 1355736, 64107096, 872919960, 4522914840, 10156209720, 10438521016, 4920547704,
  1012156680, 80448280, 1908648, 7272, 1]

private theorem oneCount : descentRowDP 14 1 = one := by
  rw [← cachedLowerNumerator_eq (bound := 127) (n := 14) (k := 1)
    (by decide) (by decide) (by decide) codes checkedCodes]
  decide +kernel

private theorem twoCount : descentRowDP 14 2 = two := by
  rw [← cachedLowerNumerator_eq (bound := 127) (n := 14) (k := 2)
    (by decide) (by decide) (by decide) codes checkedCodes]
  decide +kernel

private theorem oneSigns : rawMeshOK one nodes = true := by
  decide +kernel

private theorem twoSigns : rawMeshOK two nodes = true := by
  decide +kernel

theorem lower_cutoff_mesh : LowerCutoffMeshCertificate 14 := by
  refine ⟨nodes, rows, by decide, originalChecks, ?_⟩
  intro k hk
  rcases hk with rfl | rfl
  · exact rawSharedSigns_of_numerator (by decide) oneCount oneSigns
  · exact rawSharedSigns_of_numerator (by decide) twoCount twoSigns

#print axioms lower_cutoff_mesh
end N014

namespace N015

private def nodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentFiniteData.N015
    LongCycleBounds.DescentNecklace.N015.nodes

private def rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentFiniteData.N015
    LongCycleBounds.DescentNecklace.N015.rows

private theorem originalChecks : RepresentativeChecks 15 nodes rows := 
  descentFrozenConst LongCycleBounds.DescentFiniteData.N015
    LongCycleBounds.DescentNecklace.N015.checks

private def codes (i : Fin 15) : ℕ → ℕ := Alphabets127.codes ⟨i.val, by omega⟩

private theorem checkedCodes (i : Fin 15) : PackedCutoffChecks 127 (i.val + 1) 1 (codes i) :=
  Alphabets127.checked ⟨i.val, by omega⟩

private def one : List ℤ :=
  [1, 32752, 13824739, 848090912, 15041229521, 102776998928, 311387598411, 447538817472,
  311387598411, 102776998928, 15041229521, 848090912, 13824739, 32752, 1]

private def two : List ℤ :=
  [0, 8192, 4120456, 272697216, 5069777856, 35866688640, 111799701600, 164757845888,
  117354576448, 39644853024, 5945714480, 344696896, 5820480, 14558, 0]

private theorem oneCount : descentRowDP 15 1 = one := by
  rw [← cachedLowerNumerator_eq (bound := 127) (n := 15) (k := 1)
    (by decide) (by decide) (by decide) codes checkedCodes]
  decide +kernel

private theorem twoCount : descentRowDP 15 2 = two := by
  rw [← cachedLowerNumerator_eq (bound := 127) (n := 15) (k := 2)
    (by decide) (by decide) (by decide) codes checkedCodes]
  decide +kernel

private theorem oneSigns : rawMeshOK one nodes = true := by
  decide +kernel

private theorem twoSigns : rawMeshOK two nodes = true := by
  decide +kernel

theorem lower_cutoff_mesh : LowerCutoffMeshCertificate 15 := by
  refine ⟨nodes, rows, by decide, originalChecks, ?_⟩
  intro k hk
  rcases hk with rfl | rfl
  · exact rawSharedSigns_of_numerator (by decide) oneCount oneSigns
  · exact rawSharedSigns_of_numerator (by decide) twoCount twoSigns

#print axioms lower_cutoff_mesh
end N015

namespace N016

private def nodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentFiniteData.N016
    LongCycleBounds.DescentNecklace.N016.nodes

private def rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentFiniteData.N016
    LongCycleBounds.DescentNecklace.N016.rows

private theorem originalChecks : RepresentativeChecks 16 nodes rows := 
  descentFrozenConst LongCycleBounds.DescentFiniteData.N016
    LongCycleBounds.DescentNecklace.N016.checks

private def codes (i : Fin 16) : ℕ → ℕ := Alphabets127.codes ⟨i.val, by omega⟩

private theorem checkedCodes (i : Fin 16) : PackedCutoffChecks 127 (i.val + 1) 1 (codes i) :=
  Alphabets127.checked ⟨i.val, by omega⟩

private def one : List ℤ :=
  [1, 65519, 41932745, 3572085255, 85383238549, 782115518299, 3207483178157, 6382798925475,
  6382798925475, 3207483178157, 782115518299, 85383238549, 3572085255, 41932745, 65519, 1]

private def two : List ℤ :=
  [0, 16384, 12476056, 1144354792, 28621255872, 270967688256, 1141264797600, 2324260081504,
  2374253955136, 1217930565376, 303271977424, 33864935152, 1454453824, 17665252, 29116, 1]

private theorem oneCount : descentRowDP 16 1 = one := by
  rw [← cachedLowerNumerator_eq (bound := 127) (n := 16) (k := 1)
    (by decide) (by decide) (by decide) codes checkedCodes]
  decide +kernel

private theorem twoCount : descentRowDP 16 2 = two := by
  rw [← cachedLowerNumerator_eq (bound := 127) (n := 16) (k := 2)
    (by decide) (by decide) (by decide) codes checkedCodes]
  decide +kernel

private theorem oneSigns : rawMeshOK one nodes = true := by
  decide +kernel

private theorem twoSigns : rawMeshOK two nodes = true := by
  decide +kernel

theorem lower_cutoff_mesh : LowerCutoffMeshCertificate 16 := by
  refine ⟨nodes, rows, by decide, originalChecks, ?_⟩
  intro k hk
  rcases hk with rfl | rfl
  · exact rawSharedSigns_of_numerator (by decide) oneCount oneSigns
  · exact rawSharedSigns_of_numerator (by decide) twoCount twoSigns

#print axioms lower_cutoff_mesh
end N016

namespace N017

private def nodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentSweepData.N017
    LongCycleBounds.DescentNecklace.Sweep.N017.nodes

private def rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentSweepData.N017
    LongCycleBounds.DescentNecklace.Sweep.N017.rows

private theorem originalChecks : RepresentativeChecks 17 nodes rows := by
  let counts := descentFrozenConst LongCycleBounds.DescentSweepData.N017
    LongCycleBounds.DescentNecklace.Sweep.N017.counts
  let signs := descentFrozenConst LongCycleBounds.DescentSweepData.N017
    LongCycleBounds.DescentNecklace.Sweep.N017.signs
  exact representativeChecks_of_shared (n := 17) (by decide) nodes rows counts signs

private def codes (i : Fin 17) : ℕ → ℕ := Alphabets127.codes ⟨i.val, by omega⟩

private theorem checkedCodes (i : Fin 17) : PackedCutoffChecks 127 (i.val + 1) 1 (codes i) :=
  Alphabets127.checked ⟨i.val, by omega⟩

private def one : List ℤ :=
  [1, 131054, 126781020, 14875399450, 473353301060, 5717291972382, 31055652948388,
  83137223185370, 114890380658550, 83137223185370, 31055652948388, 5717291972382, 473353301060,
  14875399450, 126781020, 131054, 1]

private def two : List ℤ :=
  [0, 32768, 37673928, 4752083952, 157982891656, 1969261200000, 10969498154016, 30006728628032,
  42286626329760, 31173337294848, 11861505709296, 2226011086368, 188232575472, 6065128824,
  53432496, 58248, 0]

private theorem oneCount : descentRowDP 17 1 = one := by
  rw [← cachedLowerNumerator_eq (bound := 127) (n := 17) (k := 1)
    (by decide) (by decide) (by decide) codes checkedCodes]
  decide +kernel

private theorem twoCount : descentRowDP 17 2 = two := by
  rw [← cachedLowerNumerator_eq (bound := 127) (n := 17) (k := 2)
    (by decide) (by decide) (by decide) codes checkedCodes]
  decide +kernel

private theorem oneSigns : rawMeshOK one nodes = true := by
  decide +kernel

private theorem twoSigns : rawMeshOK two nodes = true := by
  decide +kernel

theorem lower_cutoff_mesh : LowerCutoffMeshCertificate 17 := by
  refine ⟨nodes, rows, by decide, originalChecks, ?_⟩
  intro k hk
  rcases hk with rfl | rfl
  · exact rawSharedSigns_of_numerator (by decide) oneCount oneSigns
  · exact rawSharedSigns_of_numerator (by decide) twoCount twoSigns

#print axioms lower_cutoff_mesh
end N017

namespace N018

private def nodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentSweepData.N018
    LongCycleBounds.DescentNecklace.Sweep.N018.nodes

private def rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentSweepData.N018
    LongCycleBounds.DescentNecklace.Sweep.N018.rows

private theorem originalChecks : RepresentativeChecks 18 nodes rows := by
  let counts := descentFrozenConst LongCycleBounds.DescentSweepData.N018
    LongCycleBounds.DescentNecklace.Sweep.N018.counts
  let signs := descentFrozenConst LongCycleBounds.DescentSweepData.N018
    LongCycleBounds.DescentNecklace.Sweep.N018.signs
  exact representativeChecks_of_shared (n := 18) (by decide) nodes rows counts signs

private def codes (i : Fin 18) : ℕ → ℕ := Alphabets127.codes ⟨i.val, by omega⟩

private theorem checkedCodes (i : Fin 18) : PackedCutoffChecks 127 (i.val + 1) 1 (codes i) :=
  Alphabets127.checked ⟨i.val, by omega⟩

private def one : List ℤ :=
  [1, 262125, 382439924, 61403313100, 2575022097600, 40457344748072, 285997074307300,
  1006709967915228, 1865385657780650, 1865385657780650, 1006709967915228, 285997074307300,
  40457344748072, 2575022097600, 61403313100, 382439924, 262125, 1]

private def two : List ℤ :=
  [0, 65536, 113546072, 19573444728, 856443633608, 13869344791528, 100417621478112,
  360718308718432, 680646923248160, 692313009916320, 379863261161040, 109742673001488,
  15803089999344, 1026074680896, 25062002736, 161229456, 116496, 1]

private theorem oneCount : descentRowDP 18 1 = one := by
  rw [← cachedLowerNumerator_eq (bound := 127) (n := 18) (k := 1)
    (by decide) (by decide) (by decide) codes checkedCodes]
  decide +kernel

private theorem twoCount : descentRowDP 18 2 = two := by
  rw [← cachedLowerNumerator_eq (bound := 127) (n := 18) (k := 2)
    (by decide) (by decide) (by decide) codes checkedCodes]
  decide +kernel

private theorem oneSigns : rawMeshOK one nodes = true := by
  decide +kernel

private theorem twoSigns : rawMeshOK two nodes = true := by
  decide +kernel

theorem lower_cutoff_mesh : LowerCutoffMeshCertificate 18 := by
  refine ⟨nodes, rows, by decide, originalChecks, ?_⟩
  intro k hk
  rcases hk with rfl | rfl
  · exact rawSharedSigns_of_numerator (by decide) oneCount oneSigns
  · exact rawSharedSigns_of_numerator (by decide) twoCount twoSigns

#print axioms lower_cutoff_mesh
end N018

namespace N019

private def nodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentSweepData.N019
    LongCycleBounds.DescentNecklace.Sweep.N019.nodes

private def rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentSweepData.N019
    LongCycleBounds.DescentNecklace.Sweep.N019.rows

private theorem originalChecks : RepresentativeChecks 19 nodes rows := by
  let counts := descentFrozenConst LongCycleBounds.DescentSweepData.N019
    LongCycleBounds.DescentNecklace.Sweep.N019.counts
  let signs := descentFrozenConst LongCycleBounds.DescentSweepData.N019
    LongCycleBounds.DescentNecklace.Sweep.N019.signs
  exact representativeChecks_of_shared (n := 19) (by decide) nodes rows counts signs

private def codes (i : Fin 19) : ℕ → ℕ := Alphabets127.codes ⟨i.val, by omega⟩

private theorem checkedCodes (i : Fin 19) : PackedCutoffChecks 127 (i.val + 1) 1 (codes i) :=
  Alphabets127.checked ⟨i.val, by omega⟩

private def one : List ℤ :=
  [1, 524268, 1151775897, 251732291184, 13796160184500, 278794377854832, 2527925001876036,
  11485644635009424, 27862280567093358, 37307713155613000, 27862280567093358, 11485644635009424,
  2527925001876036, 278794377854832, 13796160184500, 251732291184, 1151775897, 524268, 1]

private def two : List ℤ :=
  [0, 131072, 341752328, 80110516064, 4575819838960, 95206279619680, 883224832636648,
  4090757927484800, 10093723705136192, 13729599331644800, 10409312962018320, 4355818165306176,
  973638881001888, 109183585528608, 5506303445520, 102827682240, 485668800, 233010, 0]

private theorem oneCount : descentRowDP 19 1 = one := by
  rw [← cachedLowerNumerator_eq (bound := 127) (n := 19) (k := 1)
    (by decide) (by decide) (by decide) codes checkedCodes]
  decide +kernel

private theorem twoCount : descentRowDP 19 2 = two := by
  rw [← cachedLowerNumerator_eq (bound := 127) (n := 19) (k := 2)
    (by decide) (by decide) (by decide) codes checkedCodes]
  decide +kernel

private theorem oneSigns : rawMeshOK one nodes = true := by
  decide +kernel

private theorem twoSigns : rawMeshOK two nodes = true := by
  decide +kernel

theorem lower_cutoff_mesh : LowerCutoffMeshCertificate 19 := by
  refine ⟨nodes, rows, by decide, originalChecks, ?_⟩
  intro k hk
  rcases hk with rfl | rfl
  · exact rawSharedSigns_of_numerator (by decide) oneCount oneSigns
  · exact rawSharedSigns_of_numerator (by decide) twoCount twoSigns

#print axioms lower_cutoff_mesh
end N019

namespace N020

private def nodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentSweepData.N020
    LongCycleBounds.DescentNecklace.Sweep.N020.nodes

private def rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentSweepData.N020
    LongCycleBounds.DescentNecklace.Sweep.N020.rows

private theorem originalChecks : RepresentativeChecks 20 nodes rows := by
  let counts := descentFrozenConst LongCycleBounds.DescentSweepData.N020
    LongCycleBounds.DescentNecklace.Sweep.N020.counts
  let signs := descentFrozenConst LongCycleBounds.DescentSweepData.N020
    LongCycleBounds.DescentNecklace.Sweep.N020.signs
  exact representativeChecks_of_shared (n := 20) (by decide) nodes rows counts signs

private def codes (i : Fin 20) : ℕ → ℕ := Alphabets127.codes ⟨i.val, by omega⟩

private theorem checkedCodes (i : Fin 20) : PackedCutoffChecks 127 (i.val + 1) 1 (codes i) :=
  Alphabets127.checked ⟨i.val, by omega⟩

private def one : List ℤ :=
  [1, 1048555, 3464764515, 1026509354985, 73008517581444, 1879708669896492, 21598596303099900,
  124748182104463860, 388588260723953310, 679562217794156938, 679562217794156938,
  388588260723953310, 124748182104463860, 21598596303099900, 1879708669896492, 73008517581444,
  1026509354985, 3464764515, 1048555, 1]

private def two : List ℤ :=
  [0, 262144, 1027616280, 326251853832, 24160867451824, 639874975302480, 7515461743132056,
  44207986244154824, 139932608476043328, 248326954072946112, 251798435898649520,
  145953634641838992, 47503850775473952, 8344042364413728, 737696064854448, 29176760143440,
  419567098560, 1461200580, 466020, 1]

private theorem oneCount : descentRowDP 20 1 = one := by
  rw [← cachedLowerNumerator_eq (bound := 127) (n := 20) (k := 1)
    (by decide) (by decide) (by decide) codes checkedCodes]
  decide +kernel

private theorem twoCount : descentRowDP 20 2 = two := by
  rw [← cachedLowerNumerator_eq (bound := 127) (n := 20) (k := 2)
    (by decide) (by decide) (by decide) codes checkedCodes]
  decide +kernel

private theorem oneSigns : rawMeshOK one nodes = true := by
  decide +kernel

private theorem twoSigns : rawMeshOK two nodes = true := by
  decide +kernel

theorem lower_cutoff_mesh : LowerCutoffMeshCertificate 20 := by
  refine ⟨nodes, rows, by decide, originalChecks, ?_⟩
  intro k hk
  rcases hk with rfl | rfl
  · exact rawSharedSigns_of_numerator (by decide) oneCount oneSigns
  · exact rawSharedSigns_of_numerator (by decide) twoCount twoSigns

#print axioms lower_cutoff_mesh
end N020

namespace N021

private def nodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentSweepData.N021
    LongCycleBounds.DescentNecklace.Sweep.N021.nodes

private def rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentSweepData.N021
    LongCycleBounds.DescentNecklace.Sweep.N021.rows

private theorem originalChecks : RepresentativeChecks 21 nodes rows := by
  let counts := descentFrozenConst LongCycleBounds.DescentSweepData.N021
    LongCycleBounds.DescentNecklace.Sweep.N021.counts
  let signs := descentFrozenConst LongCycleBounds.DescentSweepData.N021
    LongCycleBounds.DescentNecklace.Sweep.N021.signs
  exact representativeChecks_of_shared (n := 21) (by decide) nodes rows counts signs

private def codes (i : Fin 21) : ℕ → ℕ := Alphabets127.codes ⟨i.val, by omega⟩

private theorem checkedCodes (i : Fin 21) : PackedCutoffChecks 127 (i.val + 1) 1 (codes i) :=
  Alphabets127.checked ⟨i.val, by omega⟩

private def one : List ℤ :=
  [1, 2097130, 10414216090, 4168403181210, 382493246941965, 12446388300682056,
  179385804170146680, 1300365805079109480, 5119020713873609970, 11458681306629009100,
  14950368791471452636, 11458681306629009100, 5119020713873609970, 1300365805079109480,
  179385804170146680, 12446388300682056, 382493246941965, 4168403181210, 10414216090, 2097130,
  1]

private def two : List ℤ :=
  [0, 524288, 3087829576, 1323504508368, 126350618774264, 4225823731044064, 62206356831461592,
  458880354357087376, 1834097297458402664, 4162460842441981056, 5501379289687551952,
  4269427974688563104, 1931132771857712304, 496847399305583808, 69473737523712816,
  4893004551421728, 153016441392720, 1704570004680, 4392456120, 932060, 0]

private theorem oneCount : descentRowDP 21 1 = one := by
  rw [← cachedLowerNumerator_eq (bound := 127) (n := 21) (k := 1)
    (by decide) (by decide) (by decide) codes checkedCodes]
  decide +kernel

private theorem twoCount : descentRowDP 21 2 = two := by
  rw [← cachedLowerNumerator_eq (bound := 127) (n := 21) (k := 2)
    (by decide) (by decide) (by decide) codes checkedCodes]
  decide +kernel

private theorem oneSigns : rawMeshOK one nodes = true := by
  decide +kernel

private theorem twoSigns : rawMeshOK two nodes = true := by
  decide +kernel

theorem lower_cutoff_mesh : LowerCutoffMeshCertificate 21 := by
  refine ⟨nodes, rows, by decide, originalChecks, ?_⟩
  intro k hk
  rcases hk with rfl | rfl
  · exact rawSharedSigns_of_numerator (by decide) oneCount oneSigns
  · exact rawSharedSigns_of_numerator (by decide) twoCount twoSigns

#print axioms lower_cutoff_mesh
end N021

end LongCycleBounds.DescentNecklace.LowerPacked
