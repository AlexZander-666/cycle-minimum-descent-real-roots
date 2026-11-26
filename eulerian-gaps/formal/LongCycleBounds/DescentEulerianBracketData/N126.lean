import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentPackedData.C127L127.N126

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N126

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L127.N126 LongCycleBounds.DescentNecklace.Packed.C127L127.N126.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L127.N126 LongCycleBounds.DescentNecklace.Packed.C127L127.N126.rows

private theorem actual : RepresentativeChecks 126 previousNodes rows :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L127.N126 LongCycleBounds.DescentNecklace.Packed.C127L127.N126.dataChecks

private def first : LongCycleFinite.Dyadic := ⟨-42535295865117307932921825928971026432, 0⟩

private def gaps : List Window := [
  ⟨⟨-42533916661264259619332997515883577344, 0⟩, ⟨-10626837795931498217472, 0⟩⟩,
  ⟨⟨-9446210146417067950080, 0⟩, ⟨-4265873187536896, 0⟩⟩,
  ⟨⟨-3843566233190400, 0⟩, ⟨-1404173287424, 0⟩⟩,
  ⟨⟨-1221192581120, 0⟩, ⟨-7746158592, 0⟩⟩,
  ⟨⟨-7683162112, 0⟩, ⟨-221476864, 0⟩⟩,
  ⟨⟨-221095936, 0⟩, ⟨-16255872, 0⟩⟩,
  ⟨⟨-16245152, 0⟩, ⟨-2193952, 0⟩⟩,
  ⟨⟨-2193200, 0⟩, ⟨-448806, 0⟩⟩,
  ⟨⟨-448711, 0⟩, ⟨-494333, 2⟩⟩,
  ⟨⟨-494261, 2⟩, ⟨-42388, 0⟩⟩,
  ⟨⟨-339067, 3⟩, ⟨-137443, 3⟩⟩,
  ⟨⟨-274863, 4⟩, ⟨-507405, 6⟩⟩,
  ⟨⟨-507371, 6⟩, ⟨-519067, 7⟩⟩,
  ⟨⟨-259519, 6⟩, ⟨-72113, 5⟩⟩,
  ⟨⟨-144219, 6⟩, ⟨-5361, 2⟩⟩,
  ⟨⟨-343089, 8⟩, ⟨-431705, 9⟩⟩,
  ⟨⟨-431689, 9⟩, ⟨-284681, 9⟩⟩,
  ⟨⟨-556, 0⟩, ⟨-390695, 10⟩⟩,
  ⟨⟨-97671, 8⟩, ⟨-138671, 9⟩⟩,
  ⟨⟨-138667, 9⟩, ⟨-405419, 11⟩⟩,
  ⟨⟨-202705, 10⟩, ⟨-303899, 11⟩⟩,
  ⟨⟨-75973, 9⟩, ⟨-465739, 12⟩⟩,
  ⟨⟨-232865, 11⟩, ⟨-363829, 12⟩⟩,
  ⟨⟨-181911, 11⟩, ⟨-4517, 6⟩⟩,
  ⟨⟨-289083, 12⟩, ⟨-116589, 11⟩⟩,
  ⟨⟨-466349, 13⟩, ⟨-190613, 12⟩⟩,
  ⟨⟨-95305, 11⟩, ⟨-19711, 9⟩⟩,
  ⟨⟨-315371, 13⟩, ⟨-65925, 11⟩⟩,
  ⟨⟨-16481, 9⟩, ⟨-445237, 14⟩⟩,
  ⟨⟨-445231, 14⟩, ⟨-94785, 12⟩⟩,
  ⟨⟨-379135, 14⟩, ⟨-325389, 14⟩⟩,
  ⟨⟨-40673, 11⟩, ⟨-281245, 14⟩⟩,
  ⟨⟨-281241, 14⟩, ⟨-489319, 15⟩⟩,
  ⟨⟨-489313, 15⟩, ⟨-428167, 15⟩⟩,
  ⟨⟨-428163, 15⟩, ⟨-376663, 15⟩⟩,
  ⟨⟨-376659, 15⟩, ⟨-332971, 15⟩⟩,
  ⟨⟨-332967, 15⟩, ⟨-18479, 11⟩⟩,
  ⟨⟨-295661, 15⟩, ⟨-131805, 14⟩⟩,
  ⟨⟨-263607, 15⟩, ⟨-235909, 15⟩⟩,
  ⟨⟨-235907, 15⟩, ⟨-423691, 16⟩⟩,
  ⟨⟨-423687, 16⟩, ⟨-190835, 15⟩⟩,
  ⟨⟨-190833, 15⟩, ⟨-344807, 16⟩⟩,
  ⟨⟨-86201, 14⟩, ⟨-312329, 16⟩⟩,
  ⟨⟨-156163, 15⟩, ⟨-70899, 14⟩⟩,
  ⟨⟨-283593, 16⟩, ⟨-258079, 16⟩⟩,
  ⟨⟨-258077, 16⟩, ⟨-235335, 16⟩⟩,
  ⟨⟨-235333, 16⟩, ⟨-107497, 15⟩⟩,
  ⟨⟨-13437, 12⟩, ⟨-98371, 15⟩⟩,
  ⟨⟨-393481, 17⟩, ⟨-180317, 16⟩⟩,
  ⟨⟨-360631, 17⟩, ⟨-330985, 17⟩⟩,
  ⟨⟨-330983, 17⟩, ⟨-304155, 17⟩⟩,
  ⟨⟨-304153, 17⟩, ⟨-139907, 16⟩⟩,
  ⟨⟨-69953, 15⟩, ⟨-515355, 18⟩⟩,
  ⟨⟨-64419, 15⟩, ⟨-475001, 18⟩⟩,
  ⟨⟨-237499, 17⟩, ⟨-3423, 11⟩⟩,
  ⟨⟨-109535, 16⟩, ⟨-404413, 18⟩⟩,
  ⟨⟨-202205, 17⟩, ⟨-373483, 18⟩⟩,
  ⟨⟨-46685, 15⟩, ⟨-21567, 14⟩⟩,
  ⟨⟨-345069, 18⟩, ⟨-79733, 16⟩⟩,
  ⟨⟨-318929, 18⟩, ⟨-294845, 18⟩⟩,
  ⟨⟨-294843, 18⟩, ⟨-34077, 15⟩⟩,
  ⟨⟨-136307, 17⟩, ⟨-63019, 16⟩⟩,
  ⟨⟨-504149, 19⟩, ⟨-14567, 14⟩⟩,
  ⟨⟨-116535, 17⟩, ⟨-430939, 19⟩⟩,
  ⟨⟨-53867, 16⟩, ⟨-199147, 18⟩⟩,
  ⟨⟨-398291, 19⟩, ⟨-91999, 17⟩⟩,
  ⟨⟨-367993, 19⟩, ⟨-339851, 19⟩⟩,
  ⟨⟨-42481, 16⟩, ⟨-313687, 19⟩⟩,
  ⟨⟨-78421, 17⟩, ⟨-289347, 19⟩⟩,
  ⟨⟨-4521, 13⟩, ⟨-133345, 18⟩⟩,
  ⟨⟨-4167, 13⟩, ⟨-491185, 20⟩⟩,
  ⟨⟨-491181, 20⟩, ⟨-112969, 18⟩⟩,
  ⟨⟨-14121, 15⟩, ⟨-415245, 20⟩⟩,
  ⟨⟨-207621, 19⟩, ⟨-381107, 20⟩⟩,
  ⟨⟨-23819, 16⟩, ⟨-174645, 19⟩⟩,
  ⟨⟨-43661, 17⟩, ⟨-319637, 20⟩⟩,
  ⟨⟨-159817, 19⟩, ⟨-146005, 19⟩⟩,
  ⟨⟨-292007, 20⟩, ⟨-266275, 20⟩⟩,
  ⟨⟨-266273, 20⟩, ⟨-60579, 18⟩⟩,
  ⟨⟨-121157, 19⟩, ⟨-440049, 21⟩⟩,
  ⟨⟨-220023, 20⟩, ⟨-398601, 21⟩⟩,
  ⟨⟨-199299, 20⟩, ⟨-45013, 18⟩⟩,
  ⟨⟨-360101, 21⟩, ⟨-81097, 19⟩⟩,
  ⟨⟨-324385, 21⟩, ⟨-291299, 21⟩⟩,
  ⟨⟨-9103, 16⟩, ⟨-260689, 21⟩⟩,
  ⟨⟨-521373, 22⟩, ⟨-116213, 20⟩⟩,
  ⟨⟨-464847, 22⟩, ⟨-412767, 22⟩⟩,
  ⟨⟨-412763, 22⟩, ⟨-182445, 21⟩⟩,
  ⟨⟨-182443, 21⟩, ⟨-320997, 22⟩⟩,
  ⟨⟨-160497, 21⟩, ⟨-280881, 22⟩⟩,
  ⟨⟨-140439, 21⟩, ⟨-488683, 23⟩⟩,
  ⟨⟨-244339, 22⟩, ⟨-422387, 23⟩⟩,
  ⟨⟨-422383, 23⟩, ⟨-362507, 23⟩⟩,
  ⟨⟨-181251, 22⟩, ⟨-77173, 21⟩⟩,
  ⟨⟨-19293, 19⟩, ⟨-521203, 24⟩⟩,
  ⟨⟨-130299, 22⟩, ⟨-435801, 24⟩⟩,
  ⟨⟨-435795, 24⟩, ⟨-90131, 22⟩⟩,
  ⟨⟨-360519, 24⟩, ⟨-294713, 24⟩⟩,
  ⟨⟨-73677, 22⟩, ⟨-475431, 25⟩⟩,
  ⟨⟨-14857, 20⟩, ⟨-377763, 25⟩⟩,
  ⟨⟨-377757, 25⟩, ⟨-295109, 25⟩⟩,
  ⟨⟨-295103, 25⟩, ⟨-452263, 26⟩⟩,
  ⟨⟨-452255, 26⟩, ⟨-42377, 23⟩⟩,
  ⟨⟨-339009, 26⟩, ⟨-495567, 27⟩⟩,
  ⟨⟨-123889, 25⟩, ⟨-175899, 26⟩⟩,
  ⟨⟨-175895, 26⟩, ⟨-30175, 24⟩⟩,
  ⟨⟨-482789, 28⟩, ⟨-159185, 27⟩⟩,
  ⟨⟨-318361, 28⟩, ⟨-400587, 29⟩⟩,
  ⟨⟨-400575, 29⟩, ⟨-7445, 24⟩⟩,
  ⟨⟨-476465, 30⟩, ⟨-264795, 30⟩⟩,
  ⟨⟨-132393, 29⟩, ⟨-135439, 30⟩⟩,
  ⟨⟨-67717, 29⟩, ⟨-500009, 33⟩⟩,
  ⟨⟨-124997, 31⟩, ⟨-50665, 31⟩⟩,
  ⟨⟨-405301, 34⟩, ⟨-34757, 32⟩⟩,
  ⟨⟨-278041, 35⟩, ⟨-306297, 37⟩⟩,
  ⟨⟨-38285, 34⟩, ⟨-501329, 40⟩⟩,
  ⟨⟨-250649, 39⟩, ⟨-135315, 41⟩⟩,
  ⟨⟨-270611, 42⟩, ⟨-318117, 46⟩⟩,
  ⟨⟨-159047, 45⟩, ⟨-292181, 51⟩⟩,
  ⟨⟨-292159, 51⟩, ⟨-446237, 59⟩⟩,
  ⟨⟨-223101, 58⟩, ⟨-285049, 70⟩⟩,
  ⟨⟨-285025, 70⟩, ⟨-60295, 89⟩⟩,
  ⟨⟨-482315, 92⟩, ⟨-262149, 143⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private def eulerianCoefficients : List ℤ := [
  0x1, 0x1fffffffffffffffffffffffffffff82, 0x4590ec1853f061ac57f31fb9766821086c04c013b8f22b06d6,
  0x3ffffffffffddc2abcc06afafed28ce3662b7b8bfbddad5a9764af8cedccf2a, 0x4ba2f5a688e731997c20e19cdc062951daaf7ade8af53a00d8024320328d7c7f5ca9fc973, 0x8b21d80b6dabdb599d5bd5e7d4cd72e27abbc684ecde44ef090f4ecd2301c47ee04f2895a23b76a3c,
  0x790ac394ddc55f265a1c9c3a743c033c9468aa8b520c1a6e7a4d57ae1a664808abb929036d8cec1363f4f70c, 0x7fffc46cb2acf40caeb85f79501c4f89203ccdc4d878901c61e471ff396a75635a31901e0b3f36c9314e857f0955dc, 0x12e7324fa0e6569ec2f7047c46981582fa761572d5e27cc1d2436147ac1cb565289251c75a0069b2e686b1948bf800e63765,
  0x973c9d72ed22014982508ce92a03afdeabd760e2cff16aac5386ac8d684c5f6a872f18979d9a17ea527dc83f36c20c720e3d466e, 0x15859c298849b52642c0802d0289ecbf09c979fe8e593c08cd66f22a4c58f44b87de99735518df0fa5b0aee6abc74c3b99d7d673cca22, 0x1159a21bc68c3bcc9641bab39d35211d0b2331e51343ca412914110e4056bc6840a5f6b3d965e11865107da705305d8e826c1d859151400d6,
  0x5d7d7979e42d9017caa72d0a8defa39494d379f3dff17e29641e2a1081d5f310b5c38fea24da499dea5a179c9513677822696914e7d3715bccb7, 0xef3334e9eb7eb0717e196ec8598195ef908cf477270309bf2988fa34d8974555479f02f1db93a95745eb6c1b5c42f33317fe5c62d51855db5437d18, 0x14174b7420ea7bfc02395a3d5893dd5a04ec99f0c45bd72e8ba6f790cdcd0d5edb2939d49c8522c9410c1bff04eba9253470f17266572f006857b84ed58,
  0xf5ff3672397150489fe42fcef9a3b6e203f53761a91933706e91d7a438c852000e897e891cbb989e54fae89890523c603d8235aa987b4f44b6efb056ce198, 0x72751ade2a2e69d4e7024cf72acfd09955e3bd8fa8ffc46ff4fe72d316f48808bc40e928de73e859aec7fd307b25a214221b2e93ec6b705030479c4cae04c311, 0x222b16c97806dfd23133f982d92aefe39453cde4ae3aec5162211c6f93098442fc8d3127e7068ad499919b80e6742b821f2254d550ac7ede0463779eceed41b5c0a,
  0x6d7d00de5664bb215a7b76833e7a2d9a1d2944cb7b15655bf5ab655e4a93859e308329c46fa20ebb773b6c28431154f6a41c210aa842a0efd77c923779bb471e5215e, 0xf4568564f2591a15aac231cb3a900f6ed3f0d0db3c2eaa126d2b3d2399ae47e88c62c86429a5025341906e80a805b45d2655ed984aa1c634c9898dc38bc43b7906a73b2, 0x187ef95d49b6cc80f41a46c1c69698acc436f11aff2a64c71cc719962b4d82613433b43444c01b9eb051e37667e0bb2ccd753865ccbe23b841f11a64ecbc34eefb445c87d3,
  0x1d03abf95871767fb51e066d654817b8d072eec535870d6fcc9deedbe917478306188416afb91b118cb49dd236b42e1fb871c9976912360ab7896184cca807e5a8abc22a5274, 0x19f830bc48c8c890513feaf85cd9573bda86b91ec1820f9666651ad0c9e57bb1591de87b2329fa4a3e69db974b810f5d533c46b05806411493eb99ec3633b431bb6d214406d944, 0x11eb6798f561b71f7e714b29e8851f26bd33ad1eb99923bdfd9ba155ff0257eedd8bff0ea7dbb6f3ae7c5c24e4cfcaafbf2d887257610995982cf17d40d6a407ad701f5b7a240614,
  0x9b31c52af212e9ed6c1e3adf91aa4dd760680080fc7ae26ea06fcc1e5b368ee2fc009af9408532674c2051cc92613a6120a222232dca37894b482725135b819d755b4e219b9cae875, 0x42e8914326fe38844271613446ff7d861b4c2cfbccad3e5186c4678386ec7744d87e6756f9b67de295c36f150b96d3eef71f2b08afb744eb997204cca035175a5a5349be9fe86b9b056, 0x1749019ebcef686a97e53850b8b42bba2a7f291a66618974097873b4aca4b495e9492917e45f8b85ffa0083fc4284aa1e25983a365e2addf73d17b77834ae3b81f104bab23abc38a0a3ca,
  0x69e8f774e656287116def1ab3b0a9b709cc431d7f0a593f52163b467f72e5c7c3b95440d15de1e1086d9fa808497f2dac8a5700947599963eccf9f924a696d3e2c92072b3f6ebce5cac63e, 0x18da76772786688c08992ae94fac21aa77f7aa7702eed305196c65128ad6a5e94b1f162cdc58dbc33e207147a32ae073b024823dfb0fd6398bb0217c0abd841f784637dfddc31dd07f47e4d7, 0x4dc1fa6faf838fff5e1a681fa28e4a7dd95f9c1d7cd4a4d2372caac7c46a3746f36fcff608228f9a9a89ded85f2a6823aa18bbc218bff396ecd2d34572b8579390da92f6135c58ad3b32b17f0,
  0xcc6e3c11ee14051d3a8565100b018a4e44afdcec1542355ed5236f400be0fad5b3fb3b335a280dff0916f2a7be76e80e2f05fcd2290cd8d93650a8563903dfead0ebb3e11e004ee972591f4af0, 0x1c71194554a2f085c66174cb40640d5502d86ce8e35425e463b0f6d71567345fa695272052ee4e9b8d3c0affec7d5faacf8d257201d05e56f8ffbfff32c765d73921a57ba6e336b651ddaff4e5f0, 0x35f927ee77d8fcfe7048738fbcfaf1696a07f9a2801f132ad4a60b8aaf99fd23be00b7e59491f84517bf75a7e7080a80d23890a487317f360ab8e99733804bb27ec57bb15f6ee911c330bfcd3b065,
  0x57db11ac444f6cc0b565900fc7aa7162865373e9e7f9640455096061daf74afdd82a322785b531499997da0c4ceaf20d036b40e9c3bb8aabd4a67784dd6d034942a519b34cbf38700a58a6b14ac85a, 0x7b5b295f5e3088eea216830e7378e7b6c57efd37c73ffa396568fb2889aca8e0d18cabbf8cb2c52dee04a6f5fe99086c92c6d9a73de21c7b991717a99ee9402b563fb4d842da00b256fa61ce77bf07e, 0x962953a23070a4e07beb3b33ec47e0e9dd42fe8b1a454aff613147b99808e430f0e9ca9378c8d124badae136fdc55482f517da56933d75ec1514e821358e072519a0285e2e4e414372e26af4b60255a2,
  0x9f362f4888c15d3080fcbe3832828e0094c23d7d56602dbb2aa2aef576b6239bfe63e72d023f98f2eaf376dfc0cbfc420fe106d1592c19314bb89958b9057a0418b2149be1a646c4836df1418b9bbe73f, 0x93a7744970be507f98e1d5df4553c582bf8c7cdc4561a0f9afa5040f4f5fb9401f80524435c2d01959915ed07d62af8400306baf50261dc4f8489d353254a68c4a1d6ae878489601fb176d8c014439395c, 0x783d627bf6c7c3fa85acb10a875f8f5aba10dd7b19affcb52ce2703d0627cb1bd24fb44283a791a60b2909295b63e6917be279aba00c4643b8bde59545445fa86db7ea7eacf9daaa5b606137f045df665ec,
  0x5648172f307c591643dc1a862507a6f69eb44ca0caffa6aaef0e09e2af93257ed658d41ae2019f7208dd4f60ba53b1ad62654234346cbf159e89c7f66feacbe7873932128a44154c27eb2312fddfaa42b47c, 0x36bc12d8a689fedf1c99de3c234a99a522c50521e5711b43cd9113be2d004144ff8a21723877076b4d2028c05cddd2fefa2677cf6002e42c10310985970d927337f9e3a6bee7e99d86a4050c211c00f2732d9, 0x1ec989260de25ae6fad27936420f9a382aecf61e51f61159c1bed17053485b02a00fc781ef3ce13a594aecef8412b67c99f3cb06a1dfb60325b7a1c1705b58c44ebd6feefa2516b26020d87f81eea9f48c24b6,
  0xf658caee2071e41ed09da321c2e93f2082844b61d4b579b77b231220b5479aaea47a077d443b7e565cbe4f7cb3b6f87a4665df1fb2a2f86621a364f3c6e552c67b687c264f1e938d0592ca0dfdf199f24a823a, 0x6dcf09d7d7b48a8c862edbc147395b0ad2f77abe702825a580ffc8f1f9667bbd785e8adaefd6b986ff57b80eaa3bb382c55582f3743613f2badd414b6a1240cd5a943bb3f2a7150fdc94def9865289be27cb6be, 0x2bba4e766c2b74a6c1cb61d62ef775adc164106106570ddeec6f437db1a5450fbe33ef41093331930f9dac599acdc8d452be41e5a884a4d2d6798d4773606625b784bffab8273ee5edf005cd06874311bbf14b93,
  0xf96d1b2c0e98ec16a794009c1f4e80c733ce0821a0dbfc9c7126ffc00ca4bfcdf744049b1dbbe0ed1b524457055ef5cac575da55811ba240717ca46bc3c6d000157b312e3cd0213a9134c1d6acf7ae24efbfd6e8, 0x4fc2c2086cb6254105896b33b550e9ecf4e2c68ebf0d795632d41fe82ef15e0607bf654d9d0ef91eac5ed0f44674bd193c1a8e666be15ac0f684cbc0df13544cfd3b6799ba7f36c6e2b29e30f6591053f20ded428, 0x16eb22c0ebdc606f6d83ebc0eb0cef33e53bbd677b58b9f8746161844b29ec05057c8ea123d2b11a7a395f9b0d682a22fe5e6b61803b63cb08c70a4c69001fd2e3c40089eb593ce3e8b44a50c5487528e090a18d68,
  0x5ed4eb2c3416f1df3186f91be24d30c29ba4ab57a7f4b7042c397304abc42cbc4627d3fbfbc064acb2b1167a207c7c6bba7dca3f31abe24c2b7e7e40b749b21ad1cf746f184f2988104cca755149bde17504ace165, 0x161ae31164eb132e1c6db986593e340945a4f5c2a1039d0ae8aea61d17236f046af0ac5d6acbb0968febe020cdd105582bebb3d0452b6cfc6fa5c456f2727f15d5aad7938d9e1c06552b474c3273dfd09528e0942e2, 0x4a687657f1e8dc7cd4618d219b44570ae374d8f708a60b7a074b424ad99509a34e147e0544ce63d1f52a4b519f9abc1e5d5281fcb25645f95cdcc962a2f27eda8e58bc6cb01e0fbfea254c1aa1204c65df262d427c6,
  0xe25526da6b92dca9d11ccb3f077dcc4b70ad0441f5dcc57f1047344cd960fcec51260aaee66b151be80ac309e647e54acf323cc246a907c18327366f7cf646e6c6d86527b6564097a8683e693c83b254b9ed63835aa, 0x26ecc8428dbd56c4136edfe608ded0dddc56c6f46a50414aaa1f39e69945b137a8b6a5519c46092c6ce9800bff15f213da21d338a14ff86dc10601f71f92412ffe594bb9d71c8e0fc68acfc17d682630affce7584e2f, 0x60fd810b5127914ac0930dba4751c2391fb37c3d1905ad0c403dd24a32a7aca746a46f866071dc47339a0cc808ef6dae324c9b5cc006fa5a37235c2164b767dc9adf77319e32afa5883dd7b165380805d0a25af1ef34,
  0xdb08232dcbff7e4b0960d84fd858e439d57ac7fdde34153ee95b41b8ffb0ccad388d0d6fe6ba2ecaf96e066547d8a3383621391f5177d269d76da5694c6f8f404bfea093946a3312ee4e97ef5a8ba8810aef43a689c4, 0x1c0a43bf6ebe9ffa4c740e86074431eed3f26559eda2be2ceda7e55edeeda9f70d302824d282d1b76ba7986c607ae60008c2a539a4a46caa205b3bad43f388b138e81d6837ded437491a7b4355f017bb4ebe55bd48a54, 0x3420eebadd27a1a5a92da2fbbad6bb98c022593b47de4b26c5c5247f0c13bbe6b7f317bcfd86d60efcbf8dd879e119f80ff04154897cf277f13e4f6c954c3a510158c6a8a99ddf9cc7cfc5bf61cc1d531c804fc656699,
  0x5802542a5afcf67c7f0cd198fff9471fa2f435dee33084d02eefd77f10faa8e1daa4bfecac2a0c2113395f21472fe50207a5d1e88139f5deb9c5c4186411f9f813825828289dce8d88fe7c08e17065d3d3764d026165e, 0x8700ab0b419ae2145b47698c94da47ba844cf05237ef2425639392a0dde6bea67157876f42be2da7d8a2e385c306137146d004bc3924315b8d104eeaacdcb19241d7e6da7b7f7db40231c2194aaeb6ce80fec9f77cf62, 0xbc3b0376758fe47d2285ee2b1efc154c18f17d6f29a059ebf9fa7e1d3b3e52b62b60111effa6dabd0f4d09a0237cfa32371db0bf56c71e4ed9e41b56d9717cc9db46740f0f87dddc916b0ef283882ac9d466c8a0a1b66,
  0xee9e1a7a03c1f40d5689bf3ba545291c2ba1770df9daa2c7ca9ef2a157f9fe1ae3be4f92e9f79bbd78a8be9b1dde038f6afcddb2473821eca4dfd4220cc3cf1aebf4af1cd3dbeee9764864d67bb593825439f2d976e03, 0x11316b334413efea5a5df71d6157cc61a1868dd34f07aa8be527d4fab2f428e7b185c28f3a2e6cca0f63bd53a44000e15ab87209be613774426b28f8e22af8b855cdf6d451a18e1e09b3dd1da68127e5e90ad71d7cbf20, 0x12070d43b53707a59bcc6f6ac326cc84c3fb80fbf9cc7116212db00774d1c5e2de0750169589d2f60baf27cc4c2514aea82380c4aa65f49b222c1b3abe58051d234598f924c5ce56d27f7fc7da05e51b2734c7c1c86720,
  0x11316b334413efea5a5df71d6157cc61a1868dd34f07aa8be527d4fab2f428e7b185c28f3a2e6cca0f63bd53a44000e15ab87209be613774426b28f8e22af8b855cdf6d451a18e1e09b3dd1da68127e5e90ad71d7cbf20, 0xee9e1a7a03c1f40d5689bf3ba545291c2ba1770df9daa2c7ca9ef2a157f9fe1ae3be4f92e9f79bbd78a8be9b1dde038f6afcddb2473821eca4dfd4220cc3cf1aebf4af1cd3dbeee9764864d67bb593825439f2d976e03, 0xbc3b0376758fe47d2285ee2b1efc154c18f17d6f29a059ebf9fa7e1d3b3e52b62b60111effa6dabd0f4d09a0237cfa32371db0bf56c71e4ed9e41b56d9717cc9db46740f0f87dddc916b0ef283882ac9d466c8a0a1b66,
  0x8700ab0b419ae2145b47698c94da47ba844cf05237ef2425639392a0dde6bea67157876f42be2da7d8a2e385c306137146d004bc3924315b8d104eeaacdcb19241d7e6da7b7f7db40231c2194aaeb6ce80fec9f77cf62, 0x5802542a5afcf67c7f0cd198fff9471fa2f435dee33084d02eefd77f10faa8e1daa4bfecac2a0c2113395f21472fe50207a5d1e88139f5deb9c5c4186411f9f813825828289dce8d88fe7c08e17065d3d3764d026165e, 0x3420eebadd27a1a5a92da2fbbad6bb98c022593b47de4b26c5c5247f0c13bbe6b7f317bcfd86d60efcbf8dd879e119f80ff04154897cf277f13e4f6c954c3a510158c6a8a99ddf9cc7cfc5bf61cc1d531c804fc656699,
  0x1c0a43bf6ebe9ffa4c740e86074431eed3f26559eda2be2ceda7e55edeeda9f70d302824d282d1b76ba7986c607ae60008c2a539a4a46caa205b3bad43f388b138e81d6837ded437491a7b4355f017bb4ebe55bd48a54, 0xdb08232dcbff7e4b0960d84fd858e439d57ac7fdde34153ee95b41b8ffb0ccad388d0d6fe6ba2ecaf96e066547d8a3383621391f5177d269d76da5694c6f8f404bfea093946a3312ee4e97ef5a8ba8810aef43a689c4, 0x60fd810b5127914ac0930dba4751c2391fb37c3d1905ad0c403dd24a32a7aca746a46f866071dc47339a0cc808ef6dae324c9b5cc006fa5a37235c2164b767dc9adf77319e32afa5883dd7b165380805d0a25af1ef34,
  0x26ecc8428dbd56c4136edfe608ded0dddc56c6f46a50414aaa1f39e69945b137a8b6a5519c46092c6ce9800bff15f213da21d338a14ff86dc10601f71f92412ffe594bb9d71c8e0fc68acfc17d682630affce7584e2f, 0xe25526da6b92dca9d11ccb3f077dcc4b70ad0441f5dcc57f1047344cd960fcec51260aaee66b151be80ac309e647e54acf323cc246a907c18327366f7cf646e6c6d86527b6564097a8683e693c83b254b9ed63835aa, 0x4a687657f1e8dc7cd4618d219b44570ae374d8f708a60b7a074b424ad99509a34e147e0544ce63d1f52a4b519f9abc1e5d5281fcb25645f95cdcc962a2f27eda8e58bc6cb01e0fbfea254c1aa1204c65df262d427c6,
  0x161ae31164eb132e1c6db986593e340945a4f5c2a1039d0ae8aea61d17236f046af0ac5d6acbb0968febe020cdd105582bebb3d0452b6cfc6fa5c456f2727f15d5aad7938d9e1c06552b474c3273dfd09528e0942e2, 0x5ed4eb2c3416f1df3186f91be24d30c29ba4ab57a7f4b7042c397304abc42cbc4627d3fbfbc064acb2b1167a207c7c6bba7dca3f31abe24c2b7e7e40b749b21ad1cf746f184f2988104cca755149bde17504ace165, 0x16eb22c0ebdc606f6d83ebc0eb0cef33e53bbd677b58b9f8746161844b29ec05057c8ea123d2b11a7a395f9b0d682a22fe5e6b61803b63cb08c70a4c69001fd2e3c40089eb593ce3e8b44a50c5487528e090a18d68,
  0x4fc2c2086cb6254105896b33b550e9ecf4e2c68ebf0d795632d41fe82ef15e0607bf654d9d0ef91eac5ed0f44674bd193c1a8e666be15ac0f684cbc0df13544cfd3b6799ba7f36c6e2b29e30f6591053f20ded428, 0xf96d1b2c0e98ec16a794009c1f4e80c733ce0821a0dbfc9c7126ffc00ca4bfcdf744049b1dbbe0ed1b524457055ef5cac575da55811ba240717ca46bc3c6d000157b312e3cd0213a9134c1d6acf7ae24efbfd6e8, 0x2bba4e766c2b74a6c1cb61d62ef775adc164106106570ddeec6f437db1a5450fbe33ef41093331930f9dac599acdc8d452be41e5a884a4d2d6798d4773606625b784bffab8273ee5edf005cd06874311bbf14b93,
  0x6dcf09d7d7b48a8c862edbc147395b0ad2f77abe702825a580ffc8f1f9667bbd785e8adaefd6b986ff57b80eaa3bb382c55582f3743613f2badd414b6a1240cd5a943bb3f2a7150fdc94def9865289be27cb6be, 0xf658caee2071e41ed09da321c2e93f2082844b61d4b579b77b231220b5479aaea47a077d443b7e565cbe4f7cb3b6f87a4665df1fb2a2f86621a364f3c6e552c67b687c264f1e938d0592ca0dfdf199f24a823a, 0x1ec989260de25ae6fad27936420f9a382aecf61e51f61159c1bed17053485b02a00fc781ef3ce13a594aecef8412b67c99f3cb06a1dfb60325b7a1c1705b58c44ebd6feefa2516b26020d87f81eea9f48c24b6,
  0x36bc12d8a689fedf1c99de3c234a99a522c50521e5711b43cd9113be2d004144ff8a21723877076b4d2028c05cddd2fefa2677cf6002e42c10310985970d927337f9e3a6bee7e99d86a4050c211c00f2732d9, 0x5648172f307c591643dc1a862507a6f69eb44ca0caffa6aaef0e09e2af93257ed658d41ae2019f7208dd4f60ba53b1ad62654234346cbf159e89c7f66feacbe7873932128a44154c27eb2312fddfaa42b47c, 0x783d627bf6c7c3fa85acb10a875f8f5aba10dd7b19affcb52ce2703d0627cb1bd24fb44283a791a60b2909295b63e6917be279aba00c4643b8bde59545445fa86db7ea7eacf9daaa5b606137f045df665ec,
  0x93a7744970be507f98e1d5df4553c582bf8c7cdc4561a0f9afa5040f4f5fb9401f80524435c2d01959915ed07d62af8400306baf50261dc4f8489d353254a68c4a1d6ae878489601fb176d8c014439395c, 0x9f362f4888c15d3080fcbe3832828e0094c23d7d56602dbb2aa2aef576b6239bfe63e72d023f98f2eaf376dfc0cbfc420fe106d1592c19314bb89958b9057a0418b2149be1a646c4836df1418b9bbe73f, 0x962953a23070a4e07beb3b33ec47e0e9dd42fe8b1a454aff613147b99808e430f0e9ca9378c8d124badae136fdc55482f517da56933d75ec1514e821358e072519a0285e2e4e414372e26af4b60255a2,
  0x7b5b295f5e3088eea216830e7378e7b6c57efd37c73ffa396568fb2889aca8e0d18cabbf8cb2c52dee04a6f5fe99086c92c6d9a73de21c7b991717a99ee9402b563fb4d842da00b256fa61ce77bf07e, 0x57db11ac444f6cc0b565900fc7aa7162865373e9e7f9640455096061daf74afdd82a322785b531499997da0c4ceaf20d036b40e9c3bb8aabd4a67784dd6d034942a519b34cbf38700a58a6b14ac85a, 0x35f927ee77d8fcfe7048738fbcfaf1696a07f9a2801f132ad4a60b8aaf99fd23be00b7e59491f84517bf75a7e7080a80d23890a487317f360ab8e99733804bb27ec57bb15f6ee911c330bfcd3b065,
  0x1c71194554a2f085c66174cb40640d5502d86ce8e35425e463b0f6d71567345fa695272052ee4e9b8d3c0affec7d5faacf8d257201d05e56f8ffbfff32c765d73921a57ba6e336b651ddaff4e5f0, 0xcc6e3c11ee14051d3a8565100b018a4e44afdcec1542355ed5236f400be0fad5b3fb3b335a280dff0916f2a7be76e80e2f05fcd2290cd8d93650a8563903dfead0ebb3e11e004ee972591f4af0, 0x4dc1fa6faf838fff5e1a681fa28e4a7dd95f9c1d7cd4a4d2372caac7c46a3746f36fcff608228f9a9a89ded85f2a6823aa18bbc218bff396ecd2d34572b8579390da92f6135c58ad3b32b17f0,
  0x18da76772786688c08992ae94fac21aa77f7aa7702eed305196c65128ad6a5e94b1f162cdc58dbc33e207147a32ae073b024823dfb0fd6398bb0217c0abd841f784637dfddc31dd07f47e4d7, 0x69e8f774e656287116def1ab3b0a9b709cc431d7f0a593f52163b467f72e5c7c3b95440d15de1e1086d9fa808497f2dac8a5700947599963eccf9f924a696d3e2c92072b3f6ebce5cac63e, 0x1749019ebcef686a97e53850b8b42bba2a7f291a66618974097873b4aca4b495e9492917e45f8b85ffa0083fc4284aa1e25983a365e2addf73d17b77834ae3b81f104bab23abc38a0a3ca,
  0x42e8914326fe38844271613446ff7d861b4c2cfbccad3e5186c4678386ec7744d87e6756f9b67de295c36f150b96d3eef71f2b08afb744eb997204cca035175a5a5349be9fe86b9b056, 0x9b31c52af212e9ed6c1e3adf91aa4dd760680080fc7ae26ea06fcc1e5b368ee2fc009af9408532674c2051cc92613a6120a222232dca37894b482725135b819d755b4e219b9cae875, 0x11eb6798f561b71f7e714b29e8851f26bd33ad1eb99923bdfd9ba155ff0257eedd8bff0ea7dbb6f3ae7c5c24e4cfcaafbf2d887257610995982cf17d40d6a407ad701f5b7a240614,
  0x19f830bc48c8c890513feaf85cd9573bda86b91ec1820f9666651ad0c9e57bb1591de87b2329fa4a3e69db974b810f5d533c46b05806411493eb99ec3633b431bb6d214406d944, 0x1d03abf95871767fb51e066d654817b8d072eec535870d6fcc9deedbe917478306188416afb91b118cb49dd236b42e1fb871c9976912360ab7896184cca807e5a8abc22a5274, 0x187ef95d49b6cc80f41a46c1c69698acc436f11aff2a64c71cc719962b4d82613433b43444c01b9eb051e37667e0bb2ccd753865ccbe23b841f11a64ecbc34eefb445c87d3,
  0xf4568564f2591a15aac231cb3a900f6ed3f0d0db3c2eaa126d2b3d2399ae47e88c62c86429a5025341906e80a805b45d2655ed984aa1c634c9898dc38bc43b7906a73b2, 0x6d7d00de5664bb215a7b76833e7a2d9a1d2944cb7b15655bf5ab655e4a93859e308329c46fa20ebb773b6c28431154f6a41c210aa842a0efd77c923779bb471e5215e, 0x222b16c97806dfd23133f982d92aefe39453cde4ae3aec5162211c6f93098442fc8d3127e7068ad499919b80e6742b821f2254d550ac7ede0463779eceed41b5c0a,
  0x72751ade2a2e69d4e7024cf72acfd09955e3bd8fa8ffc46ff4fe72d316f48808bc40e928de73e859aec7fd307b25a214221b2e93ec6b705030479c4cae04c311, 0xf5ff3672397150489fe42fcef9a3b6e203f53761a91933706e91d7a438c852000e897e891cbb989e54fae89890523c603d8235aa987b4f44b6efb056ce198, 0x14174b7420ea7bfc02395a3d5893dd5a04ec99f0c45bd72e8ba6f790cdcd0d5edb2939d49c8522c9410c1bff04eba9253470f17266572f006857b84ed58,
  0xef3334e9eb7eb0717e196ec8598195ef908cf477270309bf2988fa34d8974555479f02f1db93a95745eb6c1b5c42f33317fe5c62d51855db5437d18, 0x5d7d7979e42d9017caa72d0a8defa39494d379f3dff17e29641e2a1081d5f310b5c38fea24da499dea5a179c9513677822696914e7d3715bccb7, 0x1159a21bc68c3bcc9641bab39d35211d0b2331e51343ca412914110e4056bc6840a5f6b3d965e11865107da705305d8e826c1d859151400d6,
  0x15859c298849b52642c0802d0289ecbf09c979fe8e593c08cd66f22a4c58f44b87de99735518df0fa5b0aee6abc74c3b99d7d673cca22, 0x973c9d72ed22014982508ce92a03afdeabd760e2cff16aac5386ac8d684c5f6a872f18979d9a17ea527dc83f36c20c720e3d466e, 0x12e7324fa0e6569ec2f7047c46981582fa761572d5e27cc1d2436147ac1cb565289251c75a0069b2e686b1948bf800e63765,
  0x7fffc46cb2acf40caeb85f79501c4f89203ccdc4d878901c61e471ff396a75635a31901e0b3f36c9314e857f0955dc, 0x790ac394ddc55f265a1c9c3a743c033c9468aa8b520c1a6e7a4d57ae1a664808abb929036d8cec1363f4f70c, 0x8b21d80b6dabdb599d5bd5e7d4cd72e27abbc684ecde44ef090f4ecd2301c47ee04f2895a23b76a3c,
  0x4ba2f5a688e731997c20e19cdc062951daaf7ade8af53a00d8024320328d7c7f5ca9fc973, 0x3ffffffffffddc2abcc06afafed28ce3662b7b8bfbddad5a9764af8cedccf2a, 0x4590ec1853f061ac57f31fb9766821086c04c013b8f22b06d6,
  0x1fffffffffffffffffffffffffffff82, 0x1]

private theorem eulerianCoefficients_eq : descentCoeffs 125 = eulerianCoefficients := by
  decide +kernel

private theorem upper : upperOK (descentCoeffs 125) first gaps = true := by
  rw [eulerianCoefficients_eq]
  decide +kernel

private theorem lower_000 : lowerOK (rows.getD 0 []) gaps = true := by
  decide +kernel

private theorem lower_001 : lowerOK (rows.getD 1 []) gaps = true := by
  decide +kernel

private theorem lower_002 : lowerOK (rows.getD 2 []) gaps = true := by
  decide +kernel

private theorem lower_003 : lowerOK (rows.getD 3 []) gaps = true := by
  decide +kernel

private theorem lower_004 : lowerOK (rows.getD 4 []) gaps = true := by
  decide +kernel

private theorem lower_005 : lowerOK (rows.getD 5 []) gaps = true := by
  decide +kernel

private theorem lower_006 : lowerOK (rows.getD 6 []) gaps = true := by
  decide +kernel

private theorem lower_007 : lowerOK (rows.getD 7 []) gaps = true := by
  decide +kernel

private theorem lower_008 : lowerOK (rows.getD 8 []) gaps = true := by
  decide +kernel

private theorem lower_009 : lowerOK (rows.getD 9 []) gaps = true := by
  decide +kernel

private theorem lower_010 : lowerOK (rows.getD 10 []) gaps = true := by
  decide +kernel

private theorem lower_011 : lowerOK (rows.getD 11 []) gaps = true := by
  decide +kernel

private theorem lower_012 : lowerOK (rows.getD 12 []) gaps = true := by
  decide +kernel

private theorem lower_013 : lowerOK (rows.getD 13 []) gaps = true := by
  decide +kernel

private theorem lower_014 : lowerOK (rows.getD 14 []) gaps = true := by
  decide +kernel

private theorem lower_015 : lowerOK (rows.getD 15 []) gaps = true := by
  decide +kernel

private theorem lower_016 : lowerOK (rows.getD 16 []) gaps = true := by
  decide +kernel

private theorem lower_017 : lowerOK (rows.getD 17 []) gaps = true := by
  decide +kernel

private theorem lower_018 : lowerOK (rows.getD 18 []) gaps = true := by
  decide +kernel

private theorem lower_019 : lowerOK (rows.getD 19 []) gaps = true := by
  decide +kernel

private theorem lower_020 : lowerOK (rows.getD 20 []) gaps = true := by
  decide +kernel

private theorem lower_021 : lowerOK (rows.getD 21 []) gaps = true := by
  decide +kernel

private theorem lower_022 : lowerOK (rows.getD 22 []) gaps = true := by
  decide +kernel

private theorem lower_023 : lowerOK (rows.getD 23 []) gaps = true := by
  decide +kernel

private theorem lower_024 : lowerOK (rows.getD 24 []) gaps = true := by
  decide +kernel

private theorem lower_025 : lowerOK (rows.getD 25 []) gaps = true := by
  decide +kernel

private theorem lower_026 : lowerOK (rows.getD 26 []) gaps = true := by
  decide +kernel

private theorem lower_027 : lowerOK (rows.getD 27 []) gaps = true := by
  decide +kernel

private theorem lower_028 : lowerOK (rows.getD 28 []) gaps = true := by
  decide +kernel

private theorem lower_029 : lowerOK (rows.getD 29 []) gaps = true := by
  decide +kernel

private theorem lower_030 : lowerOK (rows.getD 30 []) gaps = true := by
  decide +kernel

private theorem lower_031 : lowerOK (rows.getD 31 []) gaps = true := by
  decide +kernel

private theorem lower_032 : lowerOK (rows.getD 32 []) gaps = true := by
  decide +kernel

private theorem lower_033 : lowerOK (rows.getD 33 []) gaps = true := by
  decide +kernel

private theorem lower_034 : lowerOK (rows.getD 34 []) gaps = true := by
  decide +kernel

private theorem lower_035 : lowerOK (rows.getD 35 []) gaps = true := by
  decide +kernel

private theorem lower_036 : lowerOK (rows.getD 36 []) gaps = true := by
  decide +kernel

private theorem lower_037 : lowerOK (rows.getD 37 []) gaps = true := by
  decide +kernel

private theorem lower_038 : lowerOK (rows.getD 38 []) gaps = true := by
  decide +kernel

private theorem lower_039 : lowerOK (rows.getD 39 []) gaps = true := by
  decide +kernel

private theorem lower_040 : lowerOK (rows.getD 40 []) gaps = true := by
  decide +kernel

private theorem lower_041 : lowerOK (rows.getD 41 []) gaps = true := by
  decide +kernel

private theorem lower_042 : lowerOK (rows.getD 42 []) gaps = true := by
  decide +kernel

private theorem lower_043 : lowerOK (rows.getD 43 []) gaps = true := by
  decide +kernel

private theorem lower_044 : lowerOK (rows.getD 44 []) gaps = true := by
  decide +kernel

private theorem lower_045 : lowerOK (rows.getD 45 []) gaps = true := by
  decide +kernel

private theorem lower_046 : lowerOK (rows.getD 46 []) gaps = true := by
  decide +kernel

private theorem lower_047 : lowerOK (rows.getD 47 []) gaps = true := by
  decide +kernel

private theorem lower_048 : lowerOK (rows.getD 48 []) gaps = true := by
  decide +kernel

private theorem lower_049 : lowerOK (rows.getD 49 []) gaps = true := by
  decide +kernel

private theorem lower_050 : lowerOK (rows.getD 50 []) gaps = true := by
  decide +kernel

private theorem lower_051 : lowerOK (rows.getD 51 []) gaps = true := by
  decide +kernel

private theorem lower_052 : lowerOK (rows.getD 52 []) gaps = true := by
  decide +kernel

private theorem lower_053 : lowerOK (rows.getD 53 []) gaps = true := by
  decide +kernel

private theorem lower_054 : lowerOK (rows.getD 54 []) gaps = true := by
  decide +kernel

private theorem lower_055 : lowerOK (rows.getD 55 []) gaps = true := by
  decide +kernel

private theorem lower_056 : lowerOK (rows.getD 56 []) gaps = true := by
  decide +kernel

private theorem lower_057 : lowerOK (rows.getD 57 []) gaps = true := by
  decide +kernel

private theorem lower_058 : lowerOK (rows.getD 58 []) gaps = true := by
  decide +kernel

private theorem lower_059 : lowerOK (rows.getD 59 []) gaps = true := by
  decide +kernel

private theorem lower_060 : lowerOK (rows.getD 60 []) gaps = true := by
  decide +kernel

private theorem lower_061 : lowerOK (rows.getD 61 []) gaps = true := by
  decide +kernel

private theorem lower (i : Fin (lastRepresentative 126 - 2)) :
    lowerOK (rows.getD i.val []) gaps = true := by
  fin_cases i
  · exact lower_000
  · exact lower_001
  · exact lower_002
  · exact lower_003
  · exact lower_004
  · exact lower_005
  · exact lower_006
  · exact lower_007
  · exact lower_008
  · exact lower_009
  · exact lower_010
  · exact lower_011
  · exact lower_012
  · exact lower_013
  · exact lower_014
  · exact lower_015
  · exact lower_016
  · exact lower_017
  · exact lower_018
  · exact lower_019
  · exact lower_020
  · exact lower_021
  · exact lower_022
  · exact lower_023
  · exact lower_024
  · exact lower_025
  · exact lower_026
  · exact lower_027
  · exact lower_028
  · exact lower_029
  · exact lower_030
  · exact lower_031
  · exact lower_032
  · exact lower_033
  · exact lower_034
  · exact lower_035
  · exact lower_036
  · exact lower_037
  · exact lower_038
  · exact lower_039
  · exact lower_040
  · exact lower_041
  · exact lower_042
  · exact lower_043
  · exact lower_044
  · exact lower_045
  · exact lower_046
  · exact lower_047
  · exact lower_048
  · exact lower_049
  · exact lower_050
  · exact lower_051
  · exact lower_052
  · exact lower_053
  · exact lower_054
  · exact lower_055
  · exact lower_056
  · exact lower_057
  · exact lower_058
  · exact lower_059
  · exact lower_060
  · exact lower_061

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 126) :
    StrictNegativeInterlacing (originalQuotient 126 k) (eulerian 125) 123 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N126
