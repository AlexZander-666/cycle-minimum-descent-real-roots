import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentPackedData.C127L127.N123

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N123

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L127.N123 LongCycleBounds.DescentNecklace.Packed.C127L127.N123.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L127.N123 LongCycleBounds.DescentNecklace.Packed.C127L127.N123.rows

private theorem actual : RepresentativeChecks 123 previousNodes rows :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L127.N123 LongCycleBounds.DescentNecklace.Packed.C127L127.N123.dataChecks

private def first : LongCycleFinite.Dyadic := ⟨-5316911983139663491615228241121378304, 0⟩

private def gaps : List Window := [
  ⟨⟨-5316739582658032452416624689485447168, 0⟩, ⟨-3174434254946132033536, 0⟩⟩,
  ⟨⟨-3026851295157200879616, 0⟩, ⟨-1751595037491200, 0⟩⟩,
  ⟨⟨-1632748997443584, 0⟩, ⟨-708216619008, 0⟩⟩,
  ⟨⟨-630353559552, 0⟩, ⟨-4452925440, 0⟩⟩,
  ⟨⟨-4419403776, 0⟩, ⟨-139026944, 0⟩⟩,
  ⟨⟨-138806784, 0⟩, ⟨-10841696, 0⟩⟩,
  ⟨⟨-10835008, 0⟩, ⟨-1532760, 0⟩⟩,
  ⟨⟨-1532260, 0⟩, ⟨-325245, 0⟩⟩,
  ⟨⟨-325179, 0⟩, ⟨-184491, 1⟩⟩,
  ⟨⟨-184465, 1⟩, ⟨-518631, 4⟩⟩,
  ⟨⟨-518577, 4⟩, ⟨-214493, 4⟩⟩,
  ⟨⟨-428951, 5⟩, ⟨-201365, 5⟩⟩,
  ⟨⟨-25169, 2⟩, ⟨-52259, 4⟩⟩,
  ⟨⟨-418049, 7⟩, ⟨-29411, 4⟩⟩,
  ⟨⟨-235277, 7⟩, ⟨-141485, 7⟩⟩,
  ⟨⟨-282959, 8⟩, ⟨-359503, 9⟩⟩,
  ⟨⟨-359491, 9⟩, ⟨-59775, 7⟩⟩,
  ⟨⟨-478185, 10⟩, ⟨-330641, 10⟩⟩,
  ⟨⟨-330631, 10⟩, ⟨-472615, 11⟩⟩,
  ⟨⟨-472603, 11⟩, ⟨-43441, 8⟩⟩,
  ⟨⟨-2715, 4⟩, ⟨-523851, 12⟩⟩,
  ⟨⟨-523841, 12⟩, ⟨-201689, 11⟩⟩,
  ⟨⟨-403371, 12⟩, ⟨-158255, 11⟩⟩,
  ⟨⟨-39563, 9⟩, ⟨-504997, 13⟩⟩,
  ⟨⟨-504989, 13⟩, ⟨-408809, 13⟩⟩,
  ⟨⟨-408803, 13⟩, ⟨-335279, 13⟩⟩,
  ⟨⟨-167637, 12⟩, ⟨-278189, 13⟩⟩,
  ⟨⟨-278185, 13⟩, ⟨-233235, 13⟩⟩,
  ⟨⟨-14577, 9⟩, ⟨-394763, 14⟩⟩,
  ⟨⟨-197379, 13⟩, ⟨-336903, 14⟩⟩,
  ⟨⟨-336899, 14⟩, ⟨-289717, 14⟩⟩,
  ⟨⟨-289713, 14⟩, ⟨-250863, 14⟩⟩,
  ⟨⟨-62715, 12⟩, ⟨-437167, 15⟩⟩,
  ⟨⟨-218581, 14⟩, ⟨-383083, 15⟩⟩,
  ⟨⟨-383079, 15⟩, ⟨-42179, 12⟩⟩,
  ⟨⟨-84357, 13⟩, ⟨-298631, 15⟩⟩,
  ⟨⟨-74657, 13⟩, ⟨-265431, 15⟩⟩,
  ⟨⟨-66357, 13⟩, ⟨-236855, 15⟩⟩,
  ⟨⟨-473705, 16⟩, ⟨-424241, 16⟩⟩,
  ⟨⟨-424237, 16⟩, ⟨-381189, 16⟩⟩,
  ⟨⟨-381185, 16⟩, ⟨-343545, 16⟩⟩,
  ⟨⟨-171771, 15⟩, ⟨-310475, 16⟩⟩,
  ⟨⟨-38809, 13⟩, ⟨-70325, 14⟩⟩,
  ⟨⟨-281297, 16⟩, ⟨-510909, 17⟩⟩,
  ⟨⟨-510905, 17⟩, ⟨-116237, 15⟩⟩,
  ⟨⟨-29059, 13⟩, ⟨-423937, 17⟩⟩,
  ⟨⟨-423933, 17⟩, ⟨-24201, 13⟩⟩,
  ⟨⟨-387213, 17⟩, ⟨-177119, 16⟩⟩,
  ⟨⟨-354235, 17⟩, ⟨-162265, 16⟩⟩,
  ⟨⟨-20283, 13⟩, ⟨-297697, 17⟩⟩,
  ⟨⟨-297695, 17⟩, ⟨-136697, 16⟩⟩,
  ⟨⟨-273391, 17⟩, ⟨-502657, 18⟩⟩,
  ⟨⟨-251327, 17⟩, ⟨-115625, 16⟩⟩,
  ⟨⟨-462497, 18⟩, ⟨-425875, 18⟩⟩,
  ⟨⟨-26617, 14⟩, ⟨-392405, 18⟩⟩,
  ⟨⟨-196201, 17⟩, ⟨-11305, 13⟩⟩,
  ⟨⟨-361757, 18⟩, ⟨-333651, 18⟩⟩,
  ⟨⟨-20853, 14⟩, ⟨-153911, 17⟩⟩,
  ⟨⟨-307819, 18⟩, ⟨-71013, 16⟩⟩,
  ⟨⟨-142025, 17⟩, ⟨-131073, 17⟩⟩,
  ⟨⟨-524287, 19⟩, ⟨-483855, 19⟩⟩,
  ⟨⟨-483851, 19⟩, ⟨-446493, 19⟩⟩,
  ⟨⟨-223245, 18⟩, ⟨-411929, 19⟩⟩,
  ⟨⟨-205963, 18⟩, ⟨-379919, 19⟩⟩,
  ⟨⟨-94979, 17⟩, ⟨-350249, 19⟩⟩,
  ⟨⟨-175123, 18⟩, ⟨-80681, 17⟩⟩,
  ⟨⟨-161361, 18⟩, ⟨-18573, 15⟩⟩,
  ⟨⟨-148583, 18⟩, ⟨-273427, 19⟩⟩,
  ⟨⟨-273425, 19⟩, ⟨-251359, 19⟩⟩,
  ⟨⟨-502715, 20⟩, ⟨-461679, 20⟩⟩,
  ⟨⟨-115419, 18⟩, ⟨-26469, 16⟩⟩,
  ⟨⟨-105875, 18⟩, ⟨-96997, 18⟩⟩,
  ⟨⟨-387985, 20⟩, ⟨-2773, 13⟩⟩,
  ⟨⟨-354941, 20⟩, ⟨-324201, 20⟩⟩,
  ⟨⟨-162099, 19⟩, ⟨-73901, 18⟩⟩,
  ⟨⟨-295601, 20⟩, ⟨-269011, 20⟩⟩,
  ⟨⟨-16813, 16⟩, ⟨-488591, 21⟩⟩,
  ⟨⟨-488587, 21⟩, ⟨-110669, 19⟩⟩,
  ⟨⟨-27667, 17⟩, ⟨-400065, 21⟩⟩,
  ⟨⟨-200031, 20⟩, ⟨-90139, 19⟩⟩,
  ⟨⟨-360553, 21⟩, ⟨-323969, 21⟩⟩,
  ⟨⟨-323965, 21⟩, ⟨-290135, 21⟩⟩,
  ⟨⟨-72533, 19⟩, ⟨-64725, 19⟩⟩,
  ⟨⟨-517795, 22⟩, ⟨-460237, 22⟩⟩,
  ⟨⟨-460233, 22⟩, ⟨-25457, 18⟩⟩,
  ⟨⟨-101827, 20⟩, ⟨-44847, 19⟩⟩,
  ⟨⟨-89693, 20⟩, ⟨-314391, 22⟩⟩,
  ⟨⟨-78597, 20⟩, ⟨-136967, 21⟩⟩,
  ⟨⟨-273931, 22⟩, ⟨-237197, 22⟩⟩,
  ⟨⟨-474389, 23⟩, ⟨-407953, 23⟩⟩,
  ⟨⟨-101987, 21⟩, ⟨-85, 11⟩⟩,
  ⟨⟨-87039, 21⟩, ⟨-294641, 23⟩⟩,
  ⟨⟨-294637, 23⟩, ⟨-247027, 23⟩⟩,
  ⟨⟨-15439, 19⟩, ⟨-409927, 24⟩⟩,
  ⟨⟨-204961, 23⟩, ⟨-168099, 23⟩⟩,
  ⟨⟨-336193, 24⟩, ⟨-272163, 24⟩⟩,
  ⟨⟨-272159, 24⟩, ⟨-434237, 25⟩⟩,
  ⟨⟨-217115, 24⟩, ⟨-340723, 25⟩⟩,
  ⟨⟨-340717, 25⟩, ⟨-8199, 20⟩⟩,
  ⟨⟨-262363, 25⟩, ⟨-197743, 25⟩⟩,
  ⟨⟨-197739, 25⟩, ⟨-290813, 26⟩⟩,
  ⟨⟨-145403, 25⟩, ⟨-415691, 27⟩⟩,
  ⟨⟨-207841, 26⟩, ⟨-287415, 27⟩⟩,
  ⟨⟨-17963, 23⟩, ⟨-382309, 28⟩⟩,
  ⟨⟨-382299, 28⟩, ⟨-60715, 26⟩⟩,
  ⟨⟨-242853, 28⟩, ⟨-292081, 29⟩⟩,
  ⟨⟨-36509, 26⟩, ⟨-82191, 28⟩⟩,
  ⟨⟨-328753, 30⟩, ⟨-341281, 31⟩⟩,
  ⟨⟨-85317, 29⟩, ⟨-160207, 31⟩⟩,
  ⟨⟨-20025, 28⟩, ⟨-265029, 33⟩⟩,
  ⟨⟨-33127, 30⟩, ⟨-372533, 35⟩⟩,
  ⟨⟨-186257, 34⟩, ⟨-211307, 36⟩⟩,
  ⟨⟨-422591, 37⟩, ⟨-89675, 37⟩⟩,
  ⟨⟨-179339, 38⟩, ⟨-202839, 41⟩⟩,
  ⟨⟨-405651, 42⟩, ⟨-506801, 46⟩⟩,
  ⟨⟨-506765, 46⟩, ⟨-505923, 51⟩⟩,
  ⟨⟨-252943, 50⟩, ⟨-218049, 57⟩⟩,
  ⟨⟨-436063, 58⟩, ⟨-337849, 69⟩⟩,
  ⟨⟨-337821, 69⟩, ⟨-203505, 89⟩⟩,
  ⟨⟨-101743, 88⟩, ⟨-262165, 140⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private def eulerianCoefficients : List ℤ := [
  0x1, 0x3ffffffffffffffffffffffffffff85, 0x29396f76b67b7c401eb3a1059b80139336878e449386084b8,
  0xffffffffffec316771f652ab4d29cd31a24e49769844ccdea50d1e9a9b270, 0x9ae75758ee46075f337a30c84388b7a5846c334ef2c7c24ea73032a1418c44ca27c8506, 0xa4e5bd906cc6f928b028f958b3d106416a9c9acd664bae9854ef8d22ef21c903de70855c78ccdd6,
  0x5a5723fe9150c30c6df5a5cf9634bc978959c45a87489cffe4f84b38c1e137f754b33364d687c2b8edde90, 0x3fffd4982081adf1f453bf03a3eb6a734bb3fad99a524c59de8e0f91ad6a0279015c433cb4050e3d16b82032a138, 0x6a353d6e430ba6f36049b617c8ba48faf41a7a01ea096a5a3e2a5e6c6312d81d0865e6eedb78804aa7c4d58ef493c3707,
  0x26b6a5559f95356eff12b72a940a641e69c27921e1767db52d7bab048ab3e93e6498bbfec88148988d0b052bbb3aeb94ea53eb, 0x4236e8985367a5c4e250800058148513864d75d64c657507bdbea2c8a7301399699b81b1cc09844e1333f45aa467bd2e7e629e25b0, 0x29199a939842f2c0e8d913856bdc6b2a76561b3db14d80f10c06ae3f2d50a274581287b5579c892bec33fa3b0348a202cc20b8c360ba00,
  0xae0f396a04ab620b0b700086c022c9965a9e7a57b1d88a5df509373fcb8e414054dde1581b1aecbfa07a202231e8ebb138d1368565271829c, 0x1641dc529a6d9ef17bcb76fd13992acb6f2ca7c61798e9df0ef61918ce0997978857c85f85b563f0a59ac6e01ecd2486e55e56e74c878f43064dc, 0x18456ecba81cec13d9680f7681e96b3f6669e4052271a124e5fee217470ab17b4a2db933c678fb63361b9c1dd4b2c267c44b2c20d12f1b2c974aac80,
  0xf42cfe8e01a4e213393259084b2b3233642fb234690db078e9a2d258825c4368c03ab6a0f4dc98c06adc202128ae4bdf95be6d51b29ffe9c72e38debb0, 0x5e59dc115fe00b40580837132170a54161ded721596e0d918a0d041391cbe5240c92afb0c5c4f2eccc1cfe0dfb102f369eaf0e23762f2b54ebf619fcd0b85, 0x179b97487c767124c5c6609a4f3a876cf933e65cbf394ae8bca92a7ff2096da0c885768b85601a9675e9d9096ae61ff0315c5d8f656cecea92e9d55117234f89,
  0x3fe9812d90bcd5931cfb4072998f2fad03e14fc7bc9959401c3e70ffb04d137ff7c9cad03c58981f0112d5528fadbf2970a2a45621033ae642f887700a2e8620e8, 0x7955bae9f2bc319bb9037565839fcaf940c31c8e82b9604128c021a3a735568525d23943b6485cc40f534a756d996186da9305cae3d672d7c90208d014f044502470, 0xa69188ab9b5d4ccd6df72583441c3e1ab31ca2949c46648d2ffa65b6a33d82602153aa59927498c5314f4b60790650ed1fee01feef0391c02943423e2ed1c296c8deb2,
  0xa9bb5b747a8d2848cace2b033a0cbc50ce3f289e67762c39c6f8a3c4312d176bb8096aad089fc616f1079cb418391f16d7ccaef0e842c7c18a8b6a84a71e0e99ac9a0382, 0x834b9c28c35fae8b759225ffe6f4d1f738286327a52aa140f515fbcc435fbad4f7154d6bef670d425156b4c1bc0c1d3e64b666d5c2cf2380127fee99eb895e09fb20947090, 0x4e9c5e0725afac342a2996dcd6572e5e43ba729f946b0ee09ecd4a574aa83fd53f30925f87c29a682ceda91d05cb022feec5383988919dc518bf15bbeace2b7ae79b203e4568,
  0x250d08865fb76836c019abdadac04b3b509dad4716505b1827bd5c1ec78ef5686b2c9e62a12e439b19f526cc7330c26a2c905314f99c2d5bff62077986181815ff83fd50e2f5bb, 0xdf39621006f1a0aeccaa55fe58545caf420c7d863ba6f4dcd718c8235798ae7ecce721e209f2d5dc52d1d3c9b49e755ae871d587c27ea883b6c5b8255f7df6dffc986d57192f8df, 0x44088101df570c5a2e057a381006e6f0ecada7f1e2478a32f9ded06409f5fd984c22bbb2533428e108a9d6e054236dcf570f0bfe35b4f8c4a924ec4a09cf39c899ad43cf263f447e0,
  0x10fa134bae1d8e7f4d11b44cde0b923214716ec06f655b386be5fb35817c8c67435ffa1430405fba0792c319ec3f55f03c40d2189b9df4958a3b7793cbbd55250de6465d2ddcdcbe380, 0x38114b36cfd4a001addad967ffb998a99a2359da35156f64de8c63b7a85f32480a4c9c67f0c15ec941cdb320f15041154382f1003d43b7cef2b49296e7b5c7884bfc8df05c40ff517b98, 0x9a9214ecc7a332282d3c4f7b5f77f52753d6c530808ad760616fcb920ed2892c4306ee993d1eaf20803a7e89efbf3a1f28586d54ee3058ae0ad913b94bc759d1afd630d36e01c58e66298,
  0x166a297e75bf0022689adee375f9d7ff29e51d3aa1bf85a794240077a8af47dbc71a0557778e91f424fe5e0a45c46855c677c494ea425714c075d1edc3217f7c7b2c53fb8910318df8eb980, 0x2c178983ebc8f1f975be54508d5bd982dc9c7d4331498a855af3b17fa8aa6dc776e2c493dc9ae016027e65b615c698b55d36b76037a24a0b282c01de7df4865911849d41c7af53329fcdefe0, 0x4a05b1de97fd55858e2f4f3c4a8b76a23af04280ee8c95f091a0b2239577df82704fce83ee8dd2097bc55867a7ffe42c15b028209fdc010b953994dd087426e474ff5872ff256ed6fc916ef6d,
  0x6ab1cfc15c0d9b68eb72d87483955eb630d77dd3016fde5824ea88a2cbc8783ca6cc3f53982579dc20848bf53a2b4823bec87c4fd1f3ac6575584351f46cf3a8c50f9af293a413b6f4a3be6181, 0x84c1baa69002767fd678aae65053551ed5be3844f18301dc359d4be737cd6959a991c1e8dd6c2c27d355ee22ecf1f187ddb2ed4db05f426a66db8d0b45b3b2ec348e50a713f438e94282328af78, 0x8f4cd42581e46b78802577455aad53a5c88783f040b89d769e055054dc8404b50060d885e0a6e79e7a5a5eab1978873c004ca092ff5768df347653d8a372ae396d63c485cd02f1587919aab1b0b0,
  0x86ca8889c0535d4f9b9d7d94956991659efc7da62e34320b601d314d46545c7efae9374d1e38ca3767d28544b5620d250008ff89da5cc10bce2dd7b541dd71b8bb1d9bdba9016eeba5bc1a17c3bd6, 0x6ef0037733a42d66c0a816ca4528da116206ff7fa7b6f0e1d21c3d485888724758cbf21aafff0650c663df8ffd92edccaeeda1b4986c5e65a9f21e0479d358cc67911f9b8027ed7fab083ffae17866, 0x5030b039764fe9fd679e6e015e81ae69c9d597ce034b3266d3ff90f402b63b73b5e89a01aa47374693b360406796f621f9ec9995b1f92cb03f7582eda13adca22e207dafa231af24e2c3d4044ebaa50,
  0x3315263686bdfd8460f6804b7033111bb04e724d26af6a7e25bc9d9170fa16eaa29c97ca32c99886e5c3cebde28bc2281e6013ca2d2d7c9164ffb0d10b9fd7d96e70ea0fe789554f1030ebd0db9669f8, 0x1cc44e568c4cf5756696411aabc3f394bbb60dc13927418df0033e81dc6f79213987c2f0f711aad8182b00dc922b6489395c29099bdfd61d8dcb4ca8015a9ff681ad907881d49dd52ce42ca57e0a27b6b, 0xe5cb7ef0cef886da4371c365b7c2637bfd8e628b836e4319c305e1614f348f9e2959fc6abfc7916fd4aa27cb6981274641f8a50b90218e073a6125fe7fa0f52f1677dfb4aa1ec4ed88b937a4e87e3bfdf,
  0x65faffcda65e56ff861c42c109a0715e544ae5ff1183574e0f7d2f67f322e243e504f8858b5a913ce1633c5008bffdbbbd64b5b8400a621debf1be32a9fba7a7f937d463b0c48a6193ca6d9aa39e8cc350, 0x28536d3417fa1ebbf5e03331d41d0da9ba08c4c6b498fa67c7087ab31097dd1fa86ac8016d6577ba70797e8c3a8645ce49a63b7fb5f67f4b38705c42419dd790c8775ea9e10373d8ab6138c06cea93f3a80, 0xe3d50c5aba774840c9603fbd2bf0f44c91507da1dd9b327b880adbdcfeae659e596412827535a2e9456ae35f50831a5657b1c0f20240aa04bbcd0eba7a6b6768402438dfd66aee2b8690c421173f2fd4864,
  0x47fc362a38ff6de608dcb6e92ce82b781c1b7586b120ca20372554210797d351001ad4862ad9ba6ee5a7961841b3c4de1f1446c95adddc97dcd510784dcfcc5f29043970895bd2d04a6fb2b55881909793a4, 0x1463741d36c56e7f177887cb76b4af1b0c5a3fd582d60bcdea339bb8ba612bc913099dd3b9186f83cc34ed57dea3077fa08fe2b95916bc6f47bf4205db2d149e3773b798d295d7107b271e71597134d7f3700, 0x52f6aaa3f0f41441e44bf5547aad98222bf6d3c306110af0a41969d7083b614b5d18efb683df1a06a273cbf1f68373503b1cba93ef8d92e3ab399eb6798fd8b6734bbd128863524fbe4b0ded7fb0c21342150,
  0x12f97a21081371ae4c739e87fca8eeb068d60d484553ea3a95b8580b6717fcf3e427c027774067d437eab2904d0eb18ec37c178ec8e080e3e497851eef64605959c716e113f1a11eca46e8afeb2ea779077bf1, 0x3e872e069be0a111313e13611abdbb00afd035fdc1ec889278de9969b9ba85f83b742a8df782d5ca227d80e074cf0a22169c000a352fbb9c3924526b291570d64cb8d850fa80a0ca4c831e2c8d2666348bec45, 0xb9ca1087d1c1de6f74447ec076f8b37db209e6a77f15be64863f9124c4762a37955f9766562cd9c7bb26b361b043ef7e78631fe9ae640a137e597d196d878f30f811e524f431b2ecb0598db39504dd47c583e8,
  0x1f24df11129c13d252909481085ef77b4b7b1c9a12f66e2c509179c0da1c21fcd68ccc296bf7a407bfab79e8d65f29903dc4a3ec831348d95e1a1773ba008d4673f622d85e4ccc8e04d30444c77449b1ba60eb0, 0x4b79f5ece5bc463e1ebab471d1136bbd7958fbf6bac5d5c97b8bd509ca2dd5d11bff0b3b5fc07c2a7e58d80f9184af3aa48de81a88d34c166622a6e8b15e99a6282c5d9ab4a24ce64d4f1789aefa1796a336112, 0xa56c28e033c81a69b037db76c5e96e6603d609f8370c0f723686fa98e3fb46b41057312c916431c83f3ce6f2ec4e7cacda0dd9563b2d04b143cbc11420ebf4dbd2ed30dae945fbc435cb99dff3642f9b17a75a2,
  0x1482455b99c891aa35871d710d4af2bf84b3c3c9ac8b1d1705f98e965b7f446082cdbfdce284da9b745da680345d68a283cbb5c645cf452abc09bc0ee4e723e5b3231882bc39b205680275e2793c8f6e2dbe7050, 0x24d86ef62fbc291b4d4f309b042644562cf47fc2b8607c186e7143514e667db3ef4f1bcf583afe0ac87831274dea90ead28395850e1036e265ebf334e7e47f6b0a6dc9ef78f497e6a26ed3076076101614d0d668, 0x3bfc54875a4f885bfef88e6e35929699a9af32da3fbb375ea594de940891053d0058080819e2a692c1e7e4ad1447cf1d11e3ac948c0818c51a9d9cf161be6753fa0c64fd31e2bf7997c08e0ea816f5541ad43aff,
  0x588a1650944cf3bc78f0af352ddd095baa8a83132911af2d0777100ad761fd7d484cc56ea85978516d0f4e9bbc1b2042c8e18061674b2e258e7a7b0fb64d0f6150cbd3466c6a87efb9fa5c8923b873632aaffc73, 0x76869b267b3442f77134e454382136a15828c53fe2d6018bdb8888dcfe1bd8a48b8bd4ba29e0da313b877d264df8d8b976ba20674f83212ba8a325a4eea0ed8f66e42f6a55c85961044ce0ad483dd26233a3d240, 0x8ff1f66cc5515ffeff983bba1379196a472f44c468c574a9362eb23a386589efc17a78b94c1e36750d0d1e739c58cb086f54ab0824e62a2008462eb0ace378a106953ab4e84b92561a510dfea3ff23a380bd8b00,
  0x9e9fc5b20fcf04c2411346842c346869208d3bcc6e26c61e710561f5a44c6480dad36d8fe8551d35444b10599b5fadbceaeca337f59790346394ee77aadb8090a2004793a6915e25a65b037f13ee593a58199e50, 0x9e9fc5b20fcf04c2411346842c346869208d3bcc6e26c61e710561f5a44c6480dad36d8fe8551d35444b10599b5fadbceaeca337f59790346394ee77aadb8090a2004793a6915e25a65b037f13ee593a58199e50, 0x8ff1f66cc5515ffeff983bba1379196a472f44c468c574a9362eb23a386589efc17a78b94c1e36750d0d1e739c58cb086f54ab0824e62a2008462eb0ace378a106953ab4e84b92561a510dfea3ff23a380bd8b00,
  0x76869b267b3442f77134e454382136a15828c53fe2d6018bdb8888dcfe1bd8a48b8bd4ba29e0da313b877d264df8d8b976ba20674f83212ba8a325a4eea0ed8f66e42f6a55c85961044ce0ad483dd26233a3d240, 0x588a1650944cf3bc78f0af352ddd095baa8a83132911af2d0777100ad761fd7d484cc56ea85978516d0f4e9bbc1b2042c8e18061674b2e258e7a7b0fb64d0f6150cbd3466c6a87efb9fa5c8923b873632aaffc73, 0x3bfc54875a4f885bfef88e6e35929699a9af32da3fbb375ea594de940891053d0058080819e2a692c1e7e4ad1447cf1d11e3ac948c0818c51a9d9cf161be6753fa0c64fd31e2bf7997c08e0ea816f5541ad43aff,
  0x24d86ef62fbc291b4d4f309b042644562cf47fc2b8607c186e7143514e667db3ef4f1bcf583afe0ac87831274dea90ead28395850e1036e265ebf334e7e47f6b0a6dc9ef78f497e6a26ed3076076101614d0d668, 0x1482455b99c891aa35871d710d4af2bf84b3c3c9ac8b1d1705f98e965b7f446082cdbfdce284da9b745da680345d68a283cbb5c645cf452abc09bc0ee4e723e5b3231882bc39b205680275e2793c8f6e2dbe7050, 0xa56c28e033c81a69b037db76c5e96e6603d609f8370c0f723686fa98e3fb46b41057312c916431c83f3ce6f2ec4e7cacda0dd9563b2d04b143cbc11420ebf4dbd2ed30dae945fbc435cb99dff3642f9b17a75a2,
  0x4b79f5ece5bc463e1ebab471d1136bbd7958fbf6bac5d5c97b8bd509ca2dd5d11bff0b3b5fc07c2a7e58d80f9184af3aa48de81a88d34c166622a6e8b15e99a6282c5d9ab4a24ce64d4f1789aefa1796a336112, 0x1f24df11129c13d252909481085ef77b4b7b1c9a12f66e2c509179c0da1c21fcd68ccc296bf7a407bfab79e8d65f29903dc4a3ec831348d95e1a1773ba008d4673f622d85e4ccc8e04d30444c77449b1ba60eb0, 0xb9ca1087d1c1de6f74447ec076f8b37db209e6a77f15be64863f9124c4762a37955f9766562cd9c7bb26b361b043ef7e78631fe9ae640a137e597d196d878f30f811e524f431b2ecb0598db39504dd47c583e8,
  0x3e872e069be0a111313e13611abdbb00afd035fdc1ec889278de9969b9ba85f83b742a8df782d5ca227d80e074cf0a22169c000a352fbb9c3924526b291570d64cb8d850fa80a0ca4c831e2c8d2666348bec45, 0x12f97a21081371ae4c739e87fca8eeb068d60d484553ea3a95b8580b6717fcf3e427c027774067d437eab2904d0eb18ec37c178ec8e080e3e497851eef64605959c716e113f1a11eca46e8afeb2ea779077bf1, 0x52f6aaa3f0f41441e44bf5547aad98222bf6d3c306110af0a41969d7083b614b5d18efb683df1a06a273cbf1f68373503b1cba93ef8d92e3ab399eb6798fd8b6734bbd128863524fbe4b0ded7fb0c21342150,
  0x1463741d36c56e7f177887cb76b4af1b0c5a3fd582d60bcdea339bb8ba612bc913099dd3b9186f83cc34ed57dea3077fa08fe2b95916bc6f47bf4205db2d149e3773b798d295d7107b271e71597134d7f3700, 0x47fc362a38ff6de608dcb6e92ce82b781c1b7586b120ca20372554210797d351001ad4862ad9ba6ee5a7961841b3c4de1f1446c95adddc97dcd510784dcfcc5f29043970895bd2d04a6fb2b55881909793a4, 0xe3d50c5aba774840c9603fbd2bf0f44c91507da1dd9b327b880adbdcfeae659e596412827535a2e9456ae35f50831a5657b1c0f20240aa04bbcd0eba7a6b6768402438dfd66aee2b8690c421173f2fd4864,
  0x28536d3417fa1ebbf5e03331d41d0da9ba08c4c6b498fa67c7087ab31097dd1fa86ac8016d6577ba70797e8c3a8645ce49a63b7fb5f67f4b38705c42419dd790c8775ea9e10373d8ab6138c06cea93f3a80, 0x65faffcda65e56ff861c42c109a0715e544ae5ff1183574e0f7d2f67f322e243e504f8858b5a913ce1633c5008bffdbbbd64b5b8400a621debf1be32a9fba7a7f937d463b0c48a6193ca6d9aa39e8cc350, 0xe5cb7ef0cef886da4371c365b7c2637bfd8e628b836e4319c305e1614f348f9e2959fc6abfc7916fd4aa27cb6981274641f8a50b90218e073a6125fe7fa0f52f1677dfb4aa1ec4ed88b937a4e87e3bfdf,
  0x1cc44e568c4cf5756696411aabc3f394bbb60dc13927418df0033e81dc6f79213987c2f0f711aad8182b00dc922b6489395c29099bdfd61d8dcb4ca8015a9ff681ad907881d49dd52ce42ca57e0a27b6b, 0x3315263686bdfd8460f6804b7033111bb04e724d26af6a7e25bc9d9170fa16eaa29c97ca32c99886e5c3cebde28bc2281e6013ca2d2d7c9164ffb0d10b9fd7d96e70ea0fe789554f1030ebd0db9669f8, 0x5030b039764fe9fd679e6e015e81ae69c9d597ce034b3266d3ff90f402b63b73b5e89a01aa47374693b360406796f621f9ec9995b1f92cb03f7582eda13adca22e207dafa231af24e2c3d4044ebaa50,
  0x6ef0037733a42d66c0a816ca4528da116206ff7fa7b6f0e1d21c3d485888724758cbf21aafff0650c663df8ffd92edccaeeda1b4986c5e65a9f21e0479d358cc67911f9b8027ed7fab083ffae17866, 0x86ca8889c0535d4f9b9d7d94956991659efc7da62e34320b601d314d46545c7efae9374d1e38ca3767d28544b5620d250008ff89da5cc10bce2dd7b541dd71b8bb1d9bdba9016eeba5bc1a17c3bd6, 0x8f4cd42581e46b78802577455aad53a5c88783f040b89d769e055054dc8404b50060d885e0a6e79e7a5a5eab1978873c004ca092ff5768df347653d8a372ae396d63c485cd02f1587919aab1b0b0,
  0x84c1baa69002767fd678aae65053551ed5be3844f18301dc359d4be737cd6959a991c1e8dd6c2c27d355ee22ecf1f187ddb2ed4db05f426a66db8d0b45b3b2ec348e50a713f438e94282328af78, 0x6ab1cfc15c0d9b68eb72d87483955eb630d77dd3016fde5824ea88a2cbc8783ca6cc3f53982579dc20848bf53a2b4823bec87c4fd1f3ac6575584351f46cf3a8c50f9af293a413b6f4a3be6181, 0x4a05b1de97fd55858e2f4f3c4a8b76a23af04280ee8c95f091a0b2239577df82704fce83ee8dd2097bc55867a7ffe42c15b028209fdc010b953994dd087426e474ff5872ff256ed6fc916ef6d,
  0x2c178983ebc8f1f975be54508d5bd982dc9c7d4331498a855af3b17fa8aa6dc776e2c493dc9ae016027e65b615c698b55d36b76037a24a0b282c01de7df4865911849d41c7af53329fcdefe0, 0x166a297e75bf0022689adee375f9d7ff29e51d3aa1bf85a794240077a8af47dbc71a0557778e91f424fe5e0a45c46855c677c494ea425714c075d1edc3217f7c7b2c53fb8910318df8eb980, 0x9a9214ecc7a332282d3c4f7b5f77f52753d6c530808ad760616fcb920ed2892c4306ee993d1eaf20803a7e89efbf3a1f28586d54ee3058ae0ad913b94bc759d1afd630d36e01c58e66298,
  0x38114b36cfd4a001addad967ffb998a99a2359da35156f64de8c63b7a85f32480a4c9c67f0c15ec941cdb320f15041154382f1003d43b7cef2b49296e7b5c7884bfc8df05c40ff517b98, 0x10fa134bae1d8e7f4d11b44cde0b923214716ec06f655b386be5fb35817c8c67435ffa1430405fba0792c319ec3f55f03c40d2189b9df4958a3b7793cbbd55250de6465d2ddcdcbe380, 0x44088101df570c5a2e057a381006e6f0ecada7f1e2478a32f9ded06409f5fd984c22bbb2533428e108a9d6e054236dcf570f0bfe35b4f8c4a924ec4a09cf39c899ad43cf263f447e0,
  0xdf39621006f1a0aeccaa55fe58545caf420c7d863ba6f4dcd718c8235798ae7ecce721e209f2d5dc52d1d3c9b49e755ae871d587c27ea883b6c5b8255f7df6dffc986d57192f8df, 0x250d08865fb76836c019abdadac04b3b509dad4716505b1827bd5c1ec78ef5686b2c9e62a12e439b19f526cc7330c26a2c905314f99c2d5bff62077986181815ff83fd50e2f5bb, 0x4e9c5e0725afac342a2996dcd6572e5e43ba729f946b0ee09ecd4a574aa83fd53f30925f87c29a682ceda91d05cb022feec5383988919dc518bf15bbeace2b7ae79b203e4568,
  0x834b9c28c35fae8b759225ffe6f4d1f738286327a52aa140f515fbcc435fbad4f7154d6bef670d425156b4c1bc0c1d3e64b666d5c2cf2380127fee99eb895e09fb20947090, 0xa9bb5b747a8d2848cace2b033a0cbc50ce3f289e67762c39c6f8a3c4312d176bb8096aad089fc616f1079cb418391f16d7ccaef0e842c7c18a8b6a84a71e0e99ac9a0382, 0xa69188ab9b5d4ccd6df72583441c3e1ab31ca2949c46648d2ffa65b6a33d82602153aa59927498c5314f4b60790650ed1fee01feef0391c02943423e2ed1c296c8deb2,
  0x7955bae9f2bc319bb9037565839fcaf940c31c8e82b9604128c021a3a735568525d23943b6485cc40f534a756d996186da9305cae3d672d7c90208d014f044502470, 0x3fe9812d90bcd5931cfb4072998f2fad03e14fc7bc9959401c3e70ffb04d137ff7c9cad03c58981f0112d5528fadbf2970a2a45621033ae642f887700a2e8620e8, 0x179b97487c767124c5c6609a4f3a876cf933e65cbf394ae8bca92a7ff2096da0c885768b85601a9675e9d9096ae61ff0315c5d8f656cecea92e9d55117234f89,
  0x5e59dc115fe00b40580837132170a54161ded721596e0d918a0d041391cbe5240c92afb0c5c4f2eccc1cfe0dfb102f369eaf0e23762f2b54ebf619fcd0b85, 0xf42cfe8e01a4e213393259084b2b3233642fb234690db078e9a2d258825c4368c03ab6a0f4dc98c06adc202128ae4bdf95be6d51b29ffe9c72e38debb0, 0x18456ecba81cec13d9680f7681e96b3f6669e4052271a124e5fee217470ab17b4a2db933c678fb63361b9c1dd4b2c267c44b2c20d12f1b2c974aac80,
  0x1641dc529a6d9ef17bcb76fd13992acb6f2ca7c61798e9df0ef61918ce0997978857c85f85b563f0a59ac6e01ecd2486e55e56e74c878f43064dc, 0xae0f396a04ab620b0b700086c022c9965a9e7a57b1d88a5df509373fcb8e414054dde1581b1aecbfa07a202231e8ebb138d1368565271829c, 0x29199a939842f2c0e8d913856bdc6b2a76561b3db14d80f10c06ae3f2d50a274581287b5579c892bec33fa3b0348a202cc20b8c360ba00,
  0x4236e8985367a5c4e250800058148513864d75d64c657507bdbea2c8a7301399699b81b1cc09844e1333f45aa467bd2e7e629e25b0, 0x26b6a5559f95356eff12b72a940a641e69c27921e1767db52d7bab048ab3e93e6498bbfec88148988d0b052bbb3aeb94ea53eb, 0x6a353d6e430ba6f36049b617c8ba48faf41a7a01ea096a5a3e2a5e6c6312d81d0865e6eedb78804aa7c4d58ef493c3707,
  0x3fffd4982081adf1f453bf03a3eb6a734bb3fad99a524c59de8e0f91ad6a0279015c433cb4050e3d16b82032a138, 0x5a5723fe9150c30c6df5a5cf9634bc978959c45a87489cffe4f84b38c1e137f754b33364d687c2b8edde90, 0xa4e5bd906cc6f928b028f958b3d106416a9c9acd664bae9854ef8d22ef21c903de70855c78ccdd6,
  0x9ae75758ee46075f337a30c84388b7a5846c334ef2c7c24ea73032a1418c44ca27c8506, 0xffffffffffec316771f652ab4d29cd31a24e49769844ccdea50d1e9a9b270, 0x29396f76b67b7c401eb3a1059b80139336878e449386084b8,
  0x3ffffffffffffffffffffffffffff85, 0x1]

private theorem eulerianCoefficients_eq : descentCoeffs 122 = eulerianCoefficients := by
  decide +kernel

private theorem upper : upperOK (descentCoeffs 122) first gaps = true := by
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

private theorem lower (i : Fin (lastRepresentative 123 - 2)) :
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

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 123) :
    StrictNegativeInterlacing (originalQuotient 123 k) (eulerian 122) 120 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N123
