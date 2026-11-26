import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentPackedData.C127L120.N114

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N114

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L120.N114 LongCycleBounds.DescentNecklace.Packed.C127L120.N114.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L120.N114 LongCycleBounds.DescentNecklace.Packed.C127L120.N114.rows

private theorem actual : RepresentativeChecks 114 previousNodes rows :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L120.N114 LongCycleBounds.DescentNecklace.Packed.C127L120.N114.dataChecks

private def first : LongCycleFinite.Dyadic := ⟨-10384593717069655257060992658440192, 0⟩

private def gaps : List Window := [
  ⟨⟨-10384256997378969633626220096651264, 0⟩, ⟨-79317396637249175552, 0⟩⟩,
  ⟨⟨-79028884786120753152, 0⟩, ⟨-132763344699392, 0⟩⟩,
  ⟨⟨-129615938977792, 0⟩, ⟨-90486079488, 0⟩⟩,
  ⟨⟨-84500021248, 0⟩, ⟨-856743936, 0⟩⟩,
  ⟨⟨-852359168, 0⟩, ⟨-34297472, 0⟩⟩,
  ⟨⟨-34255616, 0⟩, ⟨-3214272, 0⟩⟩,
  ⟨⟨-3212648, 0⟩, ⟨-522159, 0⟩⟩,
  ⟨⟨-522015, 0⟩, ⟨-494291, 2⟩⟩,
  ⟨⟨-123551, 0⟩, ⟨-38273, 0⟩⟩,
  ⟨⟨-306145, 3⟩, ⟨-231321, 4⟩⟩,
  ⟨⟨-462599, 5⟩, ⟨-406495, 6⟩⟩,
  ⟨⟨-406465, 6⟩, ⟨-25101, 3⟩⟩,
  ⟨⟨-50199, 4⟩, ⟨-435521, 8⟩⟩,
  ⟨⟨-435499, 8⟩, ⟨-509077, 9⟩⟩,
  ⟨⟨-3977, 2⟩, ⟨-316345, 9⟩⟩,
  ⟨⟨-316333, 9⟩, ⟨-413637, 10⟩⟩,
  ⟨⟨-51703, 7⟩, ⟨-282173, 10⟩⟩,
  ⟨⟨-70541, 8⟩, ⟨-399073, 11⟩⟩,
  ⟨⟨-399063, 11⟩, ⟨-290985, 11⟩⟩,
  ⟨⟨-145489, 10⟩, ⟨-435661, 12⟩⟩,
  ⟨⟨-108913, 10⟩, ⟨-333653, 12⟩⟩,
  ⟨⟨-166823, 11⟩, ⟨-521285, 13⟩⟩,
  ⟨⟨-130319, 11⟩, ⟨-103589, 11⟩⟩,
  ⟨⟨-414349, 13⟩, ⟨-167217, 12⟩⟩,
  ⟨⟨-83607, 11⟩, ⟨-68399, 11⟩⟩,
  ⟨⟨-273591, 13⟩, ⟨-226527, 13⟩⟩,
  ⟨⟨-56631, 11⟩, ⟨-379141, 14⟩⟩,
  ⟨⟨-1481, 6⟩, ⟨-160165, 13⟩⟩,
  ⟨⟨-320325, 14⟩, ⟨-136487, 13⟩⟩,
  ⟨⟨-272971, 14⟩, ⟨-468833, 15⟩⟩,
  ⟨⟨-117207, 13⟩, ⟨-405421, 15⟩⟩,
  ⟨⟨-405417, 15⟩, ⟨-44099, 12⟩⟩,
  ⟨⟨-88197, 13⟩, ⟨-308745, 15⟩⟩,
  ⟨⟨-308741, 15⟩, ⟨-271589, 15⟩⟩,
  ⟨⟨-135793, 14⟩, ⟨-240025, 15⟩⟩,
  ⟨⟨-480045, 16⟩, ⟨-213031, 15⟩⟩,
  ⟨⟨-213029, 15⟩, ⟨-379609, 16⟩⟩,
  ⟨⟨-379605, 16⟩, ⟨-339405, 16⟩⟩,
  ⟨⟨-169701, 15⟩, ⟨-76107, 14⟩⟩,
  ⟨⟨-304425, 16⟩, ⟨-273847, 16⟩⟩,
  ⟨⟨-68461, 14⟩, ⟨-246985, 16⟩⟩,
  ⟨⟨-246983, 16⟩, ⟨-446575, 17⟩⟩,
  ⟨⟨-446571, 17⟩, ⟨-404595, 17⟩⟩,
  ⟨⟨-404591, 17⟩, ⟨-367271, 17⟩⟩,
  ⟨⟨-367267, 17⟩, ⟨-333967, 17⟩⟩,
  ⟨⟨-83491, 15⟩, ⟨-152077, 16⟩⟩,
  ⟨⟨-38019, 14⟩, ⟨-34673, 14⟩⟩,
  ⟨⟨-138691, 16⟩, ⟨-506549, 18⟩⟩,
  ⟨⟨-506545, 18⟩, ⟨-115751, 16⟩⟩,
  ⟨⟨-57875, 15⟩, ⟨-423581, 18⟩⟩,
  ⟨⟨-211789, 17⟩, ⟨-193901, 17⟩⟩,
  ⟨⟨-387799, 18⟩, ⟨-177631, 17⟩⟩,
  ⟨⟨-88815, 16⟩, ⟨-325603, 18⟩⟩,
  ⟨⟨-10175, 13⟩, ⟨-298519, 18⟩⟩,
  ⟨⟨-298517, 18⟩, ⟨-273743, 18⟩⟩,
  ⟨⟨-68435, 16⟩, ⟨-502077, 19⟩⟩,
  ⟨⟨-502073, 19⟩, ⟨-230203, 18⟩⟩,
  ⟨⟨-460403, 19⟩, ⟨-422109, 19⟩⟩,
  ⟨⟨-211053, 18⟩, ⟨-386869, 19⟩⟩,
  ⟨⟨-193433, 18⟩, ⟨-44301, 16⟩⟩,
  ⟨⟨-354405, 19⟩, ⟨-324473, 19⟩⟩,
  ⟨⟨-162235, 18⟩, ⟨-296845, 19⟩⟩,
  ⟨⟨-148421, 18⟩, ⟨-135663, 18⟩⟩,
  ⟨⟨-67831, 17⟩, ⟨-247743, 19⟩⟩,
  ⟨⟨-247741, 19⟩, ⟨-451875, 20⟩⟩,
  ⟨⟨-451871, 20⟩, ⟨-205769, 19⟩⟩,
  ⟨⟨-411535, 20⟩, ⟨-374221, 20⟩⟩,
  ⟨⟨-374217, 20⟩, ⟨-339699, 20⟩⟩,
  ⟨⟨-21231, 16⟩, ⟨-307767, 20⟩⟩,
  ⟨⟨-76941, 18⟩, ⟨-69559, 18⟩⟩,
  ⟨⟨-278233, 20⟩, ⟨-250943, 20⟩⟩,
  ⟨⟨-250941, 20⟩, ⟨-451469, 21⟩⟩,
  ⟨⟨-451465, 21⟩, ⟨-25309, 17⟩⟩,
  ⟨⟨-101235, 19⟩, ⟨-90515, 19⟩⟩,
  ⟨⟨-45257, 18⟩, ⟨-322583, 21⟩⟩,
  ⟨⟨-322579, 21⟩, ⟨-8947, 16⟩⟩,
  ⟨⟨-286301, 21⟩, ⟨-506059, 22⟩⟩,
  ⟨⟨-253027, 21⟩, ⟨-445159, 22⟩⟩,
  ⟨⟨-445155, 22⟩, ⟨-194789, 21⟩⟩,
  ⟨⟨-194787, 21⟩, ⟨-339007, 22⟩⟩,
  ⟨⟨-84751, 20⟩, ⟨-146577, 21⟩⟩,
  ⟨⟨-293151, 22⟩, ⟨-251747, 22⟩⟩,
  ⟨⟨-503489, 23⟩, ⟨-214529, 22⟩⟩,
  ⟨⟨-429053, 23⟩, ⟨-362507, 23⟩⟩,
  ⟨⟨-181251, 22⟩, ⟨-303367, 23⟩⟩,
  ⟨⟨-151681, 22⟩, ⟨-251175, 23⟩⟩,
  ⟨⟨-502343, 24⟩, ⟨-205483, 23⟩⟩,
  ⟨⟨-25685, 20⟩, ⟨-331697, 24⟩⟩,
  ⟨⟨-331691, 24⟩, ⟨-131829, 23⟩⟩,
  ⟨⟨-131827, 23⟩, ⟨-102983, 23⟩⟩,
  ⟨⟨-411925, 25⟩, ⟨-78869, 23⟩⟩,
  ⟨⟨-157735, 24⟩, ⟨-236167, 25⟩⟩,
  ⟨⟨-118081, 24⟩, ⟨-344405, 26⟩⟩,
  ⟨⟨-172199, 25⟩, ⟨-243541, 26⟩⟩,
  ⟨⟨-487071, 27⟩, ⟨-332281, 27⟩⟩,
  ⟨⟨-20767, 23⟩, ⟨-434475, 28⟩⟩,
  ⟨⟨-13577, 23⟩, ⟨-134995, 27⟩⟩,
  ⟨⟨-134991, 27⟩, ⟨-315587, 29⟩⟩,
  ⟨⟨-315577, 29⟩, ⟨-21389, 26⟩⟩,
  ⟨⟨-85553, 28⟩, ⟨-42267, 28⟩⟩,
  ⟨⟨-338123, 31⟩, ⟨-297093, 32⟩⟩,
  ⟨⟨-37135, 29⟩, ⟨-224461, 33⟩⟩,
  ⟨⟨-112225, 32⟩, ⟨-139031, 34⟩⟩,
  ⟨⟨-139023, 34⟩, ⟨-263261, 37⟩⟩,
  ⟨⟨-263245, 37⟩, ⟨-342133, 40⟩⟩,
  ⟨⟨-171055, 39⟩, ⟨-256493, 43⟩⟩,
  ⟨⟨-512949, 44⟩, ⟨-328667, 48⟩⟩,
  ⟨⟨-164321, 47⟩, ⟨-203643, 54⟩⟩,
  ⟨⟨-203627, 54⟩, ⟨-281303, 65⟩⟩,
  ⟨⟨-281279, 65⟩, ⟨-488941, 85⟩⟩,
  ⟨⟨-488895, 85⟩, ⟨-262149, 131⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private def eulerianCoefficients : List ℤ := [
  0x1, 0x1ffffffffffffffffffffffffff8e, 0x89427101b5c7bd0b38cf2cda6489dc1118d2ad53d316c,
  0x3fffffffffc2e069ad3d0d0dcdcd53be06bf3a9c0062f22ed0ac786da, 0x5329cc9697b5ffa2c345992e300374758df05ea9f7786367b18d3471e0da0516ec, 0x11284dfb2e1bdc2d340e0f209836e72efcdadb3e55b5be2a1f1dd08e1bd0675250c0ccc30e,
  0x258f342937329276796bb57f8640418da71d64af3f852817e9506034c4735356526b23bdebc11d74, 0x7ffef46390e52657a8f761b30c4816aa4adaf969b42b64bec4d6bb692fa3bff081f2e2ce27d16b557faca, 0x49949e35fc548e88c79b59141488b9f76fcc1a37c9ef68a8e9c237434492becfc35002e4d1bb499e2a3aeda1aa,
  0xa632d435747ca3c49dd85c7434f881b5c05f121ff3c7b521b487a80b05c821be0278e0c28fd548d1d065414dfb0182, 0x7873ae007b8fa23a51932e33abf100b4b539e5816d8b1a9696cdf7c82f125de8e7f6a39d3226af1289e65fde5358e44624, 0x221ae81c3d253028df225a62d82002e2cae4329dd321a2976a3719d684cf79b9cc2de76c6cbbb7d81a64df3837ebdea49e5ff6,
  0x460b812e512d2f9ff83698e059d1d433659aa5b659f805d94ad2ad48f4f250e83ad9fe3fbbe053744ab99ef3b49af4b4481bd705c, 0x4927fa88d264081c112b33133880e061a69a0f1eaa45e917a14a908ea1411738764c3e72948d55180467a1b1f981d8664ba8ac94d212, 0x2a86ad56e8e77df3939c5f385954cb43b758194f6b3ba1222fe4b45e3662192597a01bdd0f1ebfd90a369ac5952da6672e1bc555e4dc53c,
  0xec99e3cd24a8e1f2b787c311822de629cbbc558b876ee7f09ed31fc170fef17062bfe25d48b66c9019ed220c716817d13a2b2a04d716c0fb6, 0x342bf039bd7d987f434ffd9e3dac49842f630a58feadff577beb42aff8ba0d3725d4af3e995b7d1a5031461060bef95f34a643eed858cea1c2bb, 0x7a6fbee0552b154a03a1e3cd2a28ba5f61f0699964180796ff5625e4f2cb21d4fad4ce9214d8d628e50601bd26708b49ffb0fa33182938f614e104,
  0xc6da12bda5b3a27c284c72e55f768c6b15b7ad7b31b29dc17e61d6045acfa1a5f348bb2fce3ff0a3dbd363c6da101f34cd3738088f065d1146a01828, 0xe70a9ff618e9491bca7e88643fe8c1fbb05b8e5982a0542621d63cc23caea9fec012e9e2e6455083aff2849eef279244a9118356bf1628215c020c2c2c, 0xc57ecb1ccc4d135721c8be4b2ba06e9f0f76dad436b394a8e5bc6b79fdcf17f79dd6bbe160fb4612d5de97a578b534e65a2757f5f0fadde6999806147d48,
  0x7f33b6ed617b770de824cf34a495e7e1eb9e1ce041b661e70ca4e12bb160358459e9c041829be002c14a5edde84b1d9f9c19de1371fcaa494ef65cbc9ea3c4, 0x3f0238f4cf8f38e1754bab643c215d30129fca2a278d94fe4a188fc964291c4d7b10f1b5520b06d36e0404fb64cd8e4bfb640ad1f5cfc2ed89f74e704fda2418, 0x186ec24783a337ff87fba55106ecd1c9f1b45ae607a9c7607742f0996cf211d85c6dede000d6b43b740aa889de6f560dbdd67fa820e6389228c4edbfdab0d2f28c,
  0x78826c02605d14812e8e71b52e12b9ac6ef4c3b6c75b168633326e9dde7606547202f7bdc89f2b287452bf815572770505a0da718b8ff04c26ded7f218c5d249a04, 0x1def45d4eb47ca49c41c01f5e7fef4497905bd3d100b38cb5bf73b45b71146e7f3a3531c6b6f451fc5b634119224e36355470cec21d07fd14b21059857eba236f2bac, 0x61034f618d23ac1b2c6013d1e99c658f15e9def78b64ecbf1313fc55c9ae17777facedfa85e832e35c2f86221ff93736596ef6ad0f60f142e56cf2897efcbf9f59a958,
  0x10313ea30e628ab0f72a0706c9a8212629dde4b4f51dafe134fe90a3cf3a454ea2dc0dfdfcbb22a76ee10c59ee316312ec6d2a70bc350fa4d365ee527df82432217d0c24, 0x23f7aa142456b4267c7385721b7de153812802e7eca5927e828b61d6996a85f66cdaf73e5e185e8cae6cb5d99f47df765925b4d783f6e386fb321ffbeb90721f9fff0c388, 0x4301e4071e0e9dfd1032c0065b1193bbc72c072aaffcbc5c785ee2dec57e8f0731cc516f557fe3fed67e73cb06c66e4ad4c2f5b1d0013fdf58498a3278c12588fc3bcd8b4c,
  0x697bd3d664bc67c69dbdb3a9be0ad3fcc1778853bc34b9020383633b2eb29d25aae84ec4d692610a7a9c61b99988a8b939976c9bd3b4dee5ec784ba53d3b1a13f8d904790e8, 0x8d4133cf4a73fb6d330a816355156de71640580790363e912d421d96df768b36b916cbdc00caad01e30f1d4b99e8be23d908486fbefc2039373935a31f43dd48732907d60464, 0xa1e11ae78f6b424a1ba2755cdb428eaa19220a728ebeffcb8cdc4749de5b8d0c057486a3f91d9a32d6dcf8c45f19da5fb5f3d24c27d89a1cacc5eebec7ee5f9e7b1839203d4c9,
  0x9fa10ff13f06ae82da123fc4d341871269b32e7b65109877c219cdab3b3e64c3ba1f35419c556534ba890ae1f424485f46b12792ef5ae20a95d64f3f71fc2f89f6e9deef80421a, 0x881d15182617bce28c20267a084a13ee5946fc07f9907dc673737ce4f3ad7bced1d2fb11a7b4433a7c62394962f404c9d53523913a0caa6439be3d96df22cbf0174d600a2b66a64, 0x64ceda8502df08b084b7a4a9abac3aa5f6e26e5cd90344825beccf199c31142580fa0673fbb6a1f050974c7ba76ac82af3f09cb9f9af228c8a2cd3022fac566a8fa1696c673002de,
  0x411c3b2f31afc9a3702655b39c0fe6a306d4fd1bfabdf65f533e5e426251bad541155e6b93b2db2014c51c8ac7584689de74fea6ce41aaab21ac84cc685aa7911b057f8f7855a3604, 0x24cf402ef311af66c72fc3aeb08e194f4d8e9ec6c0b85ac78b4211925964f467ff0580f5966034393ae6933daccb5c699894cc6a4a60d952118f76eeaf77f444936da46a993674cc5a, 0x1246a3bcbe5f5d8898fe956ffa6b632f0e5acbb117b074b1f99545c1246e5becf608bab8fe7eb38cf1a830deca115a916082697ebef02c1acea332341355284370c6f1c66a584b8cb3c,
  0x7fe482d6b14443ec1405ed97b106115598d380d538dada9f45983d2f6ac5d99a5f8badb72347bd947162aa1a834c059b8025007d83e883e1dcb1e436f52ca4fd3af332a39972c82996e, 0x31690ea932d033f438daaca6a2f4baf1b8c045c7842b51989f750d6669f10393398bf3f31a05b032cf71d606209d7ceda0be812fe7a0be7494a2e77625c6c45d5c193a6d6dc1f755a2f6, 0x10e79c1f8c28bbda73f5b53f5391dc8c7eb134ce4147632fb5807b7aa4f3318f5d855b8f8bd94f0914fbdc22a3b145fc3dbcdaf837f7dd080bfd01f7ff9d78219d01180a8fdd406e53b06,
  0x52226a2345f887b02aa91815c3a2ec04b77f6d28963fd4ccfed68396bdb617fa915195f7d7d9cd48838a86808476f65388bdb1f6e63fd9f562d692e67a0cfd86bfb3319c8f8d00ea256ac, 0x162eef2f6ef537d1a3a8b7b3109c2d2f7b4333830a2e5609308725fb3726392fa261841f028d4a3215e0a110463ab70f213435aaf672c8eedd9bc75783832e0900891f121da49c0a79dce2, 0x556bc2ff86cd53ef9d3b617843d27b03587ae21934efdefd03e35b8c8c41967846112a59a60635d19415ece317a61329f7ef72136a9224c2d5911a2c81cc4998f13b9dffe50493997b6d34,
  0x1259869194f5b545b636cf32e2577d17d80d1a961102f5e2079e1b97db6e2679539679763fc076ee52622587e041fd7d28b942472dfe0af68958e41a90bb5f161c531e9daade6e278020af6, 0x38610b5c705817cb29018b48367c69791b20469b23f3afdc9da8e141085fec570ec3c6914c0c469e9330c26bb940d21db13645a197001fee8e5ef2ba24cfbf113cfda93b3fc33ddd0b72d74, 0x9b0f1d9e1e74ebad358f5aa8d80f4ae764ef710a1a5a789ceaf0b2a1d764016cb0861a06dba29f9d522481e1534d1cd0205c53e9a4b0634563da9b9ed706458ef3526283ad7203a782342e2,
  0x17e32453b034dc29444ce49f21925e24607cfc57582fcd9f67e421169562002879ca0d41aeec7e792d43f94580389114f015a98abc5e63820111b40d1b897b06960fbfba55cc32940106987b, 0x34d2b250785e18d44b25c71d4a0aff05fd91ac3632345ad329df9e82e7d23ef2c751f924aa03fcab7ca1f89b6f08eed4c32c89604263940ba650fbd0959a70af1b99619bf8e541b9dcd02658, 0x68e478d654f85b0d87243ead244a3fc51abf171241a72529b77d68035c59a590a33eefaf1416be5282e5c14d85ece284619b75207a8347c6bcb66def4b8cfe4d0ca6df9f4020e9b2c67e8870,
  0xbb2f1b95bc13e7103a306131da4bdae49dc96a3c7e05c2276ae3916609dfb4b9c04d8a839ac4dd3646fc72d2fb893b7a3939a62a35d2953e21d437193be5f148aebe44372f141a3a0ea3c1c8, 0x12c62f1c431b1dde9db26fae6488c2970e207b8edc0013bfb10c71b3a47eaa380375269c2c0ec1fe8ff085cd23810272c70155cb4299a3ec42788bd52430d7c94ede7c36dffbb3165436294b0, 0x1b1b83f11a14dd84bcd4abb6ae69d993e2727d4b0def6e3b9b9e2dd91822e2d95e264a2b3cf0aec797cc157bf5ad1f669e169fe6e5fa6a73a931d2f8d408aa42a55bf614d09b63ad7507ea3d8,
  0x233ae02f8d4c9f80e4e60056c4ed885916daff0fad8c7e00614550058ff20fc09e02975d2f195e2bd86586ee2c8dff4fcdcb91e3534db7cd695585eb1b52f3e1da9e4a22dc0ac7998f46ced10, 0x29397dd3a22d04ea8a1e52ed6ef46ca3153383fb61f6f81c1df21e5bf731ddd2389a7baf741e12e9035f884f217f15aee4e6af5e6754dc8fa86740e5d62fa1ec5d1f24c4d159af8e389387108, 0x2b70cadd2b4d9913b83eac2e17890d0261ecb16051f41b637160424835b5757ac0e5a5c5a88d20c26009ef790eca039cfeef90ac6cec5f05639922b4a433838406b4d9338d6badcde95d7e2b8,
  0x29397dd3a22d04ea8a1e52ed6ef46ca3153383fb61f6f81c1df21e5bf731ddd2389a7baf741e12e9035f884f217f15aee4e6af5e6754dc8fa86740e5d62fa1ec5d1f24c4d159af8e389387108, 0x233ae02f8d4c9f80e4e60056c4ed885916daff0fad8c7e00614550058ff20fc09e02975d2f195e2bd86586ee2c8dff4fcdcb91e3534db7cd695585eb1b52f3e1da9e4a22dc0ac7998f46ced10, 0x1b1b83f11a14dd84bcd4abb6ae69d993e2727d4b0def6e3b9b9e2dd91822e2d95e264a2b3cf0aec797cc157bf5ad1f669e169fe6e5fa6a73a931d2f8d408aa42a55bf614d09b63ad7507ea3d8,
  0x12c62f1c431b1dde9db26fae6488c2970e207b8edc0013bfb10c71b3a47eaa380375269c2c0ec1fe8ff085cd23810272c70155cb4299a3ec42788bd52430d7c94ede7c36dffbb3165436294b0, 0xbb2f1b95bc13e7103a306131da4bdae49dc96a3c7e05c2276ae3916609dfb4b9c04d8a839ac4dd3646fc72d2fb893b7a3939a62a35d2953e21d437193be5f148aebe44372f141a3a0ea3c1c8, 0x68e478d654f85b0d87243ead244a3fc51abf171241a72529b77d68035c59a590a33eefaf1416be5282e5c14d85ece284619b75207a8347c6bcb66def4b8cfe4d0ca6df9f4020e9b2c67e8870,
  0x34d2b250785e18d44b25c71d4a0aff05fd91ac3632345ad329df9e82e7d23ef2c751f924aa03fcab7ca1f89b6f08eed4c32c89604263940ba650fbd0959a70af1b99619bf8e541b9dcd02658, 0x17e32453b034dc29444ce49f21925e24607cfc57582fcd9f67e421169562002879ca0d41aeec7e792d43f94580389114f015a98abc5e63820111b40d1b897b06960fbfba55cc32940106987b, 0x9b0f1d9e1e74ebad358f5aa8d80f4ae764ef710a1a5a789ceaf0b2a1d764016cb0861a06dba29f9d522481e1534d1cd0205c53e9a4b0634563da9b9ed706458ef3526283ad7203a782342e2,
  0x38610b5c705817cb29018b48367c69791b20469b23f3afdc9da8e141085fec570ec3c6914c0c469e9330c26bb940d21db13645a197001fee8e5ef2ba24cfbf113cfda93b3fc33ddd0b72d74, 0x1259869194f5b545b636cf32e2577d17d80d1a961102f5e2079e1b97db6e2679539679763fc076ee52622587e041fd7d28b942472dfe0af68958e41a90bb5f161c531e9daade6e278020af6, 0x556bc2ff86cd53ef9d3b617843d27b03587ae21934efdefd03e35b8c8c41967846112a59a60635d19415ece317a61329f7ef72136a9224c2d5911a2c81cc4998f13b9dffe50493997b6d34,
  0x162eef2f6ef537d1a3a8b7b3109c2d2f7b4333830a2e5609308725fb3726392fa261841f028d4a3215e0a110463ab70f213435aaf672c8eedd9bc75783832e0900891f121da49c0a79dce2, 0x52226a2345f887b02aa91815c3a2ec04b77f6d28963fd4ccfed68396bdb617fa915195f7d7d9cd48838a86808476f65388bdb1f6e63fd9f562d692e67a0cfd86bfb3319c8f8d00ea256ac, 0x10e79c1f8c28bbda73f5b53f5391dc8c7eb134ce4147632fb5807b7aa4f3318f5d855b8f8bd94f0914fbdc22a3b145fc3dbcdaf837f7dd080bfd01f7ff9d78219d01180a8fdd406e53b06,
  0x31690ea932d033f438daaca6a2f4baf1b8c045c7842b51989f750d6669f10393398bf3f31a05b032cf71d606209d7ceda0be812fe7a0be7494a2e77625c6c45d5c193a6d6dc1f755a2f6, 0x7fe482d6b14443ec1405ed97b106115598d380d538dada9f45983d2f6ac5d99a5f8badb72347bd947162aa1a834c059b8025007d83e883e1dcb1e436f52ca4fd3af332a39972c82996e, 0x1246a3bcbe5f5d8898fe956ffa6b632f0e5acbb117b074b1f99545c1246e5becf608bab8fe7eb38cf1a830deca115a916082697ebef02c1acea332341355284370c6f1c66a584b8cb3c,
  0x24cf402ef311af66c72fc3aeb08e194f4d8e9ec6c0b85ac78b4211925964f467ff0580f5966034393ae6933daccb5c699894cc6a4a60d952118f76eeaf77f444936da46a993674cc5a, 0x411c3b2f31afc9a3702655b39c0fe6a306d4fd1bfabdf65f533e5e426251bad541155e6b93b2db2014c51c8ac7584689de74fea6ce41aaab21ac84cc685aa7911b057f8f7855a3604, 0x64ceda8502df08b084b7a4a9abac3aa5f6e26e5cd90344825beccf199c31142580fa0673fbb6a1f050974c7ba76ac82af3f09cb9f9af228c8a2cd3022fac566a8fa1696c673002de,
  0x881d15182617bce28c20267a084a13ee5946fc07f9907dc673737ce4f3ad7bced1d2fb11a7b4433a7c62394962f404c9d53523913a0caa6439be3d96df22cbf0174d600a2b66a64, 0x9fa10ff13f06ae82da123fc4d341871269b32e7b65109877c219cdab3b3e64c3ba1f35419c556534ba890ae1f424485f46b12792ef5ae20a95d64f3f71fc2f89f6e9deef80421a, 0xa1e11ae78f6b424a1ba2755cdb428eaa19220a728ebeffcb8cdc4749de5b8d0c057486a3f91d9a32d6dcf8c45f19da5fb5f3d24c27d89a1cacc5eebec7ee5f9e7b1839203d4c9,
  0x8d4133cf4a73fb6d330a816355156de71640580790363e912d421d96df768b36b916cbdc00caad01e30f1d4b99e8be23d908486fbefc2039373935a31f43dd48732907d60464, 0x697bd3d664bc67c69dbdb3a9be0ad3fcc1778853bc34b9020383633b2eb29d25aae84ec4d692610a7a9c61b99988a8b939976c9bd3b4dee5ec784ba53d3b1a13f8d904790e8, 0x4301e4071e0e9dfd1032c0065b1193bbc72c072aaffcbc5c785ee2dec57e8f0731cc516f557fe3fed67e73cb06c66e4ad4c2f5b1d0013fdf58498a3278c12588fc3bcd8b4c,
  0x23f7aa142456b4267c7385721b7de153812802e7eca5927e828b61d6996a85f66cdaf73e5e185e8cae6cb5d99f47df765925b4d783f6e386fb321ffbeb90721f9fff0c388, 0x10313ea30e628ab0f72a0706c9a8212629dde4b4f51dafe134fe90a3cf3a454ea2dc0dfdfcbb22a76ee10c59ee316312ec6d2a70bc350fa4d365ee527df82432217d0c24, 0x61034f618d23ac1b2c6013d1e99c658f15e9def78b64ecbf1313fc55c9ae17777facedfa85e832e35c2f86221ff93736596ef6ad0f60f142e56cf2897efcbf9f59a958,
  0x1def45d4eb47ca49c41c01f5e7fef4497905bd3d100b38cb5bf73b45b71146e7f3a3531c6b6f451fc5b634119224e36355470cec21d07fd14b21059857eba236f2bac, 0x78826c02605d14812e8e71b52e12b9ac6ef4c3b6c75b168633326e9dde7606547202f7bdc89f2b287452bf815572770505a0da718b8ff04c26ded7f218c5d249a04, 0x186ec24783a337ff87fba55106ecd1c9f1b45ae607a9c7607742f0996cf211d85c6dede000d6b43b740aa889de6f560dbdd67fa820e6389228c4edbfdab0d2f28c,
  0x3f0238f4cf8f38e1754bab643c215d30129fca2a278d94fe4a188fc964291c4d7b10f1b5520b06d36e0404fb64cd8e4bfb640ad1f5cfc2ed89f74e704fda2418, 0x7f33b6ed617b770de824cf34a495e7e1eb9e1ce041b661e70ca4e12bb160358459e9c041829be002c14a5edde84b1d9f9c19de1371fcaa494ef65cbc9ea3c4, 0xc57ecb1ccc4d135721c8be4b2ba06e9f0f76dad436b394a8e5bc6b79fdcf17f79dd6bbe160fb4612d5de97a578b534e65a2757f5f0fadde6999806147d48,
  0xe70a9ff618e9491bca7e88643fe8c1fbb05b8e5982a0542621d63cc23caea9fec012e9e2e6455083aff2849eef279244a9118356bf1628215c020c2c2c, 0xc6da12bda5b3a27c284c72e55f768c6b15b7ad7b31b29dc17e61d6045acfa1a5f348bb2fce3ff0a3dbd363c6da101f34cd3738088f065d1146a01828, 0x7a6fbee0552b154a03a1e3cd2a28ba5f61f0699964180796ff5625e4f2cb21d4fad4ce9214d8d628e50601bd26708b49ffb0fa33182938f614e104,
  0x342bf039bd7d987f434ffd9e3dac49842f630a58feadff577beb42aff8ba0d3725d4af3e995b7d1a5031461060bef95f34a643eed858cea1c2bb, 0xec99e3cd24a8e1f2b787c311822de629cbbc558b876ee7f09ed31fc170fef17062bfe25d48b66c9019ed220c716817d13a2b2a04d716c0fb6, 0x2a86ad56e8e77df3939c5f385954cb43b758194f6b3ba1222fe4b45e3662192597a01bdd0f1ebfd90a369ac5952da6672e1bc555e4dc53c,
  0x4927fa88d264081c112b33133880e061a69a0f1eaa45e917a14a908ea1411738764c3e72948d55180467a1b1f981d8664ba8ac94d212, 0x460b812e512d2f9ff83698e059d1d433659aa5b659f805d94ad2ad48f4f250e83ad9fe3fbbe053744ab99ef3b49af4b4481bd705c, 0x221ae81c3d253028df225a62d82002e2cae4329dd321a2976a3719d684cf79b9cc2de76c6cbbb7d81a64df3837ebdea49e5ff6,
  0x7873ae007b8fa23a51932e33abf100b4b539e5816d8b1a9696cdf7c82f125de8e7f6a39d3226af1289e65fde5358e44624, 0xa632d435747ca3c49dd85c7434f881b5c05f121ff3c7b521b487a80b05c821be0278e0c28fd548d1d065414dfb0182, 0x49949e35fc548e88c79b59141488b9f76fcc1a37c9ef68a8e9c237434492becfc35002e4d1bb499e2a3aeda1aa,
  0x7ffef46390e52657a8f761b30c4816aa4adaf969b42b64bec4d6bb692fa3bff081f2e2ce27d16b557faca, 0x258f342937329276796bb57f8640418da71d64af3f852817e9506034c4735356526b23bdebc11d74, 0x11284dfb2e1bdc2d340e0f209836e72efcdadb3e55b5be2a1f1dd08e1bd0675250c0ccc30e,
  0x5329cc9697b5ffa2c345992e300374758df05ea9f7786367b18d3471e0da0516ec, 0x3fffffffffc2e069ad3d0d0dcdcd53be06bf3a9c0062f22ed0ac786da, 0x89427101b5c7bd0b38cf2cda6489dc1118d2ad53d316c,
  0x1ffffffffffffffffffffffffff8e, 0x1]

private theorem eulerianCoefficients_eq : descentCoeffs 113 = eulerianCoefficients := by
  decide +kernel

private theorem upper : upperOK (descentCoeffs 113) first gaps = true := by
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

private theorem lower (i : Fin (lastRepresentative 114 - 2)) :
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

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 114) :
    StrictNegativeInterlacing (originalQuotient 114 k) (eulerian 113) 111 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N114
