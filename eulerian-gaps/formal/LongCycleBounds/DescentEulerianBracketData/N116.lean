import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentPackedData.C127L120.N116

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N116

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L120.N116 LongCycleBounds.DescentNecklace.Packed.C127L120.N116.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L120.N116 LongCycleBounds.DescentNecklace.Packed.C127L120.N116.rows

private theorem actual : RepresentativeChecks 116 previousNodes rows :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L120.N116 LongCycleBounds.DescentNecklace.Packed.C127L120.N116.dataChecks

private def first : LongCycleFinite.Dyadic := ⟨-41538374868278621028243970633760768, 0⟩

private def gaps : List Window := [
  ⟨⟨-41537027989515878534504880386605056, 0⟩, ⟨-178611635321607028736, 0⟩⟩,
  ⟨⟨-177458150867046760448, 0⟩, ⟨-239675281244160, 0⟩⟩,
  ⟨⟨-232602006978560, 0⟩, ⟨-139708596224, 0⟩⟩,
  ⟨⟨-128971177984, 0⟩, ⟨-1240862720, 0⟩⟩,
  ⟨⟨-1234362368, 0⟩, ⟨-46801792, 0⟩⟩,
  ⟨⟨-46741504, 0⟩, ⟨-4211840, 0⟩⟩,
  ⟨⟨-4209600, 0⟩, ⟨-663418, 0⟩⟩,
  ⟨⟨-663228, 0⟩, ⟨-306531, 1⟩⟩,
  ⟨⟨-306475, 1⟩, ⟨-372383, 3⟩⟩,
  ⟨⟨-372335, 3⟩, ⟨-276881, 4⟩⟩,
  ⟨⟨-138427, 3⟩, ⟨-120019, 4⟩⟩,
  ⟨⟨-60005, 3⟩, ⟨-234491, 6⟩⟩,
  ⟨⟨-234477, 6⟩, ⟨-125919, 6⟩⟩,
  ⟨⟨-503651, 8⟩, ⟨-291921, 8⟩⟩,
  ⟨⟨-72977, 6⟩, ⟨-180087, 8⟩⟩,
  ⟨⟨-11255, 4⟩, ⟨-467961, 10⟩⟩,
  ⟨⟨-233973, 9⟩, ⟨-317455, 10⟩⟩,
  ⟨⟨-317445, 10⟩, ⟨-13961, 6⟩⟩,
  ⟨⟨-446741, 11⟩, ⟨-324313, 11⟩⟩,
  ⟨⟨-324305, 11⟩, ⟨-483657, 12⟩⟩,
  ⟨⟨-241823, 11⟩, ⟨-184553, 11⟩⟩,
  ⟨⟨-369099, 12⟩, ⟨-35929, 9⟩⟩,
  ⟨⟨-287427, 12⟩, ⟨-455653, 13⟩⟩,
  ⟨⟨-455645, 13⟩, ⟨-366827, 13⟩⟩,
  ⟨⟨-366821, 13⟩, ⟨-149705, 12⟩⟩,
  ⟨⟨-299405, 13⟩, ⟨-494779, 14⟩⟩,
  ⟨⟨-123693, 12⟩, ⟨-25831, 10⟩⟩,
  ⟨⟨-413291, 14⟩, ⟨-348611, 14⟩⟩,
  ⟨⟨-348607, 14⟩, ⟨-296631, 14⟩⟩,
  ⟨⟨-296627, 14⟩, ⟨-63599, 12⟩⟩,
  ⟨⟨-254393, 14⟩, ⟨-109865, 13⟩⟩,
  ⟨⟨-439455, 15⟩, ⟨-382015, 15⟩⟩,
  ⟨⟨-191005, 14⟩, ⟨-334017, 15⟩⟩,
  ⟨⟨-334013, 15⟩, ⟨-293591, 15⟩⟩,
  ⟨⟨-73397, 13⟩, ⟨-518595, 16⟩⟩,
  ⟨⟨-259295, 15⟩, ⟨-460017, 16⟩⟩,
  ⟨⟨-115003, 14⟩, ⟨-409673, 16⟩⟩,
  ⟨⟨-409669, 16⟩, ⟨-366159, 16⟩⟩,
  ⟨⟨-91539, 14⟩, ⟨-164171, 15⟩⟩,
  ⟨⟨-328339, 16⟩, ⟨-147657, 15⟩⟩,
  ⟨⟨-295311, 16⟩, ⟨-266329, 16⟩⟩,
  ⟨⟨-266327, 16⟩, ⟨-120391, 15⟩⟩,
  ⟨⟨-60195, 14⟩, ⟨-109087, 15⟩⟩,
  ⟨⟨-436345, 17⟩, ⟨-99045, 15⟩⟩,
  ⟨⟨-396177, 17⟩, ⟨-180183, 16⟩⟩,
  ⟨⟨-360363, 17⟩, ⟨-164163, 16⟩⟩,
  ⟨⟨-328323, 17⟩, ⟨-299573, 17⟩⟩,
  ⟨⟨-299571, 17⟩, ⟨-273693, 17⟩⟩,
  ⟨⟨-136845, 16⟩, ⟨-250333, 17⟩⟩,
  ⟨⟨-250331, 17⟩, ⟨-229195, 17⟩⟩,
  ⟨⟨-458387, 18⟩, ⟨-210019, 17⟩⟩,
  ⟨⟨-420035, 18⟩, ⟨-385167, 18⟩⟩,
  ⟨⟨-96291, 16⟩, ⟨-176697, 17⟩⟩,
  ⟨⟨-353391, 18⟩, ⟨-162193, 17⟩⟩,
  ⟨⟨-324383, 18⟩, ⟨-297851, 18⟩⟩,
  ⟨⟨-37231, 15⟩, ⟨-273539, 18⟩⟩,
  ⟨⟨-273537, 18⟩, ⟨-502453, 19⟩⟩,
  ⟨⟨-502449, 19⟩, ⟨-3605, 12⟩⟩,
  ⟨⟨-461437, 19⟩, ⟨-423695, 19⟩⟩,
  ⟨⟨-105923, 17⟩, ⟨-388915, 19⟩⟩,
  ⟨⟨-24307, 15⟩, ⟨-11151, 14⟩⟩,
  ⟨⟨-356829, 19⟩, ⟨-327209, 19⟩⟩,
  ⟨⟨-327207, 19⟩, ⟨-37479, 16⟩⟩,
  ⟨⟨-149915, 18⟩, ⟨-137257, 18⟩⟩,
  ⟨⟨-274511, 19⟩, ⟨-62771, 17⟩⟩,
  ⟨⟨-125541, 18⟩, ⟨-458787, 20⟩⟩,
  ⟨⟨-458783, 20⟩, ⟨-26163, 16⟩⟩,
  ⟨⟨-418605, 20⟩, ⟨-23837, 16⟩⟩,
  ⟨⟨-381389, 20⟩, ⟨-346913, 20⟩⟩,
  ⟨⟨-173455, 19⟩, ⟨-314977, 20⟩⟩,
  ⟨⟨-314975, 20⟩, ⟨-142701, 19⟩⟩,
  ⟨⟨-35675, 17⟩, ⟨-64507, 18⟩⟩,
  ⟨⟨-129013, 19⟩, ⟨-465405, 21⟩⟩,
  ⟨⟨-465401, 21⟩, ⟨-104647, 19⟩⟩,
  ⟨⟨-52323, 18⟩, ⟨-93839, 19⟩⟩,
  ⟨⟨-375353, 21⟩, ⟨-2621, 14⟩⟩,
  ⟨⟨-335485, 21⟩, ⟨-149387, 20⟩⟩,
  ⟨⟨-298771, 21⟩, ⟨-265025, 21⟩⟩,
  ⟨⟨-132511, 20⟩, ⟨-468135, 22⟩⟩,
  ⟨⟨-234065, 21⟩, ⟨-205739, 21⟩⟩,
  ⟨⟨-205737, 21⟩, ⟨-359777, 22⟩⟩,
  ⟨⟨-359773, 22⟩, ⟨-312749, 22⟩⟩,
  ⟨⟨-312745, 22⟩, ⟨-135065, 21⟩⟩,
  ⟨⟨-270127, 22⟩, ⟨-463339, 23⟩⟩,
  ⟨⟨-231667, 22⟩, ⟨-394255, 23⟩⟩,
  ⟨⟨-197125, 22⟩, ⟨-166275, 22⟩⟩,
  ⟨⟨-166273, 22⟩, ⟨-277783, 23⟩⟩,
  ⟨⟨-277779, 23⟩, ⟨-459039, 24⟩⟩,
  ⟨⟨-459033, 24⟩, ⟨-374675, 24⟩⟩,
  ⟨⟨-374669, 24⟩, ⟨-150819, 23⟩⟩,
  ⟨⟨-301633, 24⟩, ⟨-239083, 24⟩⟩,
  ⟨⟨-478159, 25⟩, ⟨-93091, 23⟩⟩,
  ⟨⟨-186179, 24⟩, ⟨-142087, 24⟩⟩,
  ⟨⟨-284169, 25⟩, ⟨-423795, 26⟩⟩,
  ⟨⟨-211893, 25⟩, ⟨-307649, 26⟩⟩,
  ⟨⟨-153821, 25⟩, ⟨-432953, 27⟩⟩,
  ⟨⟨-432943, 27⟩, ⟨-146851, 26⟩⟩,
  ⟨⟨-146847, 26⟩, ⟨-95401, 26⟩⟩,
  ⟨⟨-381593, 28⟩, ⟨-470839, 29⟩⟩,
  ⟨⟨-470825, 29⟩, ⟨-34111, 26⟩⟩,
  ⟨⟨-136439, 28⟩, ⟨-293069, 30⟩⟩,
  ⟨⟨-146529, 29⟩, ⟨-71577, 29⟩⟩,
  ⟨⟨-286297, 31⟩, ⟨-248221, 32⟩⟩,
  ⟨⟨-496421, 33⟩, ⟨-369099, 34⟩⟩,
  ⟨⟨-369081, 34⟩, ⟨-112101, 34⟩⟩,
  ⟨⟨-112095, 34⟩, ⟨-414357, 38⟩⟩,
  ⟨⟨-103583, 36⟩, ⟨-261065, 40⟩⟩,
  ⟨⟨-32631, 37⟩, ⟨-375899, 44⟩⟩,
  ⟨⟨-5873, 38⟩, ⟨-113919, 47⟩⟩,
  ⟨⟨-227821, 48⟩, ⟨-130241, 54⟩⟩,
  ⟨⟨-520923, 56⟩, ⟨-39555, 63⟩⟩,
  ⟨⟨-158207, 65⟩, ⟨-434601, 86⟩⟩,
  ⟨⟨-3395, 79⟩, ⟨-262149, 133⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private def eulerianCoefficients : List ℤ := [
  0x1, 0x7ffffffffffffffffffffffffff8c, 0x4d355f90f6405a5ab3f4893ad88d8bc99df6817f25f469,
  0x3fffffffffdd03d0b2506ad70e126531d155dfdca8a46c4d5262d530b0, 0x81f14fac458c5f6e504938d93e8fc0897857ec3c86999db2c77fadff5da1b60766c, 0x269aaf8d99c812b59e5f06a13167c600362a05daad1da9767b0cdbb0319b51df4cdfb7d13d0,
  0x730695a638e3e90419847bd0bb6b6eb147411a488ebedb90f4324979e0e2917e9f68e54865df5c51c, 0x1fffcbe100315dd521a8460be37931c97054b2379338dca9ad3f2a7733b85033683626196dad4e64b7b56d0, 0x17483e9ea52501f450ff3871e007c3acb99ea45362726767006b0a55c1a4b52b90e34200ea619534eeaf5cd987d2,
  0x40ee1ae5a71c6d24d9a7d7177142df2ab75ada6adc4dea35804b4ca4f652cd9441988dffd74f10ea166be8c70bbd6778, 0x38f43daa39f27594bc0f300f50fa1e98f9a459122bd18bf35b41b1a2b79353e84305d016dd608a1219a6dcc877c729075d72, 0x1333827ec5f4eda4cf4b886ef80fa651e2b3c98e0822efa462a4a55b91b145e8f832b051deb61dc56f6c5c3a0771a339b051c590,
  0x2e52ee93fd5f71736322bb75cda4ced14416236e2ea16bd10f74f1c62bdb609dbdb31b1dc1f9c058d8b1e03b4d84f4bb66beb0a428c, 0x38317c6cf8d17f5494411aaccb781a7f6be4f44476b24bb8840c35b445d9c30d59dac111076fd56933e5df08830dc317316abaf5fb5810, 0x259474d19fb8b1be0b42e3f5f421dd313fcdc8a47e458ae28c28b1496a3fb0b13b08d74c50122f4f598d95372f699dd875eddf9da2e0bcc9c,
  0xee9ae4d7f24eb05a41aa88c714b3fc9d234f769a8f1897fe74bec7b55ae24ee73d4f57fd183e4fac5153ce9df76cbbe7de7c5f48eb2f241a3f0, 0x3ba1bb8df135c5545e0452cd267c2eea6f08cee395e85c286a70f946e9fd8035af4d77f63410be779c4cf8e06a0e7b016bcf3e74acb3c2a1f06fc3, 0x9daef1f581bdd61b288f6543fd8b55a0aca759a0646538f8207e93f11bdd77bb76154faafb39a028e09d4bb77a058e85a25e094dcb35850c90619544,
  0x11f1c6c442b48307518d7de9f2f2910b341c71fea757ba008c8bb17aa54d6445eefdb610d17eaa4ad284b02daa962bd42eeb6be18150465b1b6ce42152b, 0x1745e7deffd3eed6a10e86ff80d5e4d561eb8c02a51c3892b80d51e421a5c1292481fd9628fc3866c704ceb2004f35ee4d2ac915dd6429511f9ad8388faa0, 0x161fb1cfb34c58f3742fc274a99bec949d0b1b11813aa2c5a4850099fb38390e3e1b8ed95aac1d6befdb9afee4a948a86a078b833e13d8fbcde67444773dd08,
  0xfcba377105afcb3dfe8755431738ab8e02a8f81465f14db918937464dc1fb3af39d55d06fad1313e04384baf8717381648ea752e7ecbf0cfe38d1a4ac1d18be0, 0x8a61aede9c61c02775e44801fb3663a376d0b2c918d3941e4ef68b5ebb6f319bddc8915b2927a8d425932503206cd364b79c12c38fd9aa20e8e1a596ecf723b3a8, 0x3b2bfc136845feb06d30323a29f35a0be5ec1e98e804db59b08243f3b493a32b1ece549457f714fe0acefd64c3a47e8492d24cb74715c5b8c7bc3f9a8ca75bbe7e60,
  0x14128b2afbe14300c500ec0bc5df0a51bad2a95e4a89aa31f7973240bb4c64062c9ccdd691ed9b2a39cd02b3d5306b66ee25bf6b236732880aaa57920e308113628cf4, 0x57a09a9b89939f21d5fea214363294ba1757864f365c6d6515e56fc07953611922f8acc3776830cb3de12ed05e54e4d01f649f43ebd1c2f217114f1758f2174f49b7730, 0x1377211993629a2998f1b428637f193c1461f00733198252a35e6c10588b96d413f198f158948c93dd8b1089b428f78c22bd8297f2036df6ca6bd598314e673d7ea82c674,
  0x38eef26b804396ff772d986d0c30ab4fb8b0434f0b2d6ceb2a60160cd6fb854bfb7e722c38c5411bfd4bcf9b24208da1ad749e126bcf8051648ab02a264d1f3a1dbb396360, 0x8a59286e0d4510bbe74ba76387ddc6b2ce2912edcb424fc2469afb5fa211f4060ea2d111b9afde16789b49f7778383f1888c6769a639a9fe85d6cf2e91f00a68949220e09e8, 0x119b1308ff236bfb4f258675e1c9e8c77ef94dd69a8d8f888a7cec45d6f4c4bc7547810c733ceae6fd51f4bced75c687fdffb9895a583993521237095b19bfd74c0d8931d0ae0,
  0x1e441b004574ef91ef65553a163280778c7f81f80efb99be7de98ec75fc1e2f021be17775001ea8cfd051a265dc20c458ed43394a2a00ee17722e86a4b9e825e4d613eeed3d048, 0x2c3b177a3bfd952dbaa49d8d23e5033cf16154df5515c54e1bfc12756da357c6f39e1921bd65bc321e128c5050b77f47b2f5e940c0d0428931c41bca1fe916679821d0027d64da0, 0x3749f239d59cb2b8532ca0bc8ec42dfc3549d0351cd37278f45c4c2e6afc7268500e4cdcd963267c2bf5ca1b6bbec665e32edf542ebb843851aa9321c5c67773f64d6a95d8ce94b9,
  0x3b71ac1af5d27747c0a4156d5464125760cf2305a8fcedbba3b29e3519df2ae68a40ffbb8d8491e3684ccbcbd8bef92487613b8561c083664e4b910ff1f3a7a21237ede898a2c1eec, 0x373fb38e1158032272bc61577956e1870b635e3d6fc9af7b1c149f7236ce9e82c70e1f3ecc30c703aed95cc456d76b321acec7bdbbd5ded5feba389b7a0ae9a166f1fe6cb3dbada401, 0x2c97bffa0f42df88d91c2c6d9d4a5620fabb15e0814a10306d6e8bfdfda46da2e35be445326668e559519adb1ef7dde03dd625f0d362372c41eb5bd55e77148a30459da90313734a290,
  0x1f62c24eff511f806c16083515ddd6dd92136fbb48162a844e405bfc07cffd0c4ad2252af12c1c4b3d2a2141735b0b16519976381c6df78a7f7433db404138fc893d62a135848122b844, 0x135601904cb68acc7677ded45c766ffe7f5298d05e12f5d8c7a6f92470ee3e9587e61d3a4c5f45060a8f092fd78bddd17de5c35aa6f86dd6f5299179020c83bcd31ab78b70ffaffe72270, 0xa7682fd6a26229573a6e8cf8bf43cab453696522c8a2b86ea2bf346a2bb712ff0261ff5e106b99362d9c23f8c8cde4d6c600f0da29e469661ea6eebd030c2decad38dee0f931fef8230d4,
  0x4fd0221d12bc44fe5b8526952275c18b411f3447c9cfead0918d93e3f581ef23fef9b1ea0b67dc97c06921f4df8d2324f9d6f490723930e38e41d16a3442b14a68bb061f3469c2dca057f0, 0x219f37cbf6fbcac98b6ee416ce207293bc60fadb7995a1d5cb9c590bb056a1cc6e180fe1464b74898305080d17f34f40754c288a495ff1d752ea53ed1e7c83611b2c96208da8ec178010d6e, 0xc8c158dd951d1809a2910d55c6ceb0eb605a73f86c599425c10f118aa829e0358c025fc6cb9507d57b512359ef2496b2ef4e22397635ac539c4bc9fb38afc2b0e0051613728408d21b3b808,
  0x4286a3b2b21b8864f8c8793e307f32fd3ef4a6b3fa7dff5479c5f3258e4d312d457b8df22c243d2a6742de8b35daf250bc59fc2fe5b79e5529410f5a934ca12950a5c289602492f549cff98e, 0x139e1d51bb5032beea5372df1603758c10e2b3d6769c632942cb0ebd6326b201b6e8ae3884d53879e21c2206693700b850323eafebcbf3987fceda1972fea922cfe5dbafcdd3e40be6bd381b0, 0x52871261fc7f11d706f28574716a52d0bafde3e32a6aaf2422573815433e47fa19c5028a074e8514b56f04649ba42507ff4708e796ea61a65ce70c7a39a637d28119e9985e378e4b1fa96dc04,
  0x1361842bed69c4c3273a78c9f7c30b3740d5d2db55285bfd4e985505bb800337d4516ece6695573a41f8210e26fe859d2ea206de897c4c6bf581aa04d3cc7146669765e2bfaa4030cbf27017b0, 0x4125f1b53451217c0e10878059c81d7e5648fe639311d7b61e5cf5f6459158c28553ee285f39394a2dcb6a3ab39df543cfdb7540f2ff2df2eb774a1519899f803c1faecee37898b93587e5df34, 0xc4317c1c3f290d746945adb0b658a07668e44120748ef4f90a8f004005bbc375630546da4d4ff798461fe9c74546184b5856c8867cb074340a9773843b7743d29b1243a58f861f80988e4662d0,
  0x211ff603c04352e11c1ad4b10ef4f931e979056f1a16ed01e5f6246fdbf171eae0ed7a15fb31cb7ec47b461fdf91670fb4737997164349897d2cc96e1909618f7d4ba905c3841b9dbd5635342d3, 0x505c57cb0ea559a6157fe2f329528de507137e10c8668c1c4792457fefcc7753fe5e8b9fb79e0950eea36b8821cc2b8e0694dc7fb2cbfb7ad12b47b7c9e9abfea20911e9738eb474a9e93c28c44, 0xaf40e47866b320e6b626f8e7ab4d2d2c66752f2010cf05839ca613b3ecb74fd84205deb89c9219a45c15095d3be2aa8ff604d3bb504db699734f7570218c7426c346a36fe07c6f7915c51e26b1b,
  0x157df977689b2c7bfdb16d65a26d89fd8e0303f6e87b9c8958b295552a20b105c17ebe6c8568343168ffef8cd3eac81c551cc8f55bb88b56c3c765c3812069c019ce86e31ec9e142e62e8c99ddc0, 0x25f8556558df9d5075b573c2230f397a3e985835fd61fd8d0802c5385822ffb272a53da504c27db52a1d61d3b5a61a884ff5fd4e675f8aac0928b5701b7570016fc6c450f4810c90810315fff830, 0x3c6fe536bffac5492ded0b9b253d68c18238f48f21eb226af8959adee39b9407700040e78a09019b6b8e13e972f8776ac77fc60bf9c704e719efd59f223e0a971d8b81f3c572a101ab1cb741c340,
  0x56b68125bf1d8ffbfdac6524698c512dd8230e31efa67714b2032402fbb92fb6e2074af35cd9cb972462d799a039d55458157a1a00620b27e77eb18196e7055d57af2fe03acff5c16f480cf8adf0, 0x703060419b2818a04cc3f7753e4024fd79dba7e7f550c9ff0787e64f2f4e5e1bcdd89b6dd326b6ad0425348b0ae86697034078457bcd9e8614387bc77aa61453efdc6176afe79e552cee523c2840, 0x82ecc83e9fc592192d011db076f575e297e00f33466713f3239c3ba34a89c01ab083896abe9c792898f734d872f6c0a5d771fd9ebf22cd130cc90751ef2d6a141ab3dba0d2d5fe3cf8cc695e6058,
  0x89d6c2a7a609f5ee5509faa8683e78b1f8e6739f26b577c075f4d5dd203c94c035dc7603049137318392753825a4d972f5852358e78f74ad6b248d5fa06165859ec91783c1e9e32dc0e47f4652a0, 0x82ecc83e9fc592192d011db076f575e297e00f33466713f3239c3ba34a89c01ab083896abe9c792898f734d872f6c0a5d771fd9ebf22cd130cc90751ef2d6a141ab3dba0d2d5fe3cf8cc695e6058, 0x703060419b2818a04cc3f7753e4024fd79dba7e7f550c9ff0787e64f2f4e5e1bcdd89b6dd326b6ad0425348b0ae86697034078457bcd9e8614387bc77aa61453efdc6176afe79e552cee523c2840,
  0x56b68125bf1d8ffbfdac6524698c512dd8230e31efa67714b2032402fbb92fb6e2074af35cd9cb972462d799a039d55458157a1a00620b27e77eb18196e7055d57af2fe03acff5c16f480cf8adf0, 0x3c6fe536bffac5492ded0b9b253d68c18238f48f21eb226af8959adee39b9407700040e78a09019b6b8e13e972f8776ac77fc60bf9c704e719efd59f223e0a971d8b81f3c572a101ab1cb741c340, 0x25f8556558df9d5075b573c2230f397a3e985835fd61fd8d0802c5385822ffb272a53da504c27db52a1d61d3b5a61a884ff5fd4e675f8aac0928b5701b7570016fc6c450f4810c90810315fff830,
  0x157df977689b2c7bfdb16d65a26d89fd8e0303f6e87b9c8958b295552a20b105c17ebe6c8568343168ffef8cd3eac81c551cc8f55bb88b56c3c765c3812069c019ce86e31ec9e142e62e8c99ddc0, 0xaf40e47866b320e6b626f8e7ab4d2d2c66752f2010cf05839ca613b3ecb74fd84205deb89c9219a45c15095d3be2aa8ff604d3bb504db699734f7570218c7426c346a36fe07c6f7915c51e26b1b, 0x505c57cb0ea559a6157fe2f329528de507137e10c8668c1c4792457fefcc7753fe5e8b9fb79e0950eea36b8821cc2b8e0694dc7fb2cbfb7ad12b47b7c9e9abfea20911e9738eb474a9e93c28c44,
  0x211ff603c04352e11c1ad4b10ef4f931e979056f1a16ed01e5f6246fdbf171eae0ed7a15fb31cb7ec47b461fdf91670fb4737997164349897d2cc96e1909618f7d4ba905c3841b9dbd5635342d3, 0xc4317c1c3f290d746945adb0b658a07668e44120748ef4f90a8f004005bbc375630546da4d4ff798461fe9c74546184b5856c8867cb074340a9773843b7743d29b1243a58f861f80988e4662d0, 0x4125f1b53451217c0e10878059c81d7e5648fe639311d7b61e5cf5f6459158c28553ee285f39394a2dcb6a3ab39df543cfdb7540f2ff2df2eb774a1519899f803c1faecee37898b93587e5df34,
  0x1361842bed69c4c3273a78c9f7c30b3740d5d2db55285bfd4e985505bb800337d4516ece6695573a41f8210e26fe859d2ea206de897c4c6bf581aa04d3cc7146669765e2bfaa4030cbf27017b0, 0x52871261fc7f11d706f28574716a52d0bafde3e32a6aaf2422573815433e47fa19c5028a074e8514b56f04649ba42507ff4708e796ea61a65ce70c7a39a637d28119e9985e378e4b1fa96dc04, 0x139e1d51bb5032beea5372df1603758c10e2b3d6769c632942cb0ebd6326b201b6e8ae3884d53879e21c2206693700b850323eafebcbf3987fceda1972fea922cfe5dbafcdd3e40be6bd381b0,
  0x4286a3b2b21b8864f8c8793e307f32fd3ef4a6b3fa7dff5479c5f3258e4d312d457b8df22c243d2a6742de8b35daf250bc59fc2fe5b79e5529410f5a934ca12950a5c289602492f549cff98e, 0xc8c158dd951d1809a2910d55c6ceb0eb605a73f86c599425c10f118aa829e0358c025fc6cb9507d57b512359ef2496b2ef4e22397635ac539c4bc9fb38afc2b0e0051613728408d21b3b808, 0x219f37cbf6fbcac98b6ee416ce207293bc60fadb7995a1d5cb9c590bb056a1cc6e180fe1464b74898305080d17f34f40754c288a495ff1d752ea53ed1e7c83611b2c96208da8ec178010d6e,
  0x4fd0221d12bc44fe5b8526952275c18b411f3447c9cfead0918d93e3f581ef23fef9b1ea0b67dc97c06921f4df8d2324f9d6f490723930e38e41d16a3442b14a68bb061f3469c2dca057f0, 0xa7682fd6a26229573a6e8cf8bf43cab453696522c8a2b86ea2bf346a2bb712ff0261ff5e106b99362d9c23f8c8cde4d6c600f0da29e469661ea6eebd030c2decad38dee0f931fef8230d4, 0x135601904cb68acc7677ded45c766ffe7f5298d05e12f5d8c7a6f92470ee3e9587e61d3a4c5f45060a8f092fd78bddd17de5c35aa6f86dd6f5299179020c83bcd31ab78b70ffaffe72270,
  0x1f62c24eff511f806c16083515ddd6dd92136fbb48162a844e405bfc07cffd0c4ad2252af12c1c4b3d2a2141735b0b16519976381c6df78a7f7433db404138fc893d62a135848122b844, 0x2c97bffa0f42df88d91c2c6d9d4a5620fabb15e0814a10306d6e8bfdfda46da2e35be445326668e559519adb1ef7dde03dd625f0d362372c41eb5bd55e77148a30459da90313734a290, 0x373fb38e1158032272bc61577956e1870b635e3d6fc9af7b1c149f7236ce9e82c70e1f3ecc30c703aed95cc456d76b321acec7bdbbd5ded5feba389b7a0ae9a166f1fe6cb3dbada401,
  0x3b71ac1af5d27747c0a4156d5464125760cf2305a8fcedbba3b29e3519df2ae68a40ffbb8d8491e3684ccbcbd8bef92487613b8561c083664e4b910ff1f3a7a21237ede898a2c1eec, 0x3749f239d59cb2b8532ca0bc8ec42dfc3549d0351cd37278f45c4c2e6afc7268500e4cdcd963267c2bf5ca1b6bbec665e32edf542ebb843851aa9321c5c67773f64d6a95d8ce94b9, 0x2c3b177a3bfd952dbaa49d8d23e5033cf16154df5515c54e1bfc12756da357c6f39e1921bd65bc321e128c5050b77f47b2f5e940c0d0428931c41bca1fe916679821d0027d64da0,
  0x1e441b004574ef91ef65553a163280778c7f81f80efb99be7de98ec75fc1e2f021be17775001ea8cfd051a265dc20c458ed43394a2a00ee17722e86a4b9e825e4d613eeed3d048, 0x119b1308ff236bfb4f258675e1c9e8c77ef94dd69a8d8f888a7cec45d6f4c4bc7547810c733ceae6fd51f4bced75c687fdffb9895a583993521237095b19bfd74c0d8931d0ae0, 0x8a59286e0d4510bbe74ba76387ddc6b2ce2912edcb424fc2469afb5fa211f4060ea2d111b9afde16789b49f7778383f1888c6769a639a9fe85d6cf2e91f00a68949220e09e8,
  0x38eef26b804396ff772d986d0c30ab4fb8b0434f0b2d6ceb2a60160cd6fb854bfb7e722c38c5411bfd4bcf9b24208da1ad749e126bcf8051648ab02a264d1f3a1dbb396360, 0x1377211993629a2998f1b428637f193c1461f00733198252a35e6c10588b96d413f198f158948c93dd8b1089b428f78c22bd8297f2036df6ca6bd598314e673d7ea82c674, 0x57a09a9b89939f21d5fea214363294ba1757864f365c6d6515e56fc07953611922f8acc3776830cb3de12ed05e54e4d01f649f43ebd1c2f217114f1758f2174f49b7730,
  0x14128b2afbe14300c500ec0bc5df0a51bad2a95e4a89aa31f7973240bb4c64062c9ccdd691ed9b2a39cd02b3d5306b66ee25bf6b236732880aaa57920e308113628cf4, 0x3b2bfc136845feb06d30323a29f35a0be5ec1e98e804db59b08243f3b493a32b1ece549457f714fe0acefd64c3a47e8492d24cb74715c5b8c7bc3f9a8ca75bbe7e60, 0x8a61aede9c61c02775e44801fb3663a376d0b2c918d3941e4ef68b5ebb6f319bddc8915b2927a8d425932503206cd364b79c12c38fd9aa20e8e1a596ecf723b3a8,
  0xfcba377105afcb3dfe8755431738ab8e02a8f81465f14db918937464dc1fb3af39d55d06fad1313e04384baf8717381648ea752e7ecbf0cfe38d1a4ac1d18be0, 0x161fb1cfb34c58f3742fc274a99bec949d0b1b11813aa2c5a4850099fb38390e3e1b8ed95aac1d6befdb9afee4a948a86a078b833e13d8fbcde67444773dd08, 0x1745e7deffd3eed6a10e86ff80d5e4d561eb8c02a51c3892b80d51e421a5c1292481fd9628fc3866c704ceb2004f35ee4d2ac915dd6429511f9ad8388faa0,
  0x11f1c6c442b48307518d7de9f2f2910b341c71fea757ba008c8bb17aa54d6445eefdb610d17eaa4ad284b02daa962bd42eeb6be18150465b1b6ce42152b, 0x9daef1f581bdd61b288f6543fd8b55a0aca759a0646538f8207e93f11bdd77bb76154faafb39a028e09d4bb77a058e85a25e094dcb35850c90619544, 0x3ba1bb8df135c5545e0452cd267c2eea6f08cee395e85c286a70f946e9fd8035af4d77f63410be779c4cf8e06a0e7b016bcf3e74acb3c2a1f06fc3,
  0xee9ae4d7f24eb05a41aa88c714b3fc9d234f769a8f1897fe74bec7b55ae24ee73d4f57fd183e4fac5153ce9df76cbbe7de7c5f48eb2f241a3f0, 0x259474d19fb8b1be0b42e3f5f421dd313fcdc8a47e458ae28c28b1496a3fb0b13b08d74c50122f4f598d95372f699dd875eddf9da2e0bcc9c, 0x38317c6cf8d17f5494411aaccb781a7f6be4f44476b24bb8840c35b445d9c30d59dac111076fd56933e5df08830dc317316abaf5fb5810,
  0x2e52ee93fd5f71736322bb75cda4ced14416236e2ea16bd10f74f1c62bdb609dbdb31b1dc1f9c058d8b1e03b4d84f4bb66beb0a428c, 0x1333827ec5f4eda4cf4b886ef80fa651e2b3c98e0822efa462a4a55b91b145e8f832b051deb61dc56f6c5c3a0771a339b051c590, 0x38f43daa39f27594bc0f300f50fa1e98f9a459122bd18bf35b41b1a2b79353e84305d016dd608a1219a6dcc877c729075d72,
  0x40ee1ae5a71c6d24d9a7d7177142df2ab75ada6adc4dea35804b4ca4f652cd9441988dffd74f10ea166be8c70bbd6778, 0x17483e9ea52501f450ff3871e007c3acb99ea45362726767006b0a55c1a4b52b90e34200ea619534eeaf5cd987d2, 0x1fffcbe100315dd521a8460be37931c97054b2379338dca9ad3f2a7733b85033683626196dad4e64b7b56d0,
  0x730695a638e3e90419847bd0bb6b6eb147411a488ebedb90f4324979e0e2917e9f68e54865df5c51c, 0x269aaf8d99c812b59e5f06a13167c600362a05daad1da9767b0cdbb0319b51df4cdfb7d13d0, 0x81f14fac458c5f6e504938d93e8fc0897857ec3c86999db2c77fadff5da1b60766c,
  0x3fffffffffdd03d0b2506ad70e126531d155dfdca8a46c4d5262d530b0, 0x4d355f90f6405a5ab3f4893ad88d8bc99df6817f25f469, 0x7ffffffffffffffffffffffffff8c,
  0x1]

private theorem eulerianCoefficients_eq : descentCoeffs 115 = eulerianCoefficients := by
  decide +kernel

private theorem upper : upperOK (descentCoeffs 115) first gaps = true := by
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

private theorem lower (i : Fin (lastRepresentative 116 - 2)) :
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

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 116) :
    StrictNegativeInterlacing (originalQuotient 116 k) (eulerian 115) 113 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N116
