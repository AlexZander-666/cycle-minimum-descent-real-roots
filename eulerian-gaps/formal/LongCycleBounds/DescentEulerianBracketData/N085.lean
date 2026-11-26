import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentPackedData.C127L088.N085

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N085

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L088.N085 LongCycleBounds.DescentNecklace.Packed.C127L088.N085.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L088.N085 LongCycleBounds.DescentNecklace.Packed.C127L088.N085.rows

private theorem actual : RepresentativeChecks 85 previousNodes rows :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L088.N085 LongCycleBounds.DescentNecklace.Packed.C127L088.N085.dataChecks

private def first : LongCycleFinite.Dyadic := ⟨-19342813113834066795298816, 0⟩

private def gaps : List Window := [
  ⟨⟨-19342185924535560670543872, 0⟩, ⟨-619246237253632, 0⟩⟩,
  ⟨⟨-618694333956096, 0⟩, ⟨-31133335552, 0⟩⟩,
  ⟨⟨-31110463488, 0⟩, ⟨-134386176, 0⟩⟩,
  ⟨⟨-132968448, 0⟩, ⟨-4163888, 0⟩⟩,
  ⟨⟨-4157536, 0⟩, ⟨-371284, 0⟩⟩,
  ⟨⟨-371092, 0⟩, ⟨-124859, 1⟩⟩,
  ⟨⟨-499307, 3⟩, ⟨-506211, 5⟩⟩,
  ⟨⟨-506131, 5⟩, ⟨-339599, 6⟩⟩,
  ⟨⟨-169781, 5⟩, ⟨-139195, 6⟩⟩,
  ⟨⟨-8699, 2⟩, ⟨-132295, 7⟩⟩,
  ⟨⟨-264573, 8⟩, ⟨-17587, 5⟩⟩,
  ⟨⟨-281377, 9⟩, ⟨-163283, 9⟩⟩,
  ⟨⟨-326551, 10⟩, ⟨-406133, 11⟩⟩,
  ⟨⟨-203059, 10⟩, ⟨-66753, 9⟩⟩,
  ⟨⟨-267003, 11⟩, ⟨-367415, 12⟩⟩,
  ⟨⟨-367405, 12⟩, ⟨-262477, 12⟩⟩,
  ⟨⟨-131235, 11⟩, ⟨-386977, 13⟩⟩,
  ⟨⟨-48371, 10⟩, ⟨-36615, 10⟩⟩,
  ⟨⟨-146457, 12⟩, ⟨-453543, 14⟩⟩,
  ⟨⟨-453535, 14⟩, ⟨-357943, 14⟩⟩,
  ⟨⟨-357937, 14⟩, ⟨-143611, 13⟩⟩,
  ⟨⟨-287217, 14⟩, ⟨-233805, 14⟩⟩,
  ⟨⟨-467603, 15⟩, ⟨-24089, 11⟩⟩,
  ⟨⟨-192709, 14⟩, ⟨-321167, 15⟩⟩,
  ⟨⟨-160581, 14⟩, ⟨-270187, 15⟩⟩,
  ⟨⟨-270183, 15⟩, ⟨-229213, 15⟩⟩,
  ⟨⟨-114605, 14⟩, ⟨-391775, 16⟩⟩,
  ⟨⟨-391771, 16⟩, ⟨-168497, 15⟩⟩,
  ⟨⟨-168495, 15⟩, ⟨-36441, 13⟩⟩,
  ⟨⟨-291525, 16⟩, ⟨-63365, 14⟩⟩,
  ⟨⟨-506915, 17⟩, ⟨-442665, 17⟩⟩,
  ⟨⟨-110665, 15⟩, ⟨-97009, 15⟩⟩,
  ⟨⟨-6063, 11⟩, ⟨-341283, 17⟩⟩,
  ⟨⟨-341279, 17⟩, ⟨-301021, 17⟩⟩,
  ⟨⟨-150509, 16⟩, ⟨-133077, 16⟩⟩,
  ⟨⟨-266151, 17⟩, ⟨-471615, 18⟩⟩,
  ⟨⟨-235805, 17⟩, ⟨-418537, 18⟩⟩,
  ⟨⟨-418533, 18⟩, ⟨-371917, 18⟩⟩,
  ⟨⟨-185957, 17⟩, ⟨-330811, 18⟩⟩,
  ⟨⟨-41351, 15⟩, ⟨-147219, 17⟩⟩,
  ⟨⟨-294435, 18⟩, ⟨-262145, 18⟩⟩,
  ⟨⟨-524285, 19⟩, ⟨-233395, 18⟩⟩,
  ⟨⟨-233393, 18⟩, ⟨-415463, 19⟩⟩,
  ⟨⟨-415459, 19⟩, ⟨-369545, 19⟩⟩,
  ⟨⟨-369541, 19⟩, ⟨-164191, 18⟩⟩,
  ⟨⟨-328379, 19⟩, ⟨-291425, 19⟩⟩,
  ⟨⟨-145711, 18⟩, ⟨-516393, 20⟩⟩,
  ⟨⟨-129097, 18⟩, ⟨-228291, 19⟩⟩,
  ⟨⟨-456577, 20⟩, ⟨-201359, 19⟩⟩,
  ⟨⟨-201357, 19⟩, ⟨-354195, 20⟩⟩,
  ⟨⟨-22137, 16⟩, ⟨-310485, 20⟩⟩,
  ⟨⟨-310481, 20⟩, ⟨-33891, 17⟩⟩,
  ⟨⟨-271125, 20⟩, ⟨-235725, 20⟩⟩,
  ⟨⟨-471445, 21⟩, ⟨-101961, 19⟩⟩,
  ⟨⟨-12745, 16⟩, ⟨-350815, 21⟩⟩,
  ⟨⟨-350811, 21⟩, ⟨-149905, 20⟩⟩,
  ⟨⟨-149903, 20⟩, ⟨-254343, 21⟩⟩,
  ⟨⟨-63585, 19⟩, ⟨-427941, 22⟩⟩,
  ⟨⟨-427935, 22⟩, ⟨-356595, 22⟩⟩,
  ⟨⟨-178295, 21⟩, ⟨-73481, 20⟩⟩,
  ⟨⟨-9185, 17⟩, ⟨-478519, 23⟩⟩,
  ⟨⟨-29907, 19⟩, ⟨-95993, 21⟩⟩,
  ⟨⟨-191983, 22⟩, ⟨-303041, 23⟩⟩,
  ⟨⟨-75759, 21⟩, ⟨-117301, 22⟩⟩,
  ⟨⟨-117299, 22⟩, ⟨-355163, 24⟩⟩,
  ⟨⟨-88789, 22⟩, ⟨-261815, 24⟩⟩,
  ⟨⟨-523619, 25⟩, ⟨-374073, 25⟩⟩,
  ⟨⟨-23379, 21⟩, ⟨-514749, 26⟩⟩,
  ⟨⟨-514737, 26⟩, ⟨-338419, 26⟩⟩,
  ⟨⟨-338409, 26⟩, ⟨-420873, 27⟩⟩,
  ⟨⟨-105215, 25⟩, ⟨-244217, 27⟩⟩,
  ⟨⟨-244209, 27⟩, ⟨-519453, 29⟩⟩,
  ⟨⟨-259717, 28⟩, ⟨-123429, 28⟩⟩,
  ⟨⟨-3857, 23⟩, ⟨-202359, 30⟩⟩,
  ⟨⟨-404699, 31⟩, ⟨-271553, 32⟩⟩,
  ⟨⟨-135769, 31⟩, ⟨-68815, 32⟩⟩,
  ⟨⟨-275243, 34⟩, ⟨-185159, 36⟩⟩,
  ⟨⟨-370293, 37⟩, ⟨-264297, 40⟩⟩,
  ⟨⟨-264277, 40⟩, ⟨-262277, 45⟩⟩,
  ⟨⟨-16391, 41⟩, ⟨-289503, 53⟩⟩,
  ⟨⟨-289479, 53⟩, ⟨-476899, 68⟩⟩,
  ⟨⟨-238427, 67⟩, ⟨-262165, 102⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private def eulerianCoefficients : List ℤ := [
  0x1, 0xfffffffffffffffffffab, 0x232f1e8ccafd7b7d8f46264f29828c3683,
  0xfffffff4515adb4098f18f4f6db547b737a7750609, 0x83c7033e1aab8485eaa6de362843b07a0c8592fc0b3c96094, 0x232ef2cbb60abca2a323db7bdc40c8be3e357ac4fcfc1852382abdc,
  0xe1958841db41a3ea89cc81aed1796b279e894526d74779c3c29f24cb96c, 0xffb517636e00973d7af31ca096c737a6fd0a466984472d3d214a0499d9d4844, 0x4d09bcb5f2d24e77b25f1e389801420e8aa44895851050369fa2f0f78b072dae7b6,
  0x822ce08f9e1c245e55d0f02013a30a551cd2ce5df7843ecd63c17eeee274b42f8c2812, 0x5dc4b2b71442caa3dd8a7ac84f14d07f12a1e2fbea137e73ba79b48e9565b153aed20cc52, 0x2135af3cda8facc49cecbd8027eaca338afe789da2be3f58f752301023de1b92055c8d579876,
  0x66f6a4ed693ed07ad79d2a6603c8f6fec51db44c0e6bf0c18d7cf8c7db601caed572169399bba4, 0xbd8d9ffe3d83a33b1f1a653dd84442ce023d84986ecf1def1c79c793a820d96eb67dba1017bb828c, 0xdce2dd67fb9af1e5d0f2f163c5ca8bdc5170a80e4b2209f8571a53f1e4ed3cd758c7ebf5f319f1fe7c,
  0xab6b27edc9b2921b386f090434a41272c29f1bc1cd34dc559a05710f178d6ba2c105d2aaca21d675d874, 0x5c4d1535fe9d9e5f4acaaf8d2790cbfa92599e9928b8f5c118925716330d0328fc2ba29dca9d1310ca6c35, 0x23a914dbd9795811a6dbbf9516212011bed61e590e8aa57a6be8e2cbb3c29b37c62bc427090ac1c074a4dde7,
  0xa29ffdc07d39ecc42eb7779155857a9e9c7db886e6e7fba7d1ea0e4983d4019a92abc2eeb117308b3ff994caf, 0x23000cef35e57178c216dbbc9de3c01f0d7a222aeeceef17d073ac44f5fed6c52dd6e49b140678bb237b05ca10d, 0x5cd075a6f4dc9caa1cef801e61dfa170331ff0a34f6019f0b662e500795d89c2e7a4134c8d01502b39bcce53dc10,
  0xc0bdd840d5f04b3cf0be882c1c9508403ee3f84efafd797f47421104b884a430750e0a34ea891a38b25688273bab0, 0x13dfa264df9389f8f9b7675a9a86ac828c6cf7a10161ce5a0d2a0697a244038a8e5a918fdb93d3bbe70518ab55cd8f0, 0x1a5f513cbd0e471bc8a4904b113ae9c87922f8f668221ed335658842d6d1dc9480c018453ddf118fbb4f4fb55a6a72d0,
  0x1c746b24acc15e23a047b441285434a531868d0cc4dc38990b3528c7d2da8822678ac290b2be66540398fb6da6e6f3148, 0x1932dccf46bde2c759d9ad386edaf880003a5ba3c3edf75de321136abf7cc59c28cf899b67a61f6219d18f1a1f447e2918, 0x12777d9876eb2d72191e04e1833f1585f3effdb4f16b1b14498b6fca67bde811de5f07e81c040486d2c2a08984aa2b63a98,
  0xb47d195a26c34942290d84067a0ca2993a19866c85101e277eb9432c2c1f0d41ba0fb4d4e2ed2d7a3f75f8ee9fabd407dc8, 0x5c7c49022d7dffe7164da290246550bf189597145ffd28e489fc010c77737a2a9109251f3ec43079248d352a7b5c744fd710, 0x27fa189092e6bd734d83a335b6b1083f030e438a4a27bfb773730db48b6fc091d668fe40ff9ab35fee68e73a3bb4d95891fb0,
  0xea608359910e828afbb6c251d3248a14d583b6611fc6f1eef163ca420762abc7a973c782d6624cd783cfdbb1a432e06102a70, 0x491e70349d59e3e503e165e0840bc518cae45fcee7a1a261ebdcf15343b2aef075848669cdcc21f5905ba689980cfb2c072b50, 0x137eb6459733abc44d857180afd5301410f7dde0b3f01a3066f301d2c55540dcab58c2fa14e8d5ef6004b7948e46b6731e3a5b2,
  0x474f8d056bd5c61277d090acf855b810c3d1144527ca311820c5ad1739522fb70421699fffeea024c68f7ea0fa67b51404eb9e6, 0xe050c7fdd1cb6c77bb2c4824c3ac8c692f0f899a0779a09f080720420f5bf476bdac1c6ad17e99caa26a543c5f5a27d1299a756, 0x2604bcc4011fb3bb7ae48d6c1f4d3d3f4ccd07c0ad8d258230c45154f9274765d981d37ae707132a2f6a6f9a29ab5468a1468d02,
  0x59115f981278b768a15071b2619adda5c7161df6aa88d1231e399267a07f805930964df619fb0f86ec6404e4cb6d0222e935a798, 0xb49657c6ba0080158f9187950ddfe049fc0db8d8bed8deafe44b480f080c4d2cdaac2220491583a22474d8d6a21d709539e5e888, 0x13d5697d415afde4ae2e88482f86566840cbd76d92d7e0ff2ecec77cd0601a9685b9ce2c5c1efaea167168c5c87f9de792fdb5368,
  0x1e3dcdfb03f5e533550a3857ffa2d0883eaa7741841b1661c8b41da97a4ab071641a2b09ea5551f6c0988efd53a4eae9fc336ca38, 0x280b2becc72a46e7a1a9edae3b49766c3d1621592aa93bb23487560f5c7c9771f3a913f76bd2deaa9efd4571a8f5736fc675f8ac4, 0x2e127b1f160b40df11ac5718941b47eed39fb539edf7c93740367c23b0ec11f4268a974737a632ebd9385af68fc182f0b2dc3e5ec,
  0x2e127b1f160b40df11ac5718941b47eed39fb539edf7c93740367c23b0ec11f4268a974737a632ebd9385af68fc182f0b2dc3e5ec, 0x280b2becc72a46e7a1a9edae3b49766c3d1621592aa93bb23487560f5c7c9771f3a913f76bd2deaa9efd4571a8f5736fc675f8ac4, 0x1e3dcdfb03f5e533550a3857ffa2d0883eaa7741841b1661c8b41da97a4ab071641a2b09ea5551f6c0988efd53a4eae9fc336ca38,
  0x13d5697d415afde4ae2e88482f86566840cbd76d92d7e0ff2ecec77cd0601a9685b9ce2c5c1efaea167168c5c87f9de792fdb5368, 0xb49657c6ba0080158f9187950ddfe049fc0db8d8bed8deafe44b480f080c4d2cdaac2220491583a22474d8d6a21d709539e5e888, 0x59115f981278b768a15071b2619adda5c7161df6aa88d1231e399267a07f805930964df619fb0f86ec6404e4cb6d0222e935a798,
  0x2604bcc4011fb3bb7ae48d6c1f4d3d3f4ccd07c0ad8d258230c45154f9274765d981d37ae707132a2f6a6f9a29ab5468a1468d02, 0xe050c7fdd1cb6c77bb2c4824c3ac8c692f0f899a0779a09f080720420f5bf476bdac1c6ad17e99caa26a543c5f5a27d1299a756, 0x474f8d056bd5c61277d090acf855b810c3d1144527ca311820c5ad1739522fb70421699fffeea024c68f7ea0fa67b51404eb9e6,
  0x137eb6459733abc44d857180afd5301410f7dde0b3f01a3066f301d2c55540dcab58c2fa14e8d5ef6004b7948e46b6731e3a5b2, 0x491e70349d59e3e503e165e0840bc518cae45fcee7a1a261ebdcf15343b2aef075848669cdcc21f5905ba689980cfb2c072b50, 0xea608359910e828afbb6c251d3248a14d583b6611fc6f1eef163ca420762abc7a973c782d6624cd783cfdbb1a432e06102a70,
  0x27fa189092e6bd734d83a335b6b1083f030e438a4a27bfb773730db48b6fc091d668fe40ff9ab35fee68e73a3bb4d95891fb0, 0x5c7c49022d7dffe7164da290246550bf189597145ffd28e489fc010c77737a2a9109251f3ec43079248d352a7b5c744fd710, 0xb47d195a26c34942290d84067a0ca2993a19866c85101e277eb9432c2c1f0d41ba0fb4d4e2ed2d7a3f75f8ee9fabd407dc8,
  0x12777d9876eb2d72191e04e1833f1585f3effdb4f16b1b14498b6fca67bde811de5f07e81c040486d2c2a08984aa2b63a98, 0x1932dccf46bde2c759d9ad386edaf880003a5ba3c3edf75de321136abf7cc59c28cf899b67a61f6219d18f1a1f447e2918, 0x1c746b24acc15e23a047b441285434a531868d0cc4dc38990b3528c7d2da8822678ac290b2be66540398fb6da6e6f3148,
  0x1a5f513cbd0e471bc8a4904b113ae9c87922f8f668221ed335658842d6d1dc9480c018453ddf118fbb4f4fb55a6a72d0, 0x13dfa264df9389f8f9b7675a9a86ac828c6cf7a10161ce5a0d2a0697a244038a8e5a918fdb93d3bbe70518ab55cd8f0, 0xc0bdd840d5f04b3cf0be882c1c9508403ee3f84efafd797f47421104b884a430750e0a34ea891a38b25688273bab0,
  0x5cd075a6f4dc9caa1cef801e61dfa170331ff0a34f6019f0b662e500795d89c2e7a4134c8d01502b39bcce53dc10, 0x23000cef35e57178c216dbbc9de3c01f0d7a222aeeceef17d073ac44f5fed6c52dd6e49b140678bb237b05ca10d, 0xa29ffdc07d39ecc42eb7779155857a9e9c7db886e6e7fba7d1ea0e4983d4019a92abc2eeb117308b3ff994caf,
  0x23a914dbd9795811a6dbbf9516212011bed61e590e8aa57a6be8e2cbb3c29b37c62bc427090ac1c074a4dde7, 0x5c4d1535fe9d9e5f4acaaf8d2790cbfa92599e9928b8f5c118925716330d0328fc2ba29dca9d1310ca6c35, 0xab6b27edc9b2921b386f090434a41272c29f1bc1cd34dc559a05710f178d6ba2c105d2aaca21d675d874,
  0xdce2dd67fb9af1e5d0f2f163c5ca8bdc5170a80e4b2209f8571a53f1e4ed3cd758c7ebf5f319f1fe7c, 0xbd8d9ffe3d83a33b1f1a653dd84442ce023d84986ecf1def1c79c793a820d96eb67dba1017bb828c, 0x66f6a4ed693ed07ad79d2a6603c8f6fec51db44c0e6bf0c18d7cf8c7db601caed572169399bba4,
  0x2135af3cda8facc49cecbd8027eaca338afe789da2be3f58f752301023de1b92055c8d579876, 0x5dc4b2b71442caa3dd8a7ac84f14d07f12a1e2fbea137e73ba79b48e9565b153aed20cc52, 0x822ce08f9e1c245e55d0f02013a30a551cd2ce5df7843ecd63c17eeee274b42f8c2812,
  0x4d09bcb5f2d24e77b25f1e389801420e8aa44895851050369fa2f0f78b072dae7b6, 0xffb517636e00973d7af31ca096c737a6fd0a466984472d3d214a0499d9d4844, 0xe1958841db41a3ea89cc81aed1796b279e894526d74779c3c29f24cb96c,
  0x232ef2cbb60abca2a323db7bdc40c8be3e357ac4fcfc1852382abdc, 0x83c7033e1aab8485eaa6de362843b07a0c8592fc0b3c96094, 0xfffffff4515adb4098f18f4f6db547b737a7750609,
  0x232f1e8ccafd7b7d8f46264f29828c3683, 0xfffffffffffffffffffab, 0x1]

private theorem eulerianCoefficients_eq : descentCoeffs 84 = eulerianCoefficients := by
  decide +kernel

private theorem upper : upperOK (descentCoeffs 84) first gaps = true := by
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

private theorem lower (i : Fin (lastRepresentative 85 - 2)) :
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

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 85) :
    StrictNegativeInterlacing (originalQuotient 85 k) (eulerian 84) 82 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N085
