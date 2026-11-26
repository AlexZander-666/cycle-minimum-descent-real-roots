import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentPackedData.C127L127.N125

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N125

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L127.N125 LongCycleBounds.DescentNecklace.Packed.C127L127.N125.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L127.N125 LongCycleBounds.DescentNecklace.Packed.C127L127.N125.rows

private theorem actual : RepresentativeChecks 125 previousNodes rows :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L127.N125 LongCycleBounds.DescentNecklace.Packed.C127L127.N125.dataChecks

private def first : LongCycleFinite.Dyadic := ⟨-21267647932558653966460912964485513216, 0⟩

private def gaps : List Window := [
  ⟨⟨-21266958330632129809666498757941788672, 0⟩, ⟨-7380228853357126615040, 0⟩⟩,
  ⟨⟨-6789933042998420963328, 0⟩, ⟨-3130953849372672, 0⟩⟩,
  ⟨⟨-2866967979491328, 0⟩, ⟨-1109573763072, 0⟩⟩,
  ⟨⟨-966858375168, 0⟩, ⟨-6448660480, 0⟩⟩,
  ⟨⟨-6398672896, 0⟩, ⟨-189672960, 0⟩⟩,
  ⟨⟨-189356032, 0⟩, ⟨-14205984, 0⟩⟩,
  ⟨⟨-14196832, 0⟩, ⟨-1946692, 0⟩⟩,
  ⟨⟨-1946036, 0⟩, ⟨-403165, 0⟩⟩,
  ⟨⟨-403080, 0⟩, ⟨-224197, 1⟩⟩,
  ⟨⟨-448329, 2⟩, ⟨-155059, 2⟩⟩,
  ⟨⟨-310085, 3⟩, ⟨-126535, 3⟩⟩,
  ⟨⟨-506099, 5⟩, ⟨-469809, 6⟩⟩,
  ⟨⟨-234889, 5⟩, ⟨-482959, 7⟩⟩,
  ⟨⟨-120733, 5⟩, ⟨-269531, 7⟩⟩,
  ⟨⟨-134759, 6⟩, ⟨-160893, 7⟩⟩,
  ⟨⟨-321773, 8⟩, ⟨-406183, 9⟩⟩,
  ⟨⟨-50771, 6⟩, ⟨-268615, 9⟩⟩,
  ⟨⟨-134303, 8⟩, ⟨-92395, 8⟩⟩,
  ⟨⟨-184785, 9⟩, ⟨-262949, 10⟩⟩,
  ⟨⟨-131471, 9⟩, ⟨-192575, 10⟩⟩,
  ⟨⟨-385141, 11⟩, ⟨-289231, 11⟩⟩,
  ⟨⟨-289225, 11⟩, ⟨-27749, 8⟩⟩,
  ⟨⟨-443975, 12⟩, ⟨-347353, 12⟩⟩,
  ⟨⟨-173673, 11⟩, ⟨-276365, 12⟩⟩,
  ⟨⟨-34545, 9⟩, ⟨-111593, 11⟩⟩,
  ⟨⟨-446365, 13⟩, ⟨-365293, 13⟩⟩,
  ⟨⟨-45661, 10⟩, ⟨-9453, 8⟩⟩,
  ⟨⟨-302491, 13⟩, ⟨-506317, 14⟩⟩,
  ⟨⟨-253155, 13⟩, ⟨-106947, 12⟩⟩,
  ⟨⟨-427783, 14⟩, ⟨-45569, 11⟩⟩,
  ⟨⟨-91137, 12⟩, ⟨-156541, 13⟩⟩,
  ⟨⟨-156539, 13⟩, ⟨-67693, 12⟩⟩,
  ⟨⟨-16923, 10⟩, ⟨-235677, 14⟩⟩,
  ⟨⟨-471349, 15⟩, ⟨-412647, 15⟩⟩,
  ⟨⟨-206321, 14⟩, ⟨-11349, 10⟩⟩,
  ⟨⟨-90791, 13⟩, ⟨-321167, 15⟩⟩,
  ⟨⟨-80291, 13⟩, ⟨-285277, 15⟩⟩,
  ⟨⟨-142637, 14⟩, ⟨-508845, 16⟩⟩,
  ⟨⟨-508841, 16⟩, ⟨-455493, 16⟩⟩,
  ⟨⟨-7117, 10⟩, ⟨-204557, 15⟩⟩,
  ⟨⟨-204555, 15⟩, ⟨-46075, 13⟩⟩,
  ⟨⟨-368597, 16⟩, ⟨-333043, 16⟩⟩,
  ⟨⟨-20815, 12⟩, ⟨-301701, 16⟩⟩,
  ⟨⟨-150849, 15⟩, ⟨-136981, 15⟩⟩,
  ⟨⟨-273959, 16⟩, ⟨-62329, 14⟩⟩,
  ⟨⟨-124657, 15⟩, ⟨-56835, 14⟩⟩,
  ⟨⟨-113669, 15⟩, ⟨-415359, 17⟩⟩,
  ⟨⟨-415355, 17⟩, ⟨-380065, 17⟩⟩,
  ⟨⟨-190031, 16⟩, ⟨-174147, 16⟩⟩,
  ⟨⟨-348291, 17⟩, ⟨-159805, 16⟩⟩,
  ⟨⟨-319607, 17⟩, ⟨-146823, 16⟩⟩,
  ⟨⟨-73411, 15⟩, ⟨-270085, 17⟩⟩,
  ⟨⟨-270083, 17⟩, ⟨-62163, 15⟩⟩,
  ⟨⟨-497301, 18⟩, ⟨-458229, 18⟩⟩,
  ⟨⟨-229113, 17⟩, ⟨-422531, 18⟩⟩,
  ⟨⟨-3301, 11⟩, ⟨-389855, 18⟩⟩,
  ⟨⟨-97463, 16⟩, ⟨-359889, 18⟩⟩,
  ⟨⟨-179943, 17⟩, ⟨-41545, 15⟩⟩,
  ⟨⟨-332357, 18⟩, ⟨-153515, 17⟩⟩,
  ⟨⟨-307027, 18⟩, ⟨-283687, 18⟩⟩,
  ⟨⟨-283685, 18⟩, ⟨-262145, 18⟩⟩,
  ⟨⟨-262143, 18⟩, ⟨-484479, 19⟩⟩,
  ⟨⟨-484475, 19⟩, ⟨-447645, 19⟩⟩,
  ⟨⟨-447641, 19⟩, ⟨-51691, 16⟩⟩,
  ⟨⟨-413525, 19⟩, ⟨-47737, 16⟩⟩,
  ⟨⟨-381893, 19⟩, ⟨-352541, 19⟩⟩,
  ⟨⟨-352539, 19⟩, ⟨-325279, 19⟩⟩,
  ⟨⟨-81319, 17⟩, ⟨-299937, 19⟩⟩,
  ⟨⟨-299935, 19⟩, ⟨-138185, 18⟩⟩,
  ⟨⟨-17273, 15⟩, ⟨-508877, 20⟩⟩,
  ⟨⟨-508873, 20⟩, ⟨-468047, 20⟩⟩,
  ⟨⟨-117011, 18⟩, ⟨-430025, 20⟩⟩,
  ⟨⟨-215011, 19⟩, ⟨-197305, 19⟩⟩,
  ⟨⟨-394607, 20⟩, ⟨-180811, 19⟩⟩,
  ⟨⟨-361619, 20⟩, ⟨-20681, 16⟩⟩,
  ⟨⟨-330893, 20⟩, ⟨-151139, 19⟩⟩,
  ⟨⟨-302275, 20⟩, ⟨-275635, 20⟩⟩,
  ⟨⟨-275633, 20⟩, ⟨-501677, 21⟩⟩,
  ⟨⟨-501673, 21⟩, ⟨-3559, 14⟩⟩,
  ⟨⟨-113887, 19⟩, ⟨-51585, 18⟩⟩,
  ⟨⟨-103169, 19⟩, ⟨-372873, 21⟩⟩,
  ⟨⟨-372869, 21⟩, ⟨-335947, 21⟩⟩,
  ⟨⟨-335943, 21⟩, ⟨-301741, 21⟩⟩,
  ⟨⟨-150869, 20⟩, ⟨-135051, 20⟩⟩,
  ⟨⟨-67525, 19⟩, ⟨-481779, 22⟩⟩,
  ⟨⟨-481775, 22⟩, ⟨-213971, 21⟩⟩,
  ⟨⟨-213969, 21⟩, ⟨-378449, 22⟩⟩,
  ⟨⟨-378445, 22⟩, ⟨-333071, 22⟩⟩,
  ⟨⟨-333067, 22⟩, ⟨-72897, 20⟩⟩,
  ⟨⟨-1139, 14⟩, ⟨-507589, 23⟩⟩,
  ⟨⟨-507583, 23⟩, ⟨-438993, 23⟩⟩,
  ⟨⟨-109747, 21⟩, ⟨-377013, 23⟩⟩,
  ⟨⟨-23563, 19⟩, ⟨-160641, 22⟩⟩,
  ⟨⟨-160639, 22⟩, ⟨-67863, 21⟩⟩,
  ⟨⟨-271449, 23⟩, ⟨-454359, 24⟩⟩,
  ⟨⟨-454353, 24⟩, ⟨-376247, 24⟩⟩,
  ⟨⟨-188121, 23⟩, ⟨-307907, 24⟩⟩,
  ⟨⟨-153951, 23⟩, ⟨-497319, 25⟩⟩,
  ⟨⟨-15541, 20⟩, ⟨-395685, 25⟩⟩,
  ⟨⟨-395679, 25⟩, ⟨-154781, 24⟩⟩,
  ⟨⟨-309557, 25⟩, ⟨-475193, 26⟩⟩,
  ⟨⟨-29699, 22⟩, ⟨-356849, 26⟩⟩,
  ⟨⟨-178421, 25⟩, ⟨-522697, 27⟩⟩,
  ⟨⟨-261343, 26⟩, ⟨-185945, 26⟩⟩,
  ⟨⟨-371881, 27⟩, ⟨-255835, 27⟩⟩,
  ⟨⟨-255829, 27⟩, ⟨-169189, 27⟩⟩,
  ⟨⟨-338369, 28⟩, ⟨-3337, 22⟩⟩,
  ⟨⟨-106781, 27⟩, ⟨-509937, 30⟩⟩,
  ⟨⟨-509921, 30⟩, ⟨-71147, 28⟩⟩,
  ⟨⟨-142289, 29⟩, ⟨-146273, 30⟩⟩,
  ⟨⟨-146267, 30⟩, ⟨-271555, 32⟩⟩,
  ⟨⟨-33943, 29⟩, ⟨-443219, 34⟩⟩,
  ⟨⟨-443199, 34⟩, ⟨-306519, 35⟩⟩,
  ⟨⟨-306503, 35⟩, ⟨-340975, 37⟩⟩,
  ⟨⟨-340955, 37⟩, ⟨-282465, 39⟩⟩,
  ⟨⟨-282447, 39⟩, ⟨-309721, 42⟩⟩,
  ⟨⟨-77425, 40⟩, ⟨-371541, 46⟩⟩,
  ⟨⟨-185757, 45⟩, ⟨-350841, 51⟩⟩,
  ⟨⟨-175407, 50⟩, ⟨-139477, 57⟩⟩,
  ⟨⟨-69733, 56⟩, ⟨-380081, 70⟩⟩,
  ⟨⟨-380049, 70⟩, ⟨-22611, 87⟩⟩,
  ⟨⟨-361741, 91⟩, ⟨-262165, 142⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private def eulerianCoefficients : List ℤ := [
  0x1, 0xfffffffffffffffffffffffffffff83, 0x17304eb2c6a575e41ac10a9327780b02ceac400692fb63c0f7,
  0xfffffffffff4ad6992b501356f9d038dd625ba629fa115e4bcca3b4054b65d, 0xf209787b377d6b84c06a4a5e2b9bce4f150ae4a55438c230fa2369553585a39746eab7e6, 0x17304eab63bb789f94dd329608480b855df1df334d2cc303d83b9a64f7d407bff7d0cf9bd7b9d8912,
  0x114aae21333652eb836635e7e5951c7b48a7486016292669367bd870d6ba914c34f6c9e49d378c246b1a9b62, 0xffff78e88cd34ce348ffa1d06686d76cca37f48f7a388bcad45fe5c4474ce4d2b670df68945faca32d6b78418b6d6, 0x219af71bcf92202c66cf99b62cf33bb400c4f531fa275bb1ec092744c5164adc0b2c88c9566f88d1a19cf2644ad674a129f,
  0xf1f90fb248f3cd7028176c0ce5c4a991f7fd5ee496d821b1912dfbab45c2dda7da52d8edfca3d535ea7cba7bc244afcb9aae23d, 0x1f4d5c4f7d6f72011395fd5512e8eaf3eb12c539ccaf57ab37a8fd03d7b2ee7ba06ed4e8e54e7debb5b0ac754ba562db442da2dc7811, 0x1721041b711d2818b7f81433eaf3f8820177095472b54a7fcb4030a2f2247a11d1f17f7d908dff0c2fd6bed04b3b83702d6d1fab3693361b,
  0x730404cda28aa046449b0a8203b74c2c2b9e8f45daaae78e297cdbf9e4d014e104cc2cb24cd5839df3a895ef3516652b387cbfe4d53b82ed6fc, 0x1112595e45d2d3b31918d0c8449db61fdfcd46cae4083da421f3ea8a9d6039e0de157e66bc65dc47d5c5c5e1d71d68abeaa61e211011ee8f00e1a34, 0x1566491067825b46a1ac3c3ebd97965debd810ff028bb2c856eaeda8a61411c1e0b4319c97707a42ecb1837591106a052428bf616cce18c65e39f5d674,
  0xf56c173be8a9b0151a4cafb0ca4c44b83e3fc9eccfe7b3034d3c488251528805f9a0a7b4082a7355c8dfa430c80ceb875a299d86daaf465a6327e1dcabbc, 0x6b5729440556eae685ab640f66273a788ac4ed8dd20a9571a26f96bc7070da40c55fa56aca29d1335d6ac9617ab5226d08eb194763c41286cedd8b9802e18b5, 0x1e36f0039bd971064e2dd9f5e5ee14bf086bc99cdb059c504c9cf68aa6b3a0945d88d27e538839f2153e65bc64bccd6a4f3b2c225b294021f4e749070998ecf0df,
  0x5b893722bb2a8433ca5edad8f43d120cf236b27f529ee4ea9ee0e169b8b67cef6c0edd4760b20d3c97d559ffeb1aa70784597dbf9651acb1a56406501675220b9a53, 0xc19346ac89cdb387dc84644de4319578fe89b863c0890ab7e23eef71ca9ed8bd7b5f1e54f3d0522fa682073d20734fd543a0e3c5c44b20e3c08178e160f2c2c5fb0711, 0x126d648a223eb01a259f1bc6944c3104ebe0699d3b9ecc9fc8a716af350d427591219a0cd236f0224529987affda39d00b6b08b10cab2542dee0df75989b0109f9f41d6f2,
  0x14c2d5089c0db9797c7b43121348d79eaee142f93fa5782ce749f4eee1a1c6c8073535955a7655cc216af3f69c83bcd73a4b52d0aa5cfe4060a365b4977a404505b0c565176, 0x11b3dac8f5d0d3a039dd9cd97535b3b1f2c8ff4da4d94738303a8fcdef5f49eaeabcdff6655b910c77e08224b79cde1fc3f85a4a96c6a3162535e8626c45f5b4ddfac7dcba7c6, 0xba708aecd81c2919600444154269b33748547d771bed1baa4f01d562972e5a517f7b1fc98b90a24aa00189a2728d71a7872d0cc7d3fe4d94755268d3398440632f0ab163caa1e2,
  0x6061d63c25c1bd8b8285332a1bd1539716adb538f39624eb836ec2e88d59bee6f1a134524cf871897e1d9ec785b71d2113e97e90f60001705d8765b7ea3db7899baf962a225a9a03, 0x27b9f4c9f595123d4b637696760ad95fcbb0447f7b86a9cb8e09333be84a7a110cfb3609d3484325866bd26f2f1f735e18da49a865f9b43cae40e6808b880d4e4db513e4fb6d5be7a9, 0xd3ac8e5fd38cf6e10f8267388223dfbf2d24630edf99c93cf6481a5ba0ddeac38c2de0f20ef8c16d5002db06ac9e8509ee36682283fd37449b15b32896f224f48a0e0bda79c7a98853d,
  0x39a043be343a8529b036d3f892d0db43859b41b2fa06dede06dafd03ba42e2ff07eaaae1e1dccf1b4e76ce4ad8faa919190a8198d489cf1c3bc58f3bf7e2ca590ab965385e707a443b4bf, 0xcf5933bd7667ec4d194577518a8dc662b5fd254410a80c115baf15ad6338d77cb95916197b0500f42870963db41e5f891a5e6ec4d887447b0d70ae9c1c17e755f262e4c4238983b2d090d8, 0x26e101b82175ef2da1df593db82a1dc8491fd3dcbe19f9e3191491363dea124114d973f83b5591e900d930b4c2a3098bf952692730e4aeecd26790a0f44caf0407068962ec03cc94d24c6d08,
  0x6210e5625fd33a81b354649e01e4154acf408afe89a88d3ba48edd9b4ff3284a175a153f16c7e599958faa1b2e92ca1230424617072d6941b7dd04fd28713f77e86b7f6e256076b4c2392ac08, 0xd187b00d957fbc70631f27e100c78abf5ab68dc25f5b3d352a517c09278bfe979a5faf1c0243c1b5376af7c4665e0a3d258d00b1d4319c64b73c6c0f1bce6412c5616f77fe3cffe75f4500cdd8, 0x17dcbbc188307f494749d87836dc5237bb0bfa71b57e74c55ce8c2ddedc3f03453c96a8994406416de4487b62f407ff30eefa93e4c64e82b276c88ea3bf7993c84af9dbec4d5e42027ec1e68ff4d,
  0x254ef017ddd1e16a876cb7a7cd272efb871bd59ad7e1db519a2fdf39756bb50531e861d1eb7f155379472a03368ef2db22d9000b00218aef35dfbf3507787c565bbf0da6f0011b821c3c23a7525e7, 0x32542927b7ed3982a2b82ade14d24667efc1df37a6a225261ee74c416c502babdf749a0bda8219dfa919c336551f2f9640a29ca26fece2c966d45e7d26f955ee01a9815e22880cc33db000849120ab, 0x3adfe24ba7e6c683cda6700f0b17fabd086e9807cb6acb8719ec6dbd98de8942e57db02fb0df9721d26708429e2746200f4686c98a9e4d6b3bf81bf5df0bb86a695a07815f2f4cca2332e8580bfe999,
  0x3bff49585107d76d4489762acbf5489366696c620048abaa080d9dc11a30c446ce199a5866d05fbe56d577c8e7b4090750ad9ffb5d65a62c8c0d8dad141941415761a2982cc824c99debc7fdcf532076, 0x357c814b671c789bce07d30db5909cde59688691ee03a43234945a08d027fbb26f6ef4b85898eb727e3285be13420539e38f77deb28b711d544508a2667e4d85d28f18d95495ce0c12dda2055f2845ec2, 0x29df358e7f7b8626638d243b6f0b3f328740f60ced0bcb72eb1557a5c166a5fa54b1a3bb058e9aed2ee19608ed79a0533453fcb0cc0cabd32e66be3701d1d369014c03b67d3900ac696bebf633414e9ed2,
  0x1ce2d7ad53dd240225c4468a78b0bfe4a881ca636158acedbb3b8c2d337110b1e58edc70d274afc28ad89c63e4385586f9206aed1ff36558452e1b39955285f419ea4387b1adf93a7e99f3ec1d0fe3f08a6, 0x119df3fe7a6ac24efc1f1a12cb66fda1a500c05d3a955503760275ee8123ca6e059684004befb89bfbb781e2070f4422cb7c5f56e27fa3b751a5bf6860f717677b12620a6a8072adb2f7c450ad0eb9142143, 0x986bee40539a5c4f9f0dd33d81f2a48cf896a490a2fa5203c94935498ba23458877c4a54574a7de28a59ac9a849cab74eed53b62466cac73c8b242be1bac4fc532f02f52a5c8c98e8277251280e699c2b229,
  0x49469f82b497624dc47b97ae71c748d8db8148f0b88259b8a70614099fa17e676b5e0a31164cc743b0548d974b6e346c6a0875e7c0abcf1097a74ae83cfeae7a9f374c35073503cbd6ccb5f7706db4df5164d, 0x1f653e174395d634392e47b2b102bc41f325d7c64d79990eace8ab19c75ed1e8da2c8436fc9dddb591c49841874c8271787f906e4316ecf426a66cd630ebe1c97b7bd36113c2f2203502a785ea4b6ad6c5b7af, 0xc04021171b39271dc56a9a75718be9e2ebd8b0f637e6dab1f30f0d63c4a0d077d926f703a0d3e047be8b3432776f5e2fe71078984b9bd1a2a0afc086b576207746d00beef40e958cbcabb4e1962a1843022e84,
  0x41dc32604a77536e620c10d07e8c18ef67b01c1d74a84b395549256a0ad9e945be66e6c0b0835cd03d23be9e590f5bf368c897e0aa4105d2a6b4139146a20d2ab76d47761c04066ed015f28b3167d5c2c80604c, 0x143bd95b79c7f08363d70b9435e0927627738ce554718b9dca0bc32fd0e215759ea299e78a69ae1ec751f836f2b6cee26c844ed1bbb0c77984737b2313d6eaf9775cd3ee64b723ac7d70f7f262c20cb81d636d8c, 0x595a22d04407c627708221340e0d6314c6782d333df607a2045eeae932c587e650d013edd377f59b32a21fe1a7c27b355c4b3c9ddae8256ab7948ed3da6e168f5cc92a7c2e325571e294a41a3bb1c6d97dec7644,
  0x163097160f8d425fc80f9e683cc256d7f43a4b04fa3a076b3efdae7c41242abac67b2e5d3545a71e5f7f73e1b7314d8187188ac7be4fb151fb84d5f9241c45a7bd077e4138f3996a0f65405be501b883473af4ac1, 0x4f730118ce57bfdf9ee6d9968b4a48fbb3e9bff16a20b261a3bf2a90655fba04f5d7926f56f0b31226c2c127e89b91130949cff07e50ba14fac4419ea2712b0a6e5514f6bbf4b08973b452e5f825b3646677adc83, 0x100a9829f024c10700427c0ad2f7b5dab6824f9a22af3475c7a155976319b924587cf7e175704612b5e6a9a40e932fe1303046ec4f79ebc061b15885624eda1da5a7783edf134143a74b2091f6688cd024bf184407,
  0x2ed00c07866f09d1ac47c917aeb280fd816819e0555e4aba904ddb365d3e28d011327b2633775401a6fffbd4a844a9ccb640e8d7cc0681a9c4b712c6f32a5592f8d442c670cde83ab20dc750aa1d95de2c4ccadb4d, 0x7b89731a1eeff1585397b09243e29af91a441145c5e4cac848523bd9d2ffd753b1cc144beabc6b51e46cb3db13d1771a74b43df1f6fbb9be09512997a0834c3f3234034e8225dd6a72cf216c9ee6761e9773f3eb92, 0x12716f9b40226528dcc27c76db53903050af822fd81ba71d9b3adf3f177feab1b326d3804dc1713691965d186ba9a26cab1aa4216450a55ddb69a3af095acef03f09babead8261979551a7ca531e94fa6ed37ac4a56,
  0x27e8f32da2bc2dc9ce798ba307e12fd27433305fdf3145b8e1e5d258bc5672f9372575351b4119b81841f96456b7d22ba2937de7506250771576f1c3a86a1092188354ea4fd8545dc113da943aad5e15741d549da66, 0x4e4bbc96a5b30fce3ffa9cfd7bf08d0f00caf76c6758175d240df6307d64b01f92c8c06f1720156984abaec44ca779499cd3ba81cc2b9e74dda7d051366700bcaea580dc1b99f2f541696243ad3a000696d3b99c3c2, 0x8b57aa370fb0d055a5e0f58891aa33feaeccfdf2cea8a5853f1ca6ce7f02ac99a36bb78fef5aabf4fb7607d124e95f90b6a704c39ac1fa6dc7dc6d079b8d515efcbd627ac6690092c1efb055f77feaf8860e9312fc7,
  0xe11641fecea7b59dc691f00331cb553dbbaf7d6ba90799ce852d288e319eac4b3a6a898f2eb936f72e08ea2aeb9e79ec89678740357d818b52781f7d38488ecec3dcdcae8cdc513767a280dce42dfd6919d5c1f43f5, 0x14a2ab53f3652662baa90218e14ea9558578f3a8f5e235efd21811a188623a74d08e8c521c9d3539cdfd7055d69b0295cb9ee4f91009db3ddab4d8970645e2c3d5da54e85a3490647a0d9f0432b3b58e19d37bb77999, 0x1b7eef211c260a2c3be145bcee4a8fadaf90af05eb8fcb94fdb0db094f1c08f4595aae7abe4c5da607e429219d65bfe0151d6676635d74c87431a1932a8d1f4d57c4c18cf63fbe76f5da5d99eb4d907fe9081c587ab3,
  0x214a14b99340e56fa4880539bc1f0491762310caff2ecfaaa0866b39949d6745d4210704446d7984f9dccf9bf3002c154483859fd2c451b4035df463b8a12e25f55989a7e9d430904f9b9d87a7d062bfa8458204b9d0, 0x24a09cfb57cd445caa41e66f435b051dfff6dd6daa41e9d3909dd76c9c13db3286273d21b1db1234eb0a797e92947b4a7a2fc08b82d7464f8261bd6b29555fb92b38123b3665317372ca283075e35794a0ed4495e870, 0x24a09cfb57cd445caa41e66f435b051dfff6dd6daa41e9d3909dd76c9c13db3286273d21b1db1234eb0a797e92947b4a7a2fc08b82d7464f8261bd6b29555fb92b38123b3665317372ca283075e35794a0ed4495e870,
  0x214a14b99340e56fa4880539bc1f0491762310caff2ecfaaa0866b39949d6745d4210704446d7984f9dccf9bf3002c154483859fd2c451b4035df463b8a12e25f55989a7e9d430904f9b9d87a7d062bfa8458204b9d0, 0x1b7eef211c260a2c3be145bcee4a8fadaf90af05eb8fcb94fdb0db094f1c08f4595aae7abe4c5da607e429219d65bfe0151d6676635d74c87431a1932a8d1f4d57c4c18cf63fbe76f5da5d99eb4d907fe9081c587ab3, 0x14a2ab53f3652662baa90218e14ea9558578f3a8f5e235efd21811a188623a74d08e8c521c9d3539cdfd7055d69b0295cb9ee4f91009db3ddab4d8970645e2c3d5da54e85a3490647a0d9f0432b3b58e19d37bb77999,
  0xe11641fecea7b59dc691f00331cb553dbbaf7d6ba90799ce852d288e319eac4b3a6a898f2eb936f72e08ea2aeb9e79ec89678740357d818b52781f7d38488ecec3dcdcae8cdc513767a280dce42dfd6919d5c1f43f5, 0x8b57aa370fb0d055a5e0f58891aa33feaeccfdf2cea8a5853f1ca6ce7f02ac99a36bb78fef5aabf4fb7607d124e95f90b6a704c39ac1fa6dc7dc6d079b8d515efcbd627ac6690092c1efb055f77feaf8860e9312fc7, 0x4e4bbc96a5b30fce3ffa9cfd7bf08d0f00caf76c6758175d240df6307d64b01f92c8c06f1720156984abaec44ca779499cd3ba81cc2b9e74dda7d051366700bcaea580dc1b99f2f541696243ad3a000696d3b99c3c2,
  0x27e8f32da2bc2dc9ce798ba307e12fd27433305fdf3145b8e1e5d258bc5672f9372575351b4119b81841f96456b7d22ba2937de7506250771576f1c3a86a1092188354ea4fd8545dc113da943aad5e15741d549da66, 0x12716f9b40226528dcc27c76db53903050af822fd81ba71d9b3adf3f177feab1b326d3804dc1713691965d186ba9a26cab1aa4216450a55ddb69a3af095acef03f09babead8261979551a7ca531e94fa6ed37ac4a56, 0x7b89731a1eeff1585397b09243e29af91a441145c5e4cac848523bd9d2ffd753b1cc144beabc6b51e46cb3db13d1771a74b43df1f6fbb9be09512997a0834c3f3234034e8225dd6a72cf216c9ee6761e9773f3eb92,
  0x2ed00c07866f09d1ac47c917aeb280fd816819e0555e4aba904ddb365d3e28d011327b2633775401a6fffbd4a844a9ccb640e8d7cc0681a9c4b712c6f32a5592f8d442c670cde83ab20dc750aa1d95de2c4ccadb4d, 0x100a9829f024c10700427c0ad2f7b5dab6824f9a22af3475c7a155976319b924587cf7e175704612b5e6a9a40e932fe1303046ec4f79ebc061b15885624eda1da5a7783edf134143a74b2091f6688cd024bf184407, 0x4f730118ce57bfdf9ee6d9968b4a48fbb3e9bff16a20b261a3bf2a90655fba04f5d7926f56f0b31226c2c127e89b91130949cff07e50ba14fac4419ea2712b0a6e5514f6bbf4b08973b452e5f825b3646677adc83,
  0x163097160f8d425fc80f9e683cc256d7f43a4b04fa3a076b3efdae7c41242abac67b2e5d3545a71e5f7f73e1b7314d8187188ac7be4fb151fb84d5f9241c45a7bd077e4138f3996a0f65405be501b883473af4ac1, 0x595a22d04407c627708221340e0d6314c6782d333df607a2045eeae932c587e650d013edd377f59b32a21fe1a7c27b355c4b3c9ddae8256ab7948ed3da6e168f5cc92a7c2e325571e294a41a3bb1c6d97dec7644, 0x143bd95b79c7f08363d70b9435e0927627738ce554718b9dca0bc32fd0e215759ea299e78a69ae1ec751f836f2b6cee26c844ed1bbb0c77984737b2313d6eaf9775cd3ee64b723ac7d70f7f262c20cb81d636d8c,
  0x41dc32604a77536e620c10d07e8c18ef67b01c1d74a84b395549256a0ad9e945be66e6c0b0835cd03d23be9e590f5bf368c897e0aa4105d2a6b4139146a20d2ab76d47761c04066ed015f28b3167d5c2c80604c, 0xc04021171b39271dc56a9a75718be9e2ebd8b0f637e6dab1f30f0d63c4a0d077d926f703a0d3e047be8b3432776f5e2fe71078984b9bd1a2a0afc086b576207746d00beef40e958cbcabb4e1962a1843022e84, 0x1f653e174395d634392e47b2b102bc41f325d7c64d79990eace8ab19c75ed1e8da2c8436fc9dddb591c49841874c8271787f906e4316ecf426a66cd630ebe1c97b7bd36113c2f2203502a785ea4b6ad6c5b7af,
  0x49469f82b497624dc47b97ae71c748d8db8148f0b88259b8a70614099fa17e676b5e0a31164cc743b0548d974b6e346c6a0875e7c0abcf1097a74ae83cfeae7a9f374c35073503cbd6ccb5f7706db4df5164d, 0x986bee40539a5c4f9f0dd33d81f2a48cf896a490a2fa5203c94935498ba23458877c4a54574a7de28a59ac9a849cab74eed53b62466cac73c8b242be1bac4fc532f02f52a5c8c98e8277251280e699c2b229, 0x119df3fe7a6ac24efc1f1a12cb66fda1a500c05d3a955503760275ee8123ca6e059684004befb89bfbb781e2070f4422cb7c5f56e27fa3b751a5bf6860f717677b12620a6a8072adb2f7c450ad0eb9142143,
  0x1ce2d7ad53dd240225c4468a78b0bfe4a881ca636158acedbb3b8c2d337110b1e58edc70d274afc28ad89c63e4385586f9206aed1ff36558452e1b39955285f419ea4387b1adf93a7e99f3ec1d0fe3f08a6, 0x29df358e7f7b8626638d243b6f0b3f328740f60ced0bcb72eb1557a5c166a5fa54b1a3bb058e9aed2ee19608ed79a0533453fcb0cc0cabd32e66be3701d1d369014c03b67d3900ac696bebf633414e9ed2, 0x357c814b671c789bce07d30db5909cde59688691ee03a43234945a08d027fbb26f6ef4b85898eb727e3285be13420539e38f77deb28b711d544508a2667e4d85d28f18d95495ce0c12dda2055f2845ec2,
  0x3bff49585107d76d4489762acbf5489366696c620048abaa080d9dc11a30c446ce199a5866d05fbe56d577c8e7b4090750ad9ffb5d65a62c8c0d8dad141941415761a2982cc824c99debc7fdcf532076, 0x3adfe24ba7e6c683cda6700f0b17fabd086e9807cb6acb8719ec6dbd98de8942e57db02fb0df9721d26708429e2746200f4686c98a9e4d6b3bf81bf5df0bb86a695a07815f2f4cca2332e8580bfe999, 0x32542927b7ed3982a2b82ade14d24667efc1df37a6a225261ee74c416c502babdf749a0bda8219dfa919c336551f2f9640a29ca26fece2c966d45e7d26f955ee01a9815e22880cc33db000849120ab,
  0x254ef017ddd1e16a876cb7a7cd272efb871bd59ad7e1db519a2fdf39756bb50531e861d1eb7f155379472a03368ef2db22d9000b00218aef35dfbf3507787c565bbf0da6f0011b821c3c23a7525e7, 0x17dcbbc188307f494749d87836dc5237bb0bfa71b57e74c55ce8c2ddedc3f03453c96a8994406416de4487b62f407ff30eefa93e4c64e82b276c88ea3bf7993c84af9dbec4d5e42027ec1e68ff4d, 0xd187b00d957fbc70631f27e100c78abf5ab68dc25f5b3d352a517c09278bfe979a5faf1c0243c1b5376af7c4665e0a3d258d00b1d4319c64b73c6c0f1bce6412c5616f77fe3cffe75f4500cdd8,
  0x6210e5625fd33a81b354649e01e4154acf408afe89a88d3ba48edd9b4ff3284a175a153f16c7e599958faa1b2e92ca1230424617072d6941b7dd04fd28713f77e86b7f6e256076b4c2392ac08, 0x26e101b82175ef2da1df593db82a1dc8491fd3dcbe19f9e3191491363dea124114d973f83b5591e900d930b4c2a3098bf952692730e4aeecd26790a0f44caf0407068962ec03cc94d24c6d08, 0xcf5933bd7667ec4d194577518a8dc662b5fd254410a80c115baf15ad6338d77cb95916197b0500f42870963db41e5f891a5e6ec4d887447b0d70ae9c1c17e755f262e4c4238983b2d090d8,
  0x39a043be343a8529b036d3f892d0db43859b41b2fa06dede06dafd03ba42e2ff07eaaae1e1dccf1b4e76ce4ad8faa919190a8198d489cf1c3bc58f3bf7e2ca590ab965385e707a443b4bf, 0xd3ac8e5fd38cf6e10f8267388223dfbf2d24630edf99c93cf6481a5ba0ddeac38c2de0f20ef8c16d5002db06ac9e8509ee36682283fd37449b15b32896f224f48a0e0bda79c7a98853d, 0x27b9f4c9f595123d4b637696760ad95fcbb0447f7b86a9cb8e09333be84a7a110cfb3609d3484325866bd26f2f1f735e18da49a865f9b43cae40e6808b880d4e4db513e4fb6d5be7a9,
  0x6061d63c25c1bd8b8285332a1bd1539716adb538f39624eb836ec2e88d59bee6f1a134524cf871897e1d9ec785b71d2113e97e90f60001705d8765b7ea3db7899baf962a225a9a03, 0xba708aecd81c2919600444154269b33748547d771bed1baa4f01d562972e5a517f7b1fc98b90a24aa00189a2728d71a7872d0cc7d3fe4d94755268d3398440632f0ab163caa1e2, 0x11b3dac8f5d0d3a039dd9cd97535b3b1f2c8ff4da4d94738303a8fcdef5f49eaeabcdff6655b910c77e08224b79cde1fc3f85a4a96c6a3162535e8626c45f5b4ddfac7dcba7c6,
  0x14c2d5089c0db9797c7b43121348d79eaee142f93fa5782ce749f4eee1a1c6c8073535955a7655cc216af3f69c83bcd73a4b52d0aa5cfe4060a365b4977a404505b0c565176, 0x126d648a223eb01a259f1bc6944c3104ebe0699d3b9ecc9fc8a716af350d427591219a0cd236f0224529987affda39d00b6b08b10cab2542dee0df75989b0109f9f41d6f2, 0xc19346ac89cdb387dc84644de4319578fe89b863c0890ab7e23eef71ca9ed8bd7b5f1e54f3d0522fa682073d20734fd543a0e3c5c44b20e3c08178e160f2c2c5fb0711,
  0x5b893722bb2a8433ca5edad8f43d120cf236b27f529ee4ea9ee0e169b8b67cef6c0edd4760b20d3c97d559ffeb1aa70784597dbf9651acb1a56406501675220b9a53, 0x1e36f0039bd971064e2dd9f5e5ee14bf086bc99cdb059c504c9cf68aa6b3a0945d88d27e538839f2153e65bc64bccd6a4f3b2c225b294021f4e749070998ecf0df, 0x6b5729440556eae685ab640f66273a788ac4ed8dd20a9571a26f96bc7070da40c55fa56aca29d1335d6ac9617ab5226d08eb194763c41286cedd8b9802e18b5,
  0xf56c173be8a9b0151a4cafb0ca4c44b83e3fc9eccfe7b3034d3c488251528805f9a0a7b4082a7355c8dfa430c80ceb875a299d86daaf465a6327e1dcabbc, 0x1566491067825b46a1ac3c3ebd97965debd810ff028bb2c856eaeda8a61411c1e0b4319c97707a42ecb1837591106a052428bf616cce18c65e39f5d674, 0x1112595e45d2d3b31918d0c8449db61fdfcd46cae4083da421f3ea8a9d6039e0de157e66bc65dc47d5c5c5e1d71d68abeaa61e211011ee8f00e1a34,
  0x730404cda28aa046449b0a8203b74c2c2b9e8f45daaae78e297cdbf9e4d014e104cc2cb24cd5839df3a895ef3516652b387cbfe4d53b82ed6fc, 0x1721041b711d2818b7f81433eaf3f8820177095472b54a7fcb4030a2f2247a11d1f17f7d908dff0c2fd6bed04b3b83702d6d1fab3693361b, 0x1f4d5c4f7d6f72011395fd5512e8eaf3eb12c539ccaf57ab37a8fd03d7b2ee7ba06ed4e8e54e7debb5b0ac754ba562db442da2dc7811,
  0xf1f90fb248f3cd7028176c0ce5c4a991f7fd5ee496d821b1912dfbab45c2dda7da52d8edfca3d535ea7cba7bc244afcb9aae23d, 0x219af71bcf92202c66cf99b62cf33bb400c4f531fa275bb1ec092744c5164adc0b2c88c9566f88d1a19cf2644ad674a129f, 0xffff78e88cd34ce348ffa1d06686d76cca37f48f7a388bcad45fe5c4474ce4d2b670df68945faca32d6b78418b6d6,
  0x114aae21333652eb836635e7e5951c7b48a7486016292669367bd870d6ba914c34f6c9e49d378c246b1a9b62, 0x17304eab63bb789f94dd329608480b855df1df334d2cc303d83b9a64f7d407bff7d0cf9bd7b9d8912, 0xf209787b377d6b84c06a4a5e2b9bce4f150ae4a55438c230fa2369553585a39746eab7e6,
  0xfffffffffff4ad6992b501356f9d038dd625ba629fa115e4bcca3b4054b65d, 0x17304eb2c6a575e41ac10a9327780b02ceac400692fb63c0f7, 0xfffffffffffffffffffffffffffff83,
  0x1]

private theorem eulerianCoefficients_eq : descentCoeffs 124 = eulerianCoefficients := by
  decide +kernel

private theorem upper : upperOK (descentCoeffs 124) first gaps = true := by
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

private theorem lower (i : Fin (lastRepresentative 125 - 2)) :
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

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 125) :
    StrictNegativeInterlacing (originalQuotient 125 k) (eulerian 124) 122 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N125
