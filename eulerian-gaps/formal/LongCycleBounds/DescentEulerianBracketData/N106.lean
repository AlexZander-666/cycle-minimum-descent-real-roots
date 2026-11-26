import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentPackedData.C127L112.N106

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N106

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L112.N106 LongCycleBounds.DescentNecklace.Packed.C127L112.N106.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L112.N106 LongCycleBounds.DescentNecklace.Packed.C127L112.N106.rows

private theorem actual : RepresentativeChecks 106 previousNodes rows :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L112.N106 LongCycleBounds.DescentNecklace.Packed.C127L112.N106.dataChecks

private def first : LongCycleFinite.Dyadic := ⟨-40564819207303340847894502572032, 0⟩

private def gaps : List Window := [
  ⟨⟨-40563503896011600131352422252544, 0⟩, ⟨-3414784048709500928, 0⟩⟩,
  ⟨⟨-2261871340195676160, 0⟩, ⟨-13181489512448, 0⟩⟩,
  ⟨⟨-13046634250240, 0⟩, ⟨-14976712704, 0⟩⟩,
  ⟨⟨-14378598400, 0⟩, ⟨-198249984, 0⟩⟩,
  ⟨⟨-197527552, 0⟩, ⟨-9883648, 0⟩⟩,
  ⟨⟨-9874112, 0⟩, ⟨-1088316, 0⟩⟩,
  ⟨⟨-1087856, 0⟩, ⟨-199962, 0⟩⟩,
  ⟨⟨-199914, 0⟩, ⟨-417057, 3⟩⟩,
  ⟨⟨-416993, 3⟩, ⟨-279265, 4⟩⟩,
  ⟨⟨-139617, 3⟩, ⟨-224907, 5⟩⟩,
  ⟨⟨-28111, 2⟩, ⟨-208433, 6⟩⟩,
  ⟨⟨-208419, 6⟩, ⟨-215425, 7⟩⟩,
  ⟨⟨-430827, 8⟩, ⟨-485543, 9⟩⟩,
  ⟨⟨-485521, 9⟩, ⟨-146671, 8⟩⟩,
  ⟨⟨-146665, 8⟩, ⟨-93805, 8⟩⟩,
  ⟨⟨-375207, 10⟩, ⟨-503155, 11⟩⟩,
  ⟨⟨-125785, 9⟩, ⟨-350933, 11⟩⟩,
  ⟨⟨-350923, 11⟩, ⟨-253065, 11⟩⟩,
  ⟨⟨-253059, 11⟩, ⟨-375503, 12⟩⟩,
  ⟨⟨-375495, 12⟩, ⟨-71371, 10⟩⟩,
  ⟨⟨-142739, 11⟩, ⟨-110835, 11⟩⟩,
  ⟨⟨-110833, 11⟩, ⟨-350625, 13⟩⟩,
  ⟨⟨-350619, 13⟩, ⟨-281787, 13⟩⟩,
  ⟨⟨-140891, 12⟩, ⟨-229689, 13⟩⟩,
  ⟨⟨-459371, 14⟩, ⟨-379139, 14⟩⟩,
  ⟨⟨-189567, 13⟩, ⟨-316397, 14⟩⟩,
  ⟨⟨-316393, 14⟩, ⟨-266647, 14⟩⟩,
  ⟨⟨-266643, 14⟩, ⟨-453397, 15⟩⟩,
  ⟨⟨-28337, 11⟩, ⟨-97127, 13⟩⟩,
  ⟨⟨-48563, 12⟩, ⟨-10477, 10⟩⟩,
  ⟨⟨-83815, 13⟩, ⟨-145575, 14⟩⟩,
  ⟨⟨-291147, 15⟩, ⟨-508577, 16⟩⟩,
  ⟨⟨-127143, 14⟩, ⟨-446473, 16⟩⟩,
  ⟨⟨-111617, 14⟩, ⟨-196885, 15⟩⟩,
  ⟨⟨-196883, 15⟩, ⟨-174373, 15⟩⟩,
  ⟨⟨-348743, 16⟩, ⟨-310037, 16⟩⟩,
  ⟨⟨-310033, 16⟩, ⟨-276563, 16⟩⟩,
  ⟨⟨-17285, 12⟩, ⟨-61865, 14⟩⟩,
  ⟨⟨-494915, 17⟩, ⟨-444061, 17⟩⟩,
  ⟨⟨-444057, 17⟩, ⟨-399413, 17⟩⟩,
  ⟨⟨-199705, 16⟩, ⟨-180023, 16⟩⟩,
  ⟨⟨-360043, 17⟩, ⟨-81299, 15⟩⟩,
  ⟨⟨-325193, 17⟩, ⟨-294229, 17⟩⟩,
  ⟨⟨-294227, 17⟩, ⟨-266615, 17⟩⟩,
  ⟨⟨-266613, 17⟩, ⟨-483819, 18⟩⟩,
  ⟨⟨-483815, 18⟩, ⟨-109869, 16⟩⟩,
  ⟨⟨-27467, 14⟩, ⟨-399571, 18⟩⟩,
  ⟨⟨-24973, 14⟩, ⟨-363563, 18⟩⟩,
  ⟨⟨-45445, 15⟩, ⟨-330993, 18⟩⟩,
  ⟨⟨-165495, 17⟩, ⟨-301465, 18⟩⟩,
  ⟨⟨-301463, 18⟩, ⟨-137319, 17⟩⟩,
  ⟨⟨-68659, 16⟩, ⟨-500439, 19⟩⟩,
  ⟨⟨-500435, 19⟩, ⟨-455907, 19⟩⟩,
  ⟨⟨-455903, 19⟩, ⟨-103809, 17⟩⟩,
  ⟨⟨-811, 10⟩, ⟨-378035, 19⟩⟩,
  ⟨⟨-23627, 15⟩, ⟨-343969, 19⟩⟩,
  ⟨⟨-171983, 18⟩, ⟨-9773, 14⟩⟩,
  ⟨⟨-312733, 19⟩, ⟨-142037, 18⟩⟩,
  ⟨⟨-284071, 19⟩, ⟨-515499, 20⟩⟩,
  ⟨⟨-515495, 20⟩, ⟨-467117, 20⟩⟩,
  ⟨⟨-233557, 19⟩, ⟨-422637, 20⟩⟩,
  ⟨⟨-422633, 20⟩, ⟨-381729, 20⟩⟩,
  ⟨⟨-381725, 20⟩, ⟨-344107, 20⟩⟩,
  ⟨⟨-43013, 17⟩, ⟨-77377, 18⟩⟩,
  ⟨⟨-309505, 20⟩, ⟨-138851, 19⟩⟩,
  ⟨⟨-277699, 20⟩, ⟨-496959, 21⟩⟩,
  ⟨⟨-248477, 20⟩, ⟨-443303, 21⟩⟩,
  ⟨⟨-221649, 20⟩, ⟨-394099, 21⟩⟩,
  ⟨⟨-394095, 21⟩, ⟨-87259, 19⟩⟩,
  ⟨⟨-43629, 18⟩, ⟨-307837, 21⟩⟩,
  ⟨⟨-153917, 20⟩, ⟨-270245, 21⟩⟩,
  ⟨⟨-270241, 21⟩, ⟨-472061, 22⟩⟩,
  ⟨⟨-59007, 19⟩, ⟨-102487, 20⟩⟩,
  ⟨⟨-51243, 19⟩, ⟨-353763, 22⟩⟩,
  ⟨⟨-353759, 22⟩, ⟨-303135, 22⟩⟩,
  ⟨⟨-303131, 22⟩, ⟨-515445, 23⟩⟩,
  ⟨⟨-515439, 23⟩, ⟨-434395, 23⟩⟩,
  ⟨⟨-434389, 23⟩, ⟨-90627, 21⟩⟩,
  ⟨⟨-362503, 23⟩, ⟨-37399, 20⟩⟩,
  ⟨⟨-299187, 23⟩, ⟨-487747, 24⟩⟩,
  ⟨⟨-121935, 22⟩, ⟨-391993, 24⟩⟩,
  ⟨⟨-195993, 23⟩, ⟨-310013, 24⟩⟩,
  ⟨⟨-38751, 21⟩, ⟨-481439, 25⟩⟩,
  ⟨⟨-481431, 25⟩, ⟨-183007, 24⟩⟩,
  ⟨⟨-366007, 25⟩, ⟨-271557, 25⟩⟩,
  ⟨⟨-271551, 25⟩, ⟨-48957, 23⟩⟩,
  ⟨⟨-12239, 21⟩, ⟨-273167, 26⟩⟩,
  ⟨⟨-34145, 23⟩, ⟨-366301, 27⟩⟩,
  ⟨⟨-366291, 27⟩, ⟨-58569, 25⟩⟩,
  ⟨⟨-468539, 28⟩, ⟨-4423, 22⟩⟩,
  ⟨⟨-283063, 28⟩, ⟨-159505, 28⟩⟩,
  ⟨⟨-318999, 29⟩, ⟨-41215, 27⟩⟩,
  ⟨⟨-329707, 30⟩, ⟨-152779, 30⟩⟩,
  ⟨⟨-305545, 31⟩, ⟨-492213, 33⟩⟩,
  ⟨⟨-246095, 32⟩, ⟨-82393, 32⟩⟩,
  ⟨⟨-329555, 34⟩, ⟨-5371, 30⟩⟩,
  ⟨⟨-343723, 36⟩, ⟨-505331, 39⟩⟩,
  ⟨⟨-252649, 38⟩, ⟨-445431, 42⟩⟩,
  ⟨⟨-445399, 42⟩, ⟨-178077, 45⟩⟩,
  ⟨⟨-11129, 41⟩, ⟨-304535, 52⟩⟩,
  ⟨⟨-152255, 51⟩, ⟨-351401, 62⟩⟩,
  ⟨⟨-351371, 62⟩, ⟨-195803, 79⟩⟩,
  ⟨⟨-195785, 79⟩, ⟨-262149, 123⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private def eulerianCoefficients : List ℤ := [
  0x1, 0x1ffffffffffffffffffffffff96, 0x55b0c1891ff99735f89f9de4daaef2f873b23ae520,
  0x3ffffffffdc84cfdd38c2a737590de89f3d738f65201833a32f6a, 0xdf3d5e8140f653e1a3959da884f92f7040d463af96b0a12e3af9438bf8e06, 0xab617d4b4960bf29915386f5034496449cfaa0cf70739337b64f775eca9508bee29a,
  0x6d4ecbe4a4aee8a840920da4309814aeee8b0b5db058dfbb62f84858154ec0e3d7efb6e4a0, 0x7ffd2bd50bed7058e00c6a269160b360366b95a1382054f393237b35f63eadb1e5faf36d336f366, 0x1cab8a990645b634b1da183cbd6edca6239e94418192a95785701004b76aa4d434a1944be58724d3f445,
  0x1bdbcc1adf584e5b3aace6eafcb0473d4a604ba0eb9d0ff294354665a63db42c19cb2c6f0d46d01fac948c08, 0x967aa1fec978f12e8bb2865945454607783f9b63c00a450ba8d09665ab079051cd533b01825b35df4fd51aba700, 0x152dbb037eeefb00ee682207ae331bf36b1e6581590aed1c586f045e4b6a9a5d2f010aeb122ec4aa6943fd430ffacf8,
  0x16cfdfb879f45587f7ea3ea75b4426e17392e1e1514680534ab9ba91a9c72bffb111e20b036c4a7eed2f39f8dd00c7cc58, 0xd10ea33d7fd7c137c1890db7856d9431c46d1d1e6361d1c6ff50551a5403a6c1b8ac6b7213898f9387934e62750b5f2e2098, 0x4530aacc3fc6acf36aef6c4da9c14ca0d801f1f0baf5db2f5066e462c2fd827db753aba7ddc1bf05ebe0c4e9a09a11e4af0cc00,
  0xe233ef85aaebd661cbb37242c4e8e2a0d85c124606bbbe928e3b1f6d9126bbd751487bc48d67205a87cac190a4a34f4bc99482268, 0x1e1acc56dad8f5d01ad467e6c76872b72773f8cb030eaa8c662878b4bbc0506ac8fb27cd592a7e25d654a26f7897e95d16044ab4b766, 0x2b9faf2178036db695805786712aac0776037ba0ea3ad502b9cbd4b0c81fce25453640e8ace68a88f7031bf5c7087f9dff073cbf9ac95c,
  0x2c9b7a6e30c2f9d8ca001063ca109353622cf7d16a5eaacf9c1e226604c05f65760e4addf47458223e407e27eb1e686f1969206a21b1e4c0, 0x212e00766511c4c6672e0c54592325221874c2fb7a538492d6e5219cb44150ad1a0f78dd8722a7349521dadb9bf129c15590a63e9876ed29a4, 0x126b3b9b78d6e0f2a1d983fd32bc6f98ce1f55b69c05066506b21b7f7cbfd0d4e176732c95cff4719b3adaef945e3c95e160f8df5d979724f34c,
  0x7ccb27ac7e6857bd1286f62757cff707d4d42eecaebbdfc792e8c003d63bba809dbbb681dad00c6e4c57c4458576031f3192a9dce9f654072d9e4, 0x291310b8002d19fcf135cca032264ca18089c03677139ccc5339453d2a3cb202952f961b88e5d697aa5a622f3f4dea16bc8b83631d455bc4e7c4ec0, 0xaae17218df7710216eba5a66874f9826f2eaa940955680be587996594a3199a6f5258e3393e0303fc8a1e2b424580d5142faf426ce74ac52f1d24d1c,
  0x2399a000d0c5c8ce5170de695bbf84adaab9f9da304956d95800cbe9a2a549dba772e10a0fe24d36b8394d38104a1a429b28015964b68c97ff590b8456, 0x604347120733bed6fc13f7b8c813a23338d150e05f5e5b0629545e584c6c9c00b7f3b7ae44e07e6f5c2ba9bac79ed10fc9db9a5b5038f0aeec47deef348, 0xd57661b1b8d9f9eda64d4f363bd56b5d35efd94f3da96d373be0866cf28e28bca35a4cc5678388931022666e8e5bdf9daf74ef7a3b642af8bb8747746800,
  0x187f05ec7991998a97d06fe78abc10063be663b3f69c0aa05a8b73e3a57efd323760e921771da9a0e011bdcccb53f329f5a8bedf67ead8eef08c838e975bb8, 0x258fa5ae062a8475511d9a8909c84f281635d9c16e57771eb3bb46a1ccd4d4ba0689d7c7fc58ec10b0d13d5dd823800e681f2fbe331bd12bd8356b81639d2f8, 0x3076fcfe73fcb4296dc4a411cd0dc184305f48b6a7679e8d2e839851317d0968c98d371483672077c41bc5d94db74619ccbd5ac8b5de0273bef7d3391b688b98,
  0x34fafec2315898d18e9fe95a50e52e862005af8dafa5c6d312b3a9066c8f70d841ec81d90a2a5d0ec1dc15c3d46c12889474fa62deff2ebc75324ac7e81c9ff00, 0x315e70f78c69db900a0d68178ee2f424bdf459ae545c62fb95ca2452dc90beef8360856b7e138f7a7cf4429ab6f191f3691f0363690c13bae5f1fefe42420f3168, 0x276de28bbe67f86fdf79ab1cda4aeec33c50f67ecc2dbdf9a6ae5956cada68058071f5722e7a50c7d990df841850b941558a281cd4a38189c3d19546df549c245a3,
  0x1b1fb263d3d1ecee927a3e5df92c6657741917c6efae953fe87f0ebeeb8815138e1952b84f22afebf183a0a960780bd13a3524db1b5666401c1399fe9b3f582a6d1a, 0x1024922e401ab966f08b9cc7631c27828078c68ac758783553c909703db80291cfa8695e976400ecc0c36e1093afea99a7a01476cda270129faa86333c6f77b065660, 0x8586d8bb3390a004104b6b82da10fb612a83e4eb2ca0bbfee383716efde9c48fda63af45b2ecad82c4c81ae0a73a4535c404ccebda07b5b3ddc47b2b574faed0076e6,
  0x3c2de12db29fdb4b0ad7888350336b7ee10284ea2700f74b5e3f721b788fb839179ff2f56b8b6426f3640cdd4185be0ee2f91bc3cb3c4b94290c58fda39d3b7a08e29a, 0x17b8e08c818b198188c7d55ac733e688b4f76c30d6bf8b720bb787ac51c1e079d97f9334d604057b5d43166fc4c4d4587eee35538270adc0d3779e151bed939f5e84cd6, 0x833f85afad35c78a86d6cb6046d0e136fdcccf4726da78cee173ff92411e22e971b4f51d877c6ee0160ac1f0cf2d93740b4aac1fa2392ffccab69008f432f265ded03e0,
  0x27eb33e2bf154cb1ffb51cc9e442877eb02a8ee0abdc436de7a1103037a97118e327a5a6398f3c4d0e8e0fa4cb1e34d14a08074f92d46cccc1fe652ba850ad3550233a2a, 0xab4583060f2dc6ccaf6ebb69577e8ba2d8c480129933ce7d5e6f11eb38dfbcb389a2830372408ab0492d5bd17011d58dde5e76a90731508c5ae47cfc66841cd0d2a99af7, 0x28946dcf8a8cbd1d2a5c98583e4564f724805de866e1d91391c5f48486541690398382949004c4e3fc9cec02e77aaf8b5986a2e13e181bca67c46c699399d0af4c5fec390,
  0x882f00345678173c0718d42928dfcfaceaafcdcf6427cb6fdccc2ebc85bc8a321d34d5b4d591ea11e96961b88e4720e2538677d1adefe4b89f59c8c095236be5c7607d200, 0x19546ce4bf2a18de36e40b44540973d5323c86e23f29f22201f4a2d5011ae9b5703aebdd0ade1c079848e5e03030520e6c853a1f2cd6eefe9bbe0157b3f2e6ab0325e13670, 0x42f236c4a69272e1acbfe173d72c3294dce43b842b73a282d349a4c3cba8db5b65f18404b3dd2dd8a3a695769c366b5f76fcbd02af63cca3bf1b84b31c071ce8ffe571e8b0,
  0x9d591bc8fd0d7922d539ed8c53b2203db781a222f2c24a71813f7a1a969a87b8927911847ffa8b29fb4c3fb279add2e512546741512011078802ac42943dccf6ba9878c4b0, 0x149421f8b9e3452d3647cf336a713574f03b6eec2d7d49f71d5df2ceabb0a745bae5f77a704c62652311c272b6eb64bf021b4188c7a97e4add4abca46401eccd1a5fece5400, 0x26602b686c587bfbfa347d553da7824133187048b3e82ec8b039f2fbde3fa0eff068e2e27fda0508269d5e53b8ce9a63fb30e594c789f96d77ef642c7248933edbce782b950,
  0x3fd40a9fc2f93ec29c33e21a913dd1a124eab62c2d5dc44858044d22e01dd30951d0bc1e3c058490c58a9069a4ae628c185580313514cb5dc8d27b0f4603ab12a63f3ffef64, 0x5ebfc7b14f6505c81a07c1142ac5d67e792af58c1041cbb74a15d3839101f258062db1873d5c255d1e0a9b588cec9262090ef4c5dab52d944083b2a24d13516f8db25b1ff48, 0x7d97a2664629e145649a634ca8706e675623c6af5d61675d933ad7f5ad326afeebc357d98522ead4bcabb651696630b312076eb25c4241e3ff1301b20d8880f294c3a3ba880,
  0x94b529d36b982e3496dbb03f2469a6e1d4a2bfea8274f8f691e5fb7408317b5a76a48e2a90d80838f7a7bd3c2ecda8f49d9b14f95094960848297a40f6e552fe41b2acd76b8, 0x9d5188061654921fdac5baa7fff31f2acf7061eda598303c15c00898ecda40727d6ca510395dcb567a69d8d4fae4302e0be6df962737cde712ebea747d027ffa89dc13e2828, 0x94b529d36b982e3496dbb03f2469a6e1d4a2bfea8274f8f691e5fb7408317b5a76a48e2a90d80838f7a7bd3c2ecda8f49d9b14f95094960848297a40f6e552fe41b2acd76b8,
  0x7d97a2664629e145649a634ca8706e675623c6af5d61675d933ad7f5ad326afeebc357d98522ead4bcabb651696630b312076eb25c4241e3ff1301b20d8880f294c3a3ba880, 0x5ebfc7b14f6505c81a07c1142ac5d67e792af58c1041cbb74a15d3839101f258062db1873d5c255d1e0a9b588cec9262090ef4c5dab52d944083b2a24d13516f8db25b1ff48, 0x3fd40a9fc2f93ec29c33e21a913dd1a124eab62c2d5dc44858044d22e01dd30951d0bc1e3c058490c58a9069a4ae628c185580313514cb5dc8d27b0f4603ab12a63f3ffef64,
  0x26602b686c587bfbfa347d553da7824133187048b3e82ec8b039f2fbde3fa0eff068e2e27fda0508269d5e53b8ce9a63fb30e594c789f96d77ef642c7248933edbce782b950, 0x149421f8b9e3452d3647cf336a713574f03b6eec2d7d49f71d5df2ceabb0a745bae5f77a704c62652311c272b6eb64bf021b4188c7a97e4add4abca46401eccd1a5fece5400, 0x9d591bc8fd0d7922d539ed8c53b2203db781a222f2c24a71813f7a1a969a87b8927911847ffa8b29fb4c3fb279add2e512546741512011078802ac42943dccf6ba9878c4b0,
  0x42f236c4a69272e1acbfe173d72c3294dce43b842b73a282d349a4c3cba8db5b65f18404b3dd2dd8a3a695769c366b5f76fcbd02af63cca3bf1b84b31c071ce8ffe571e8b0, 0x19546ce4bf2a18de36e40b44540973d5323c86e23f29f22201f4a2d5011ae9b5703aebdd0ade1c079848e5e03030520e6c853a1f2cd6eefe9bbe0157b3f2e6ab0325e13670, 0x882f00345678173c0718d42928dfcfaceaafcdcf6427cb6fdccc2ebc85bc8a321d34d5b4d591ea11e96961b88e4720e2538677d1adefe4b89f59c8c095236be5c7607d200,
  0x28946dcf8a8cbd1d2a5c98583e4564f724805de866e1d91391c5f48486541690398382949004c4e3fc9cec02e77aaf8b5986a2e13e181bca67c46c699399d0af4c5fec390, 0xab4583060f2dc6ccaf6ebb69577e8ba2d8c480129933ce7d5e6f11eb38dfbcb389a2830372408ab0492d5bd17011d58dde5e76a90731508c5ae47cfc66841cd0d2a99af7, 0x27eb33e2bf154cb1ffb51cc9e442877eb02a8ee0abdc436de7a1103037a97118e327a5a6398f3c4d0e8e0fa4cb1e34d14a08074f92d46cccc1fe652ba850ad3550233a2a,
  0x833f85afad35c78a86d6cb6046d0e136fdcccf4726da78cee173ff92411e22e971b4f51d877c6ee0160ac1f0cf2d93740b4aac1fa2392ffccab69008f432f265ded03e0, 0x17b8e08c818b198188c7d55ac733e688b4f76c30d6bf8b720bb787ac51c1e079d97f9334d604057b5d43166fc4c4d4587eee35538270adc0d3779e151bed939f5e84cd6, 0x3c2de12db29fdb4b0ad7888350336b7ee10284ea2700f74b5e3f721b788fb839179ff2f56b8b6426f3640cdd4185be0ee2f91bc3cb3c4b94290c58fda39d3b7a08e29a,
  0x8586d8bb3390a004104b6b82da10fb612a83e4eb2ca0bbfee383716efde9c48fda63af45b2ecad82c4c81ae0a73a4535c404ccebda07b5b3ddc47b2b574faed0076e6, 0x1024922e401ab966f08b9cc7631c27828078c68ac758783553c909703db80291cfa8695e976400ecc0c36e1093afea99a7a01476cda270129faa86333c6f77b065660, 0x1b1fb263d3d1ecee927a3e5df92c6657741917c6efae953fe87f0ebeeb8815138e1952b84f22afebf183a0a960780bd13a3524db1b5666401c1399fe9b3f582a6d1a,
  0x276de28bbe67f86fdf79ab1cda4aeec33c50f67ecc2dbdf9a6ae5956cada68058071f5722e7a50c7d990df841850b941558a281cd4a38189c3d19546df549c245a3, 0x315e70f78c69db900a0d68178ee2f424bdf459ae545c62fb95ca2452dc90beef8360856b7e138f7a7cf4429ab6f191f3691f0363690c13bae5f1fefe42420f3168, 0x34fafec2315898d18e9fe95a50e52e862005af8dafa5c6d312b3a9066c8f70d841ec81d90a2a5d0ec1dc15c3d46c12889474fa62deff2ebc75324ac7e81c9ff00,
  0x3076fcfe73fcb4296dc4a411cd0dc184305f48b6a7679e8d2e839851317d0968c98d371483672077c41bc5d94db74619ccbd5ac8b5de0273bef7d3391b688b98, 0x258fa5ae062a8475511d9a8909c84f281635d9c16e57771eb3bb46a1ccd4d4ba0689d7c7fc58ec10b0d13d5dd823800e681f2fbe331bd12bd8356b81639d2f8, 0x187f05ec7991998a97d06fe78abc10063be663b3f69c0aa05a8b73e3a57efd323760e921771da9a0e011bdcccb53f329f5a8bedf67ead8eef08c838e975bb8,
  0xd57661b1b8d9f9eda64d4f363bd56b5d35efd94f3da96d373be0866cf28e28bca35a4cc5678388931022666e8e5bdf9daf74ef7a3b642af8bb8747746800, 0x604347120733bed6fc13f7b8c813a23338d150e05f5e5b0629545e584c6c9c00b7f3b7ae44e07e6f5c2ba9bac79ed10fc9db9a5b5038f0aeec47deef348, 0x2399a000d0c5c8ce5170de695bbf84adaab9f9da304956d95800cbe9a2a549dba772e10a0fe24d36b8394d38104a1a429b28015964b68c97ff590b8456,
  0xaae17218df7710216eba5a66874f9826f2eaa940955680be587996594a3199a6f5258e3393e0303fc8a1e2b424580d5142faf426ce74ac52f1d24d1c, 0x291310b8002d19fcf135cca032264ca18089c03677139ccc5339453d2a3cb202952f961b88e5d697aa5a622f3f4dea16bc8b83631d455bc4e7c4ec0, 0x7ccb27ac7e6857bd1286f62757cff707d4d42eecaebbdfc792e8c003d63bba809dbbb681dad00c6e4c57c4458576031f3192a9dce9f654072d9e4,
  0x126b3b9b78d6e0f2a1d983fd32bc6f98ce1f55b69c05066506b21b7f7cbfd0d4e176732c95cff4719b3adaef945e3c95e160f8df5d979724f34c, 0x212e00766511c4c6672e0c54592325221874c2fb7a538492d6e5219cb44150ad1a0f78dd8722a7349521dadb9bf129c15590a63e9876ed29a4, 0x2c9b7a6e30c2f9d8ca001063ca109353622cf7d16a5eaacf9c1e226604c05f65760e4addf47458223e407e27eb1e686f1969206a21b1e4c0,
  0x2b9faf2178036db695805786712aac0776037ba0ea3ad502b9cbd4b0c81fce25453640e8ace68a88f7031bf5c7087f9dff073cbf9ac95c, 0x1e1acc56dad8f5d01ad467e6c76872b72773f8cb030eaa8c662878b4bbc0506ac8fb27cd592a7e25d654a26f7897e95d16044ab4b766, 0xe233ef85aaebd661cbb37242c4e8e2a0d85c124606bbbe928e3b1f6d9126bbd751487bc48d67205a87cac190a4a34f4bc99482268,
  0x4530aacc3fc6acf36aef6c4da9c14ca0d801f1f0baf5db2f5066e462c2fd827db753aba7ddc1bf05ebe0c4e9a09a11e4af0cc00, 0xd10ea33d7fd7c137c1890db7856d9431c46d1d1e6361d1c6ff50551a5403a6c1b8ac6b7213898f9387934e62750b5f2e2098, 0x16cfdfb879f45587f7ea3ea75b4426e17392e1e1514680534ab9ba91a9c72bffb111e20b036c4a7eed2f39f8dd00c7cc58,
  0x152dbb037eeefb00ee682207ae331bf36b1e6581590aed1c586f045e4b6a9a5d2f010aeb122ec4aa6943fd430ffacf8, 0x967aa1fec978f12e8bb2865945454607783f9b63c00a450ba8d09665ab079051cd533b01825b35df4fd51aba700, 0x1bdbcc1adf584e5b3aace6eafcb0473d4a604ba0eb9d0ff294354665a63db42c19cb2c6f0d46d01fac948c08,
  0x1cab8a990645b634b1da183cbd6edca6239e94418192a95785701004b76aa4d434a1944be58724d3f445, 0x7ffd2bd50bed7058e00c6a269160b360366b95a1382054f393237b35f63eadb1e5faf36d336f366, 0x6d4ecbe4a4aee8a840920da4309814aeee8b0b5db058dfbb62f84858154ec0e3d7efb6e4a0,
  0xab617d4b4960bf29915386f5034496449cfaa0cf70739337b64f775eca9508bee29a, 0xdf3d5e8140f653e1a3959da884f92f7040d463af96b0a12e3af9438bf8e06, 0x3ffffffffdc84cfdd38c2a737590de89f3d738f65201833a32f6a,
  0x55b0c1891ff99735f89f9de4daaef2f873b23ae520, 0x1ffffffffffffffffffffffff96, 0x1]

private theorem eulerianCoefficients_eq : descentCoeffs 105 = eulerianCoefficients := by
  decide +kernel

private theorem upper : upperOK (descentCoeffs 105) first gaps = true := by
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

private theorem lower (i : Fin (lastRepresentative 106 - 2)) :
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

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 106) :
    StrictNegativeInterlacing (originalQuotient 106 k) (eulerian 105) 103 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N106
