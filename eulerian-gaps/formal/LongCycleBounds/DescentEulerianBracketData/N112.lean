import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentPackedData.C127L112.N112

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N112

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L112.N112 LongCycleBounds.DescentNecklace.Packed.C127L112.N112.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L112.N112 LongCycleBounds.DescentNecklace.Packed.C127L112.N112.rows

private theorem actual : RepresentativeChecks 112 previousNodes rows :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L112.N112 LongCycleBounds.DescentNecklace.Packed.C127L112.N112.dataChecks

private def first : LongCycleFinite.Dyadic := ⟨-2596148429267413814265248164610048, 0⟩

private def gaps : List Window := [
  ⟨⟨-2596064249344742408406555024162816, 0⟩, ⟨-35182753607715913728, 0⟩⟩,
  ⟨⟨-35110625644933808128, 0⟩, ⟨-74751758303232, 0⟩⟩,
  ⟨⟨-73354551754752, 0⟩, ⟨-58404110336, 0⟩⟩,
  ⟨⟨-55037919232, 0⟩, ⟨-595263488, 0⟩⟩,
  ⟨⟨-592549888, 0⟩, ⟨-25134912, 0⟩⟩,
  ⟨⟨-25105920, 0⟩, ⟨-2452144, 0⟩⟩,
  ⟨⟨-2450952, 0⟩, ⟨-410856, 0⟩⟩,
  ⟨⟨-410747, 0⟩, ⟨-398471, 2⟩⟩,
  ⟨⟨-398403, 2⟩, ⟨-503391, 4⟩⟩,
  ⟨⟨-251665, 3⟩, ⟨-386433, 5⟩⟩,
  ⟨⟨-193199, 4⟩, ⟨-172055, 5⟩⟩,
  ⟨⟨-344085, 6⟩, ⟨-343849, 7⟩⟩,
  ⟨⟨-85957, 5⟩, ⟨-47061, 5⟩⟩,
  ⟨⟨-188235, 7⟩, ⟨-443743, 9⟩⟩,
  ⟨⟨-110931, 7⟩, ⟨-277749, 9⟩⟩,
  ⟨⟨-277739, 9⟩, ⟨-365485, 10⟩⟩,
  ⟨⟨-365473, 10⟩, ⟨-501447, 11⟩⟩,
  ⟨⟨-501433, 11⟩, ⟨-178175, 10⟩⟩,
  ⟨⟨-356341, 11⟩, ⟨-65243, 9⟩⟩,
  ⟨⟨-130483, 10⟩, ⟨-392257, 12⟩⟩,
  ⟨⟨-49031, 9⟩, ⟨-301463, 12⟩⟩,
  ⟨⟨-301457, 12⟩, ⟨-472469, 13⟩⟩,
  ⟨⟨-472461, 13⟩, ⟨-376609, 13⟩⟩,
  ⟨⟨-188301, 12⟩, ⟨-152365, 12⟩⟩,
  ⟨⟨-304725, 13⟩, ⟨-499721, 14⟩⟩,
  ⟨⟨-499713, 14⟩, ⟨-207295, 13⟩⟩,
  ⟨⟨-51823, 11⟩, ⟨-347581, 14⟩⟩,
  ⟨⟨-43447, 11⟩, ⟨-294145, 14⟩⟩,
  ⟨⟨-294141, 14⟩, ⟨-502043, 15⟩⟩,
  ⟨⟨-502037, 15⟩, ⟨-107921, 13⟩⟩,
  ⟨⟨-431679, 15⟩, ⟨-46715, 12⟩⟩,
  ⟨⟨-93429, 13⟩, ⟨-162765, 14⟩⟩,
  ⟨⟨-162763, 14⟩, ⟨-285129, 15⟩⟩,
  ⟨⟨-142563, 14⟩, ⟨-251001, 15⟩⟩,
  ⟨⟨-501997, 16⟩, ⟨-221967, 15⟩⟩,
  ⟨⟨-221965, 15⟩, ⟨-12319, 11⟩⟩,
  ⟨⟨-98551, 14⟩, ⟨-351363, 16⟩⟩,
  ⟨⟨-351359, 16⟩, ⟨-314243, 16⟩⟩,
  ⟨⟨-2455, 9⟩, ⟨-281913, 16⟩⟩,
  ⟨⟨-140955, 15⟩, ⟨-507231, 17⟩⟩,
  ⟨⟨-253613, 16⟩, ⟨-457471, 17⟩⟩,
  ⟨⟨-457467, 17⟩, ⟨-413535, 17⟩⟩,
  ⟨⟨-413531, 17⟩, ⟨-93647, 15⟩⟩,
  ⟨⟨-46823, 14⟩, ⟨-169965, 16⟩⟩,
  ⟨⟨-339927, 17⟩, ⟨-77247, 15⟩⟩,
  ⟨⟨-308985, 17⟩, ⟨-281267, 17⟩⟩,
  ⟨⟨-17579, 13⟩, ⟨-128181, 16⟩⟩,
  ⟨⟨-32045, 14⟩, ⟨-116959, 16⟩⟩,
  ⟨⟨-58479, 15⟩, ⟨-106821, 16⟩⟩,
  ⟨⟨-427281, 18⟩, ⟨-195277, 17⟩⟩,
  ⟨⟨-195275, 17⟩, ⟨-44651, 15⟩⟩,
  ⟨⟨-357205, 18⟩, ⟨-163435, 17⟩⟩,
  ⟨⟨-326867, 18⟩, ⟨-299215, 18⟩⟩,
  ⟨⟨-74803, 16⟩, ⟨-136977, 17⟩⟩,
  ⟨⟨-8561, 13⟩, ⟨-501689, 19⟩⟩,
  ⟨⟨-501685, 19⟩, ⟨-229669, 18⟩⟩,
  ⟨⟨-229667, 18⟩, ⟨-210237, 18⟩⟩,
  ⟨⟨-210235, 18⟩, ⟨-384761, 19⟩⟩,
  ⟨⟨-192379, 18⟩, ⟨-175955, 18⟩⟩,
  ⟨⟨-351907, 19⟩, ⟨-80415, 17⟩⟩,
  ⟨⟨-321657, 19⟩, ⟨-293777, 19⟩⟩,
  ⟨⟨-146887, 18⟩, ⟨-67015, 17⟩⟩,
  ⟨⟨-268057, 19⟩, ⟨-244323, 19⟩⟩,
  ⟨⟨-244321, 19⟩, ⟨-444807, 20⟩⟩,
  ⟨⟨-111201, 18⟩, ⟨-404319, 20⟩⟩,
  ⟨⟨-404315, 20⟩, ⟨-5733, 14⟩⟩,
  ⟨⟨-91727, 18⟩, ⟨-166177, 19⟩⟩,
  ⟨⟨-332351, 20⟩, ⟨-300435, 20⟩⟩,
  ⟨⟨-18777, 16⟩, ⟨-270961, 20⟩⟩,
  ⟨⟨-270959, 20⟩, ⟨-243763, 20⟩⟩,
  ⟨⟨-243761, 20⟩, ⟨-218685, 20⟩⟩,
  ⟨⟨-218683, 20⟩, ⟨-195581, 20⟩⟩,
  ⟨⟨-195579, 20⟩, ⟨-348651, 21⟩⟩,
  ⟨⟨-43581, 18⟩, ⟨-309597, 21⟩⟩,
  ⟨⟨-154797, 20⟩, ⟨-34223, 18⟩⟩,
  ⟨⟨-273781, 21⟩, ⟨-482027, 22⟩⟩,
  ⟨⟨-482023, 22⟩, ⟨-211103, 21⟩⟩,
  ⟨⟨-211101, 21⟩, ⟨-367763, 22⟩⟩,
  ⟨⟨-367759, 22⟩, ⟨-79595, 20⟩⟩,
  ⟨⟨-39797, 19⟩, ⟨-68441, 20⟩⟩,
  ⟨⟨-8555, 17⟩, ⟨-58407, 20⟩⟩,
  ⟨⟨-467251, 23⟩, ⟨-395419, 23⟩⟩,
  ⟨⟨-197707, 22⟩, ⟨-331513, 23⟩⟩,
  ⟨⟨-331509, 23⟩, ⟨-137517, 22⟩⟩,
  ⟨⟨-137515, 22⟩, ⟨-28189, 20⟩⟩,
  ⟨⟨-451017, 24⟩, ⟨-364945, 24⟩⟩,
  ⟨⟨-364939, 24⟩, ⟨-290899, 24⟩⟩,
  ⟨⟨-145447, 23⟩, ⟨-455919, 25⟩⟩,
  ⟨⟨-56989, 22⟩, ⟨-350383, 25⟩⟩,
  ⟨⟨-43797, 22⟩, ⟨-131663, 24⟩⟩,
  ⟨⟨-263321, 25⟩, ⟨-96423, 24⟩⟩,
  ⟨⟨-96421, 24⟩, ⟨-34261, 23⟩⟩,
  ⟨⟨-137041, 25⟩, ⟨-188025, 26⟩⟩,
  ⟨⟨-47005, 24⟩, ⟨-494839, 28⟩⟩,
  ⟨⟨-247413, 27⟩, ⟨-77433, 26⟩⟩,
  ⟨⟨-309723, 28⟩, ⟨-91267, 27⟩⟩,
  ⟨⟨-713, 20⟩, ⟨-49965, 27⟩⟩,
  ⟨⟨-199853, 29⟩, ⟨-199715, 30⟩⟩,
  ⟨⟨-199707, 30⟩, ⟨-177835, 31⟩⟩,
  ⟨⟨-355655, 32⟩, ⟨-68263, 31⟩⟩,
  ⟨⟨-136519, 32⟩, ⟨-344925, 35⟩⟩,
  ⟨⟨-344907, 35⟩, ⟨-83647, 35⟩⟩,
  ⟨⟨-41821, 34⟩, ⟨-448447, 40⟩⟩,
  ⟨⟨-224209, 39⟩, ⟨-87523, 41⟩⟩,
  ⟨⟨-87517, 41⟩, ⟨-474135, 48⟩⟩,
  ⟨⟨-118525, 46⟩, ⟨-19903, 50⟩⟩,
  ⟨⟨-159211, 53⟩, ⟨-250067, 64⟩⟩,
  ⟨⟨-125023, 63⟩, ⟨-137519, 82⟩⟩,
  ⟨⟨-68753, 81⟩, ⟨-262149, 129⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private def eulerianCoefficients : List ℤ := [
  0x1, 0x7fffffffffffffffffffffffff90, 0xf404571f7c0dc1bc64fe88a0b2bc31e581768978a933,
  0x3fffffffff953e19e239b9fb3137d0a439b1cdaa2b975c23db3d1ee0, 0x353978b1b0747aa59c99d6c15349b52750a0bd7a2e76120972fab82ac98f6d529, 0x7a022a1b2bb9fef90324bd0ef40f92f003fcbe3ff7aa9e98809dd1a135f2fee15f740cf0,
  0xc43a7b376b1186c9c8eb94db2cbf547fb4a88bac4cdafa95c800b8275b2c4aeeecc706cb4af0c3, 0x1fffaa265e4fdb9b50bfdfd05825440e91b4c9b29214921fb3953f8016ab2eeb5e81e751c6d563aad140, 0xe88a463977cbebfa8c647b7ec2ee615f76c6db9951a53138d90ac0132780b91a5b47908004287acad5f7fd87,
  0x1a9660605cff98783d448476cb062202a48c64917a70510627c7acb82c0d5413cb63d5fc94593cbe0f77a78b45f30, 0xfeb991a9afe7a6968d76df0657ba9cec40c616291b26c7117e0b251dccc4285159f0cca94a7680d9d0dfa8de250bca35, 0x3c917b817d98912127485e9b77f69cfcd519818270dd2f2837f88fa0a63091d47150b594b298d9235547f035d67b0d1db260,
  0x69e23bce4b5553271a8ae1f65e1765129132c657a491c8a32068d3144cf080e584395143e316dc2cdc19d199315576e66695757, 0x5f324bd61458bb2c80559cfd24bf1f152198823279c3c9fca648a2f945186808088a08e889bbce561f284939f1bdea5f15b9388b50, 0x301706c0939eddf364969c5eaa4cfd7a03e8c8f569f2870cd5c2f084dd213deadace5042b6b204ed3fac4d0c6f46a33e044faa64ba38d,
  0xea6154c5c1098f5d9b7b413edf56ffe874c0e3916f1f60f912f517aa60739ac4fe701ce02dca862756ba0f88b2ec66e4a74ad2e7db33d00, 0x2d951800d717bbc29bbf86400bb6e45f782e3a49ad2d818fe0f421ff865794f0a51ea582bf33f299e2eb49d5fc3aeaf480ed054e866f158dae, 0x5ee5a0832580221273c264e16163d260a10b6e27df0198e2c4a06b95d9e06321956061fa93c43813119247e40976aa513f6affa714f0a2704ce0,
  0x896824d51b517a8bd137f4477096d656216483950adff30f2923b7838d016cb1b414a8aa754ba413aabfb45dca0e3b46144687eff85cf510e478ea, 0x8ef13030839959cdff7843d2e947bd9aa93120299460d044ad6b0ef6c782b57ac76ebac669747142b8938793ef61eeae818565105e51e9e4c1c28d40, 0x6dcdb002043c5385970b85bd4e135e1c25d32af2068c13dab4eac94c6a6e83be024758076fce3b750a912f5c9060c00700fe5c5272db09099046f5bafe,
  0x3fc1866181b517cf78a24f29e1e3e322cc5010e15eb9ad400646e65c64ac2bd902081ec3928d9db9c089880df61c3507d42151f8c7b30756d40a8dcd4220, 0x1c8c73920d9f9def366d9d9ee1e3cc9a3a0397fd0881a4eae0491b7b9bd2f454c17160b513346f97b395c252b1f056c9b709d163445b1c864d31ece7065e2a, 0xa07ed14364818accf4bf34d3f0026238242bde608224c87ff5e522925092209fcb0a5b3a5879e15ddd22476f14d61e6d2943ca1a2d0b5ca30e5ed7fdc96fa80,
  0x2cec4445860cd0daae5e259982cab1a5e2201211ada9c93c50098396fae4485bda770b109a19de17dc7282b4c3c5f79edc0ee8fec095c2519e5e1eca2871f811a, 0xa265e3791e8ca743433d926d7375c110c57ec5600621024ce9f95a1a1fc52d67f28d368a0ba76db992cdfc4575377e35412b30ac7f0d839d1e71c2cf055727d920, 0x1df6fecd973867c2b2b10ff5abfd6ebc9cf8bb6089b7bb36974a5ae1553b6b8f1846b51f9ef5baf9e677bf825d7078fcae20231ddf77cceadb808f2c0c246fa1a8ce,
  0x48fda340dda11a9ab5ba893da70ab4bd622afd143d1a2ac12e3d166bf25e53edbb0ac59f7993af78a166c4a407b9677593312bead7d1471d74a21cb2ab59a58187f40, 0x940bc957e7ce13da183ef7f6810cee6566405fe6f3cee1071ccf2290d4398711dd11da3fcc4c190e56807e42b8d1fe9f6e3028217ecec6ff02f3a88d39f6e145c1ca5a, 0xfc14213835cd70fff2a6caad57fe3674cbcfa6d0ad5ec828034df8bf44187466bf4f9d7faed5200f9af326c4d768cd7a3ad8ce61a25f2c6bf05ec34d49c9e09245b7de0,
  0x16af429eed569684b714b159c286346d643c5be97c02869c7667e715e3df8bf9b7e35b3c91aeb1b295a0f9d16ee42cc1881f6becfe116cd16f3909dd69c22b538235c6d7e, 0x1bcd1dc8b38c7040b67996d26f14f0f7e500672c6c357e4fef2a4d446ddf0bdfc0c3891b8a35852a528936a0b4d9f82fdd68b2e811904f0de22fcff5676d0ee4cfcd3b4900, 0x1d2c20f1233fbde256cade79021901055bec648c640b267c79dd5b5ebc0fa21d56174051ecc8a71cd11ac550493cfb2d42166da83f2190b39ca0a371a85f94dced876379bcb,
  0x1a594e8ca4ef456e07737399d6c4419ff81fb2bfc7bb35ea7c300c63600d0494973f7999ff5a1421a93523b497c02ef48344e02b6ed9401089d8a3bee8523701f5a666e74c30, 0x14956128c5231d2dd9354ede3ea4f9da79a29a43bc94e5b33b118f60241462aa5a6a1bfd9793c64dbb2ac8303bc5434d22c05985a3119fd910a9aa80ce4860231586d2eee94b1, 0xdf7cd78cf1fbf1962b2fac76b4c4ee38e6a55bdd4ff36c5b498bb025b430f284f4b1bf7767ee55dac03ed6b51a024f1bcd1250ea0ff7efc8128df505fe902729898ac48b968a0,
  0x84432316b2a0893ec210daffe0c584dd224141176d9eff582b7776ba16db624b012b13bd46a45bdbc1ea7ee3ff2a8c59524d7d9338efd1398a6f7bf4a51fd91bba3f5be012fda3, 0x4481ff4d16d83484425b43d225e4affc97a4865274362ea0f540866a825a46239332a788e5087cbf806226fc491656d316f092b0c7095bc89e3e64cb2330a08c7bac150624d2550, 0x1f28918535a5a50b0f26f20ec9b0d47cc4a82b482b0122e0f6ab1300918019c6677cd01a96afa7ece7dbf0a80231da66434e7b2c75e3113462d81ad876d588efd20d01a616a10e41,
  0xc7af3f997567822589c30cd7ad45104ec8dbe457362864a6f8343953d282bd91c94cbf3cdde22614a8af8ee2680ad025481079f35e87111d3cc4d340dd6b76a3f879d1e034fefac0, 0x46a05b282cdd219a46a0c0733a1ddb571d285e9ea2487e85fbd29ef62e71ec7dee0d766959ca12e8f5046efb90b9fed1d85a0729e34781a062b783235987b1c4064411839f7f9ee15, 0x161c876b8b2d32ba8b0cb348e2ce85acad7875d761adf71b658b265360d60da36db39d0386d4ec65247d40d88b2ebd3535c6610cf1815dacd64fcf7b64b755f5549ec45827c16dc090,
  0x6242101b8f0d62172f67b46c0d898ca122f0305ed771ae6a987ebbafe52d954c06508f4703b03a5c132e3bba6721da1e97dd0adad15698d27c02a672be84c99f2363623445565766df, 0x1841dbd38cff934e5c1cdefa75adff5a1eb55d988f57d02eee54b4de24267579e40151b38948d0d18c790a053b875cfe50d4484a0a3ffaf28823d8135636c89409386bec3ad3ce64a20, 0x55520c53ab67d62524b110f6f0403e7746f46047f66f5a07b3a6faec338270cce2bf6d6c3d326e35914bde686d049faf04876e9ab05e81431dd4ac0afc9d5f888655392c45fce46d365,
  0x10ba8397e5b0b175f4c1026fec4b042e2c991201ed554b5ec0e27d8e46b1d1111b290cd17f3f6c6b3146e75363dd7c7a8a9358c8f673fdf27b95d6c670fa635d9e0be0a7a67a561286f0, 0x2edf6075a9d66cda5916999c1e613d5203f0a8438b32e5b21c517f374cba5219484d6656ef536993ac0e377df4d72564ac0a77db52f17476d27a6807dec8a3251ebf8d51312b13e11587, 0x7573e641f1e767bb43735b124b52c2feceb46011b11f3d67f0f80f159c7fc6002a1ae254e5cd7f391e3a3c228c88007474b69fdd9381c84b253de5a9817a99e2e52c7e52fad1f4f87a00,
  0x1077f241fdb0a0f1f49ead956ff4845521aef38af67a4a5417fa2d3796646de822235679adda79c7e29dee576affb2debb604adffab52196637381c57c992c8646783941944cdf9395ff4, 0x211c0ec451fddbb512ac1d2111da3a927fee07b3542b615979ad58c2c255d39aa86ca4ec8993d58667c55c7c4cdf43dd7407bbf7b0325d903b2b608cf743ec1c70d9a81760ab7952ad740, 0x3bb407518f92dabcd633633f95acdce8d669392049fe1af69b4fe41cd488223896953e94ae7e0b73ac1339ffa20ea8f91427d557e56aa260289ca54b50bf92262a114493d1c56cb55e41c,
  0x609fd26b29416e012e78a33a7ece2f6eb0b947a491355c8d0618f25395b8441f34d667e56a86611ee3cb5b97b3c0cec1184c2eebdfec5f918915ff703ea3e901daf02adbe29a8582a6f80, 0x8c6e412685341d811a838c52321c5882711a0d7a3eaa2c6a64f2a5b567ac198c50b061a9d633007bafd27ae4ffc254a1ce48c5dc091b9c5f1e0e80e9409af41bb726028531f22f9e80854, 0xb75cf27a7d64bc95ed8cd1a2ed6f6d33cf41d6999ea6d008514ec18d244b52884215db9e261d3777e4d49b34d5465f64594ddd225add6597d159a1ce3eca9fc0f8b11f34594344cfe92c0,
  0xd729e47290bcf701f7b4b55041b731a7b6a2518ab93fd7228fd544c672dffa0bf6d0be300dc01aceb2f113d820312e8ee0b7bb63d594f640b82003e9e6114983e5d7c9f4ebe5171ec861c, 0xe2f0d2a0b1b6b8b35725585fef84da774b2f5e94292420c0158c77d6f551560cb86983efabf43c113874f1379d8ca4239ef0f6c64a25da41f564f9a2dadb7517c52a19a3129b4d5b07300, 0xd729e47290bcf701f7b4b55041b731a7b6a2518ab93fd7228fd544c672dffa0bf6d0be300dc01aceb2f113d820312e8ee0b7bb63d594f640b82003e9e6114983e5d7c9f4ebe5171ec861c,
  0xb75cf27a7d64bc95ed8cd1a2ed6f6d33cf41d6999ea6d008514ec18d244b52884215db9e261d3777e4d49b34d5465f64594ddd225add6597d159a1ce3eca9fc0f8b11f34594344cfe92c0, 0x8c6e412685341d811a838c52321c5882711a0d7a3eaa2c6a64f2a5b567ac198c50b061a9d633007bafd27ae4ffc254a1ce48c5dc091b9c5f1e0e80e9409af41bb726028531f22f9e80854, 0x609fd26b29416e012e78a33a7ece2f6eb0b947a491355c8d0618f25395b8441f34d667e56a86611ee3cb5b97b3c0cec1184c2eebdfec5f918915ff703ea3e901daf02adbe29a8582a6f80,
  0x3bb407518f92dabcd633633f95acdce8d669392049fe1af69b4fe41cd488223896953e94ae7e0b73ac1339ffa20ea8f91427d557e56aa260289ca54b50bf92262a114493d1c56cb55e41c, 0x211c0ec451fddbb512ac1d2111da3a927fee07b3542b615979ad58c2c255d39aa86ca4ec8993d58667c55c7c4cdf43dd7407bbf7b0325d903b2b608cf743ec1c70d9a81760ab7952ad740, 0x1077f241fdb0a0f1f49ead956ff4845521aef38af67a4a5417fa2d3796646de822235679adda79c7e29dee576affb2debb604adffab52196637381c57c992c8646783941944cdf9395ff4,
  0x7573e641f1e767bb43735b124b52c2feceb46011b11f3d67f0f80f159c7fc6002a1ae254e5cd7f391e3a3c228c88007474b69fdd9381c84b253de5a9817a99e2e52c7e52fad1f4f87a00, 0x2edf6075a9d66cda5916999c1e613d5203f0a8438b32e5b21c517f374cba5219484d6656ef536993ac0e377df4d72564ac0a77db52f17476d27a6807dec8a3251ebf8d51312b13e11587, 0x10ba8397e5b0b175f4c1026fec4b042e2c991201ed554b5ec0e27d8e46b1d1111b290cd17f3f6c6b3146e75363dd7c7a8a9358c8f673fdf27b95d6c670fa635d9e0be0a7a67a561286f0,
  0x55520c53ab67d62524b110f6f0403e7746f46047f66f5a07b3a6faec338270cce2bf6d6c3d326e35914bde686d049faf04876e9ab05e81431dd4ac0afc9d5f888655392c45fce46d365, 0x1841dbd38cff934e5c1cdefa75adff5a1eb55d988f57d02eee54b4de24267579e40151b38948d0d18c790a053b875cfe50d4484a0a3ffaf28823d8135636c89409386bec3ad3ce64a20, 0x6242101b8f0d62172f67b46c0d898ca122f0305ed771ae6a987ebbafe52d954c06508f4703b03a5c132e3bba6721da1e97dd0adad15698d27c02a672be84c99f2363623445565766df,
  0x161c876b8b2d32ba8b0cb348e2ce85acad7875d761adf71b658b265360d60da36db39d0386d4ec65247d40d88b2ebd3535c6610cf1815dacd64fcf7b64b755f5549ec45827c16dc090, 0x46a05b282cdd219a46a0c0733a1ddb571d285e9ea2487e85fbd29ef62e71ec7dee0d766959ca12e8f5046efb90b9fed1d85a0729e34781a062b783235987b1c4064411839f7f9ee15, 0xc7af3f997567822589c30cd7ad45104ec8dbe457362864a6f8343953d282bd91c94cbf3cdde22614a8af8ee2680ad025481079f35e87111d3cc4d340dd6b76a3f879d1e034fefac0,
  0x1f28918535a5a50b0f26f20ec9b0d47cc4a82b482b0122e0f6ab1300918019c6677cd01a96afa7ece7dbf0a80231da66434e7b2c75e3113462d81ad876d588efd20d01a616a10e41, 0x4481ff4d16d83484425b43d225e4affc97a4865274362ea0f540866a825a46239332a788e5087cbf806226fc491656d316f092b0c7095bc89e3e64cb2330a08c7bac150624d2550, 0x84432316b2a0893ec210daffe0c584dd224141176d9eff582b7776ba16db624b012b13bd46a45bdbc1ea7ee3ff2a8c59524d7d9338efd1398a6f7bf4a51fd91bba3f5be012fda3,
  0xdf7cd78cf1fbf1962b2fac76b4c4ee38e6a55bdd4ff36c5b498bb025b430f284f4b1bf7767ee55dac03ed6b51a024f1bcd1250ea0ff7efc8128df505fe902729898ac48b968a0, 0x14956128c5231d2dd9354ede3ea4f9da79a29a43bc94e5b33b118f60241462aa5a6a1bfd9793c64dbb2ac8303bc5434d22c05985a3119fd910a9aa80ce4860231586d2eee94b1, 0x1a594e8ca4ef456e07737399d6c4419ff81fb2bfc7bb35ea7c300c63600d0494973f7999ff5a1421a93523b497c02ef48344e02b6ed9401089d8a3bee8523701f5a666e74c30,
  0x1d2c20f1233fbde256cade79021901055bec648c640b267c79dd5b5ebc0fa21d56174051ecc8a71cd11ac550493cfb2d42166da83f2190b39ca0a371a85f94dced876379bcb, 0x1bcd1dc8b38c7040b67996d26f14f0f7e500672c6c357e4fef2a4d446ddf0bdfc0c3891b8a35852a528936a0b4d9f82fdd68b2e811904f0de22fcff5676d0ee4cfcd3b4900, 0x16af429eed569684b714b159c286346d643c5be97c02869c7667e715e3df8bf9b7e35b3c91aeb1b295a0f9d16ee42cc1881f6becfe116cd16f3909dd69c22b538235c6d7e,
  0xfc14213835cd70fff2a6caad57fe3674cbcfa6d0ad5ec828034df8bf44187466bf4f9d7faed5200f9af326c4d768cd7a3ad8ce61a25f2c6bf05ec34d49c9e09245b7de0, 0x940bc957e7ce13da183ef7f6810cee6566405fe6f3cee1071ccf2290d4398711dd11da3fcc4c190e56807e42b8d1fe9f6e3028217ecec6ff02f3a88d39f6e145c1ca5a, 0x48fda340dda11a9ab5ba893da70ab4bd622afd143d1a2ac12e3d166bf25e53edbb0ac59f7993af78a166c4a407b9677593312bead7d1471d74a21cb2ab59a58187f40,
  0x1df6fecd973867c2b2b10ff5abfd6ebc9cf8bb6089b7bb36974a5ae1553b6b8f1846b51f9ef5baf9e677bf825d7078fcae20231ddf77cceadb808f2c0c246fa1a8ce, 0xa265e3791e8ca743433d926d7375c110c57ec5600621024ce9f95a1a1fc52d67f28d368a0ba76db992cdfc4575377e35412b30ac7f0d839d1e71c2cf055727d920, 0x2cec4445860cd0daae5e259982cab1a5e2201211ada9c93c50098396fae4485bda770b109a19de17dc7282b4c3c5f79edc0ee8fec095c2519e5e1eca2871f811a,
  0xa07ed14364818accf4bf34d3f0026238242bde608224c87ff5e522925092209fcb0a5b3a5879e15ddd22476f14d61e6d2943ca1a2d0b5ca30e5ed7fdc96fa80, 0x1c8c73920d9f9def366d9d9ee1e3cc9a3a0397fd0881a4eae0491b7b9bd2f454c17160b513346f97b395c252b1f056c9b709d163445b1c864d31ece7065e2a, 0x3fc1866181b517cf78a24f29e1e3e322cc5010e15eb9ad400646e65c64ac2bd902081ec3928d9db9c089880df61c3507d42151f8c7b30756d40a8dcd4220,
  0x6dcdb002043c5385970b85bd4e135e1c25d32af2068c13dab4eac94c6a6e83be024758076fce3b750a912f5c9060c00700fe5c5272db09099046f5bafe, 0x8ef13030839959cdff7843d2e947bd9aa93120299460d044ad6b0ef6c782b57ac76ebac669747142b8938793ef61eeae818565105e51e9e4c1c28d40, 0x896824d51b517a8bd137f4477096d656216483950adff30f2923b7838d016cb1b414a8aa754ba413aabfb45dca0e3b46144687eff85cf510e478ea,
  0x5ee5a0832580221273c264e16163d260a10b6e27df0198e2c4a06b95d9e06321956061fa93c43813119247e40976aa513f6affa714f0a2704ce0, 0x2d951800d717bbc29bbf86400bb6e45f782e3a49ad2d818fe0f421ff865794f0a51ea582bf33f299e2eb49d5fc3aeaf480ed054e866f158dae, 0xea6154c5c1098f5d9b7b413edf56ffe874c0e3916f1f60f912f517aa60739ac4fe701ce02dca862756ba0f88b2ec66e4a74ad2e7db33d00,
  0x301706c0939eddf364969c5eaa4cfd7a03e8c8f569f2870cd5c2f084dd213deadace5042b6b204ed3fac4d0c6f46a33e044faa64ba38d, 0x5f324bd61458bb2c80559cfd24bf1f152198823279c3c9fca648a2f945186808088a08e889bbce561f284939f1bdea5f15b9388b50, 0x69e23bce4b5553271a8ae1f65e1765129132c657a491c8a32068d3144cf080e584395143e316dc2cdc19d199315576e66695757,
  0x3c917b817d98912127485e9b77f69cfcd519818270dd2f2837f88fa0a63091d47150b594b298d9235547f035d67b0d1db260, 0xfeb991a9afe7a6968d76df0657ba9cec40c616291b26c7117e0b251dccc4285159f0cca94a7680d9d0dfa8de250bca35, 0x1a9660605cff98783d448476cb062202a48c64917a70510627c7acb82c0d5413cb63d5fc94593cbe0f77a78b45f30,
  0xe88a463977cbebfa8c647b7ec2ee615f76c6db9951a53138d90ac0132780b91a5b47908004287acad5f7fd87, 0x1fffaa265e4fdb9b50bfdfd05825440e91b4c9b29214921fb3953f8016ab2eeb5e81e751c6d563aad140, 0xc43a7b376b1186c9c8eb94db2cbf547fb4a88bac4cdafa95c800b8275b2c4aeeecc706cb4af0c3,
  0x7a022a1b2bb9fef90324bd0ef40f92f003fcbe3ff7aa9e98809dd1a135f2fee15f740cf0, 0x353978b1b0747aa59c99d6c15349b52750a0bd7a2e76120972fab82ac98f6d529, 0x3fffffffff953e19e239b9fb3137d0a439b1cdaa2b975c23db3d1ee0,
  0xf404571f7c0dc1bc64fe88a0b2bc31e581768978a933, 0x7fffffffffffffffffffffffff90, 0x1]

private theorem eulerianCoefficients_eq : descentCoeffs 111 = eulerianCoefficients := by
  decide +kernel

private theorem upper : upperOK (descentCoeffs 111) first gaps = true := by
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

private theorem lower (i : Fin (lastRepresentative 112 - 2)) :
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

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 112) :
    StrictNegativeInterlacing (originalQuotient 112 k) (eulerian 111) 109 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N112
