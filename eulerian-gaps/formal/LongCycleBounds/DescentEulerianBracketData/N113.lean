import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentPackedData.C127L120.N113

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N113

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L120.N113 LongCycleBounds.DescentNecklace.Packed.C127L120.N113.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L120.N113 LongCycleBounds.DescentNecklace.Packed.C127L120.N113.rows

private theorem actual : RepresentativeChecks 113 previousNodes rows :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L120.N113 LongCycleBounds.DescentNecklace.Packed.C127L120.N113.dataChecks

private def first : LongCycleFinite.Dyadic := ⟨-5192296858534827628530496329220096, 0⟩

private def gaps : List Window := [
  ⟨⟨-5192128498689484816813110048325632, 0⟩, ⟨-52872681837794689024, 0⟩⟩,
  ⟨⟨-52728425912230477824, 0⟩, ⟨-99192001265664, 0⟩⟩,
  ⟨⟨-97096862531584, 0⟩, ⟨-74786799616, 0⟩⟩,
  ⟨⟨-70270058496, 0⟩, ⟨-713807872, 0⟩⟩,
  ⟨⟨-710379520, 0⟩, ⟨-29355776, 0⟩⟩,
  ⟨⟨-29321024, 0⟩, ⟨-2808520, 0⟩⟩,
  ⟨⟨-2807128, 0⟩, ⟨-463116, 0⟩⟩,
  ⟨⟨-462990, 0⟩, ⟨-221935, 1⟩⟩,
  ⟨⟨-443793, 2⟩, ⟨-277603, 3⟩⟩,
  ⟨⟨-277569, 3⟩, ⟨-211419, 4⟩⟩,
  ⟨⟨-422799, 5⟩, ⟨-46751, 3⟩⟩,
  ⟨⟨-93495, 4⟩, ⟨-371625, 7⟩⟩,
  ⟨⟨-371603, 7⟩, ⟨-50619, 5⟩⟩,
  ⟨⟨-101233, 6⟩, ⟨-237655, 8⟩⟩,
  ⟨⟨-237645, 8⟩, ⟨-296437, 9⟩⟩,
  ⟨⟨-148213, 8⟩, ⟨-388837, 10⟩⟩,
  ⟨⟨-48603, 7⟩, ⟨-265997, 10⟩⟩,
  ⟨⟨-265989, 10⟩, ⟨-377131, 11⟩⟩,
  ⟨⟨-377121, 11⟩, ⟨-275587, 11⟩⟩,
  ⟨⟨-68895, 9⟩, ⟨-413419, 12⟩⟩,
  ⟨⟨-206705, 11⟩, ⟨-317165, 12⟩⟩,
  ⟨⟨-317159, 12⟩, ⟨-496313, 13⟩⟩,
  ⟨⟨-31019, 9⟩, ⟨-395059, 13⟩⟩,
  ⟨⟨-395053, 13⟩, ⟨-159631, 12⟩⟩,
  ⟨⟨-319257, 13⟩, ⟨-522959, 14⟩⟩,
  ⟨⟨-522951, 14⟩, ⟨-108357, 12⟩⟩,
  ⟨⟨-216711, 13⟩, ⟨-363047, 14⟩⟩,
  ⟨⟨-181521, 13⟩, ⟨-306987, 14⟩⟩,
  ⟨⟨-306983, 14⟩, ⟨-261793, 14⟩⟩,
  ⟨⟨-130895, 13⟩, ⟨-3515, 8⟩⟩,
  ⟨⟨-224957, 14⟩, ⟨-48661, 12⟩⟩,
  ⟨⟨-97321, 13⟩, ⟨-338923, 15⟩⟩,
  ⟨⟨-338919, 15⟩, ⟨-296737, 15⟩⟩,
  ⟨⟨-148367, 14⟩, ⟨-522247, 16⟩⟩,
  ⟨⟨-261121, 15⟩, ⟨-115425, 14⟩⟩,
  ⟨⟨-461695, 16⟩, ⟨-409879, 16⟩⟩,
  ⟨⟨-409875, 16⟩, ⟨-365265, 16⟩⟩,
  ⟨⟨-182631, 15⟩, ⟨-163315, 15⟩⟩,
  ⟨⟨-326627, 16⟩, ⟨-36625, 13⟩⟩,
  ⟨⟨-292997, 16⟩, ⟨-65895, 14⟩⟩,
  ⟨⟨-263577, 16⟩, ⟨-118863, 15⟩⟩,
  ⟨⟨-59431, 14⟩, ⟨-53727, 14⟩⟩,
  ⟨⟨-429813, 17⟩, ⟨-389377, 17⟩⟩,
  ⟨⟨-194687, 16⟩, ⟨-2761, 10⟩⟩,
  ⟨⟨-353405, 17⟩, ⟨-40163, 14⟩⟩,
  ⟨⟨-321301, 17⟩, ⟨-292555, 17⟩⟩,
  ⟨⟨-36569, 14⟩, ⟨-133365, 16⟩⟩,
  ⟨⟨-266727, 17⟩, ⟨-486933, 18⟩⟩,
  ⟨⟨-486929, 18⟩, ⟨-222453, 17⟩⟩,
  ⟨⟨-222451, 17⟩, ⟨-406849, 18⟩⟩,
  ⟨⟨-406845, 18⟩, ⟨-23269, 14⟩⟩,
  ⟨⟨-372301, 18⟩, ⟨-340881, 18⟩⟩,
  ⟨⟨-170439, 17⟩, ⟨-78059, 16⟩⟩,
  ⟨⟨-156117, 17⟩, ⟨-143039, 17⟩⟩,
  ⟨⟨-286075, 18⟩, ⟨-262145, 18⟩⟩,
  ⟨⟨-524285, 19⟩, ⟨-480429, 19⟩⟩,
  ⟨⟨-240213, 18⟩, ⟨-110045, 17⟩⟩,
  ⟨⟨-27511, 15⟩, ⟨-50399, 16⟩⟩,
  ⟨⟨-403189, 19⟩, ⟨-369161, 19⟩⟩,
  ⟨⟨-184579, 18⟩, ⟨-42227, 16⟩⟩,
  ⟨⟨-337813, 19⟩, ⟨-308919, 19⟩⟩,
  ⟨⟨-77229, 17⟩, ⟨-282257, 19⟩⟩,
  ⟨⟨-141127, 18⟩, ⟨-128819, 18⟩⟩,
  ⟨⟨-64409, 17⟩, ⟨-14681, 15⟩⟩,
  ⟨⟨-117447, 18⟩, ⟨-427757, 20⟩⟩,
  ⟨⟨-213877, 19⟩, ⟨-388899, 20⟩⟩,
  ⟨⟨-12153, 15⟩, ⟨-352975, 20⟩⟩,
  ⟨⟨-88243, 18⟩, ⟨-79941, 18⟩⟩,
  ⟨⟨-319761, 20⟩, ⟨-18067, 16⟩⟩,
  ⟨⟨-289069, 20⟩, ⟨-130359, 19⟩⟩,
  ⟨⟨-521431, 21⟩, ⟨-469077, 21⟩⟩,
  ⟨⟨-469073, 21⟩, ⟨-210391, 20⟩⟩,
  ⟨⟨-210389, 20⟩, ⟨-376275, 21⟩⟩,
  ⟨⟨-376271, 21⟩, ⟨-167659, 20⟩⟩,
  ⟨⟨-335315, 21⟩, ⟨-297685, 21⟩⟩,
  ⟨⟨-148841, 20⟩, ⟨-131585, 20⟩⟩,
  ⟨⟨-263167, 21⟩, ⟨-231587, 21⟩⟩,
  ⟨⟨-231585, 21⟩, ⟨-25345, 18⟩⟩,
  ⟨⟨-101379, 20⟩, ⟨-11033, 17⟩⟩,
  ⟨⟨-88263, 20⟩, ⟨-305477, 22⟩⟩,
  ⟨⟨-305473, 22⟩, ⟨-262499, 22⟩⟩,
  ⟨⟨-8203, 17⟩, ⟨-13991, 18⟩⟩,
  ⟨⟨-447707, 23⟩, ⟨-378575, 23⟩⟩,
  ⟨⟨-189285, 22⟩, ⟨-158551, 22⟩⟩,
  ⟨⟨-158549, 22⟩, ⟨-262815, 23⟩⟩,
  ⟨⟨-262811, 23⟩, ⟨-107625, 22⟩⟩,
  ⟨⟨-430493, 24⟩, ⟨-86975, 22⟩⟩,
  ⟨⟨-347895, 24⟩, ⟨-138463, 23⟩⟩,
  ⟨⟨-276921, 24⟩, ⟨-433339, 25⟩⟩,
  ⟨⟨-433331, 25⟩, ⟨-332453, 25⟩⟩,
  ⟨⟨-166223, 24⟩, ⟨-249365, 25⟩⟩,
  ⟨⟨-15585, 21⟩, ⟨-364443, 26⟩⟩,
  ⟨⟨-364435, 26⟩, ⟨-258353, 26⟩⟩,
  ⟨⟨-516695, 27⟩, ⟨-176737, 26⟩⟩,
  ⟨⟨-353465, 27⟩, ⟨-231831, 27⟩⟩,
  ⟨⟨-231825, 27⟩, ⟨-144585, 27⟩⟩,
  ⟨⟨-144581, 27⟩, ⟨-339411, 29⟩⟩,
  ⟨⟨-339399, 29⟩, ⟨-369843, 30⟩⟩,
  ⟨⟨-369829, 30⟩, ⟨-183745, 30⟩⟩,
  ⟨⟨-91869, 29⟩, ⟨-325061, 32⟩⟩,
  ⟨⟨-162523, 31⟩, ⟨-247561, 33⟩⟩,
  ⟨⟨-247549, 33⟩, ⟨-154845, 34⟩⟩,
  ⟨⟨-309673, 35⟩, ⟨-74197, 35⟩⟩,
  ⟨⟨-148385, 36⟩, ⟨-391699, 40⟩⟩,
  ⟨⟨-391673, 40⟩, ⟨-74915, 41⟩⟩,
  ⟨⟨-299639, 43⟩, ⟨-49343, 45⟩⟩,
  ⟨⟨-394715, 48⟩, ⟨-509315, 55⟩⟩,
  ⟨⟨-509275, 55⟩, ⟨-187543, 64⟩⟩,
  ⟨⟨-187527, 64⟩, ⟨-366711, 84⟩⟩,
  ⟨⟨-366677, 84⟩, ⟨-262165, 130⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private def eulerianCoefficients : List ℤ := [
  0x1, 0xffffffffffffffffffffffffff8f, 0x2dc0d055e7429456c2efb99e2183495b084639c69cb79,
  0xfffffffffebcde40a14eb9c8421642f1133350c9ed159007f5548637, 0x10a1f5b7a2246653c0c3094f5577631241f5c73b76dbe866be52346c7f7a9b304d, 0x2dc0cfe06f6b31e221dd0a1e0fd299e7d14d7ec6b00f2d8a9b94b88f83061976c2be365c3,
  0x55d999108d2e9ef9f82042d4b6f83808c6373335cc0c356a51db02e54d702ccdf16fa811519f0b5, 0xfffda1aeef0897c4b647c1eb613805cf074eaeadb1ee3c836d716b0900e19bc01ecb39abd8747f1349fb, 0x82ce977e255c19c4026a12567c7053b7ed2e8e9d5cf5a135afe41b54e2f8fb778452279461ea517d2031cebbf,
  0x109e59cbdc60de7e323ca146ac93d5af900527a4eee0e27d4faaab466ed0097129980077a7db47a3131264cdd2b931, 0xaf2a2c0f0f54505e412a22a123a53053f995bf2c54a1719c4f1b83134e2869076db8967ba5d49423f353edc57af5f9d67, 0x2d73649485b1933f290ca3f2f9d0ff879e667a0440895ec2f298d75ed6f089f5937e0fef91df48e68d54eaac3ad693b0b2369,
  0x561f796bdbca632876842fdd212dde7468bc7f1dccaa896af60b0898994453b3726ad58e1698569944a24a664d1d38ac52f31ceb, 0x5374f4d87294c5c6186a2d12e26d9e3e9393988ede6ff51da8951723bd4f1c08e03ae9f5e5c52662809c5e0ec1c441202e1bbd46505, 0x2d3a07959258ba0bd556535ed8903ecc49c118c7eaa5fb8f5b1e694af2bb9d640034b015f44b9e8368a975a7b080c3bddc7100a613e9e3,
  0xeb84e05eb088827f2f0d1252dd3f72a9287896d3bef1af4bd0c5057c85f0344c5e3e9fa6c23e1d65350c141bce4f03224f44f5e0dddcc86d, 0x30c64e00aeb19b148895ccdc8406134566dce6439e8a056d3c6a80085ea13999b94ff9e5bf385db5cfda84392f41b24a5eba91b285c83a5488e, 0x6bd0f9d20f2d433f95b772aaa9d5da98ac066e66f0560a30637c2292724a178a1ce0d4309e8c0385e577e5e6f12f1d6e7315deeb79ccea4e4fb52,
  0xa55930cc12ed124e34da882581cf48fa3f597f6827281a04351d986447d1b7596b261e8a0b6df3a0cacae195bba87f8bd568560aec8968be631339e, 0xb5cc2992bb2e79d9cc066a0382d819bf281f8070cbc83a0aa0e4f24f2606fb214231218c629b553d1908e3c14c60dd12a93c984a98ba00ae64632f602, 0x9353e1d7bc83df63b6bc130e7336c8072af202d697ad06bc98594fca56ac3c7ce4f8603bb79d0b94dd83de75101f6f259cb6983154ddd2dd70b741319d6,
  0x5a1a9a9f1dd117d84daa3e623b4566771905383a22c48ae8f4867417ed0a10d7ab78201193ce9dd1926934d090dbef2eeb837763278367dac9f3168fd270a, 0x2a7086b5d80f0dadcd442391b04e17fb57226cdaafef31802a8c665177b587b07abe68b157b3bd0147024cf42e51db6c4327586bc9a6480a57607fe9bbbb506, 0xfaab0e12dd7ece1b990aeb0a248bc575d46d0d67bb2c3f1598d11e69720787e127cff37678640cd889227bb55f1dbbcfde8818f2c654b7df46649f58ff5e389a,
  0x49a3e42b941cced117b536626a04c2af66190d82b22514bcfcd749da0cbfd4c2f436ba3fb1af095cccb328c354d7ec8f903a40e59ce1be1d084219bfd305f9b78a, 0x11729dcd87232eac79e860cb907123c1aa0c6e6e00bfa57207b686e22c2e3fe602163ed62f74edcc7aa79a45c4d02743d86af4046e1e8dae90e4ad9071c6c5c0ed16, 0x35f9b1a19a33631b971435e19e8843cc03094597cc86fd587cb715a08c3f095587af08aa823d4f737a5f2657f303d670c41483680845126fbeec95116d3a30d6fbe7a,
  0x89aee04bc70fa902635b3a78766de2100be9d11a78a7cbfb31269769b971cd968a6253fa948a0a2813f99ab5568acd39a766b883e4e1037d86fd61c24be4fab35af766, 0x1244896809cde60b60f93567704b6f365ed8ac8dd3df38de447637a01ec2f385a620fe46bf62e62fd91be9d5ec18573738c036b25c4a77403df9ed2ea9948e29cefdad32, 0x208a59090e509044f9cd52669f0d3d765de4c37df261dca4054895a9b947c810b71621112170c483ce89391a0b5d096d2df101ff9ec8f7dcf10a6add6b425901be08d5b6e,
  0x30ff783e2beb80844273ae6ca146fc6b08c97a4b4dbd6a90f27a3f553dbe1c8862dcf8cc88a27c8e51e2022c77aa0fd40a2a783ce0a1ea9970ae68c5e9025e90b9ed7f9402, 0x3ec7afa5b03146216ae0b9c244b6588666b7e76db8a7c9375fcb7aa6c8d7d30984b602153e83508e266a5c4cadca2288f6e356f61f84218a0890ac09dd508d7f0bcd7a7c4de, 0x44db1d4010cf5ab70c0869fb570a1d688527af9f7027b6d9b615c498c635f2126dcd0f81938e9248a9121807cf91e39c4d7efa1387b25326c9ba42171b9737af2ad75fb1e52b,
  0x40fe6515485d1f22a89df04e4006c2c496a14ededb4d4372b181698568247cc2cef80f4086b156596c182ec38912354a8e574833370903ca9241ee65c0a433d4574e625e13205, 0x350dfa78097db6fbd169c9bf0878ae8ca7ad59ea9b60c0e5830d0d6896308f39ebdd7447a760b3ec4afbc6ca88fc11873c03c021907cbf2fde7326ddee075f0f57efa0c5178ad3, 0x259e7c891552fdbfe867bcf98a4350a6b70529517ef70453bf1bece5383103c7ef9ae9581134f6b82454b467f9a2a85e1c4a6e4e1c4b2acc6c9efebd95d80a6c64d111157d56fbd,
  0x17434512254ea0919b59921a2f57339f843affdcbe13bf2a6fe59bad98659db4ceb58627d2636d5e92180ed2d01cb140acf34a269f0682f0475a3f363856c71b07387b6cf9c9b80f, 0xc974699ebc9684ef8073b13c10d8ffe4b12fdd15b11e438d1b353f057a48ac6076efecad93a64f3032b8cfc3f95685538198102dfa647c485362d8b31ff3d1e8c54941d93d03d8a1, 0x5fc07680fb5e4179301d4f9eca9320cf232f7853be6a6e7ee025a52c2c565719e4ccdfae61809d60d04479de7279f97248b0d6a378e22e77aeacca9259d48c312bbf72189dcd5f507,
  0x2815f36ef6a4686604d89507ea963723e376500534b9a2ac3d1ef1604261f4f85af6953917a36cd5c87925f348e1e7ccfc73f42db462da9481ae60a9dc7bae9601b8be4364bbc43e89, 0xed24337a1bfbc2b5e3bac8c3eda7eea563354aaf071520864b1a67766a38b353b2a01537147d6b2ac34cbc94501fa78436ab54a7c8fd38fb360d9b74d3b1f0e46df0afe8579ebda75d, 0x4da15cc271c7f97b7697ebff487c66ba707267935f6ac3bf1364aeb125137c63ecfd380079d5f7c81bbd0500327e4657e029b6be97fc6ad92df26602b635e3f15bdda442e9982529f73,
  0x168ce5bc09159b58e6fbe454144a932c484d4858d2e5a9dd6561560157f92fce750ea4ffe47cd2711f3303c38561775fb0365f5c4b32eb489d6e44b1038a6f5ed0151b2ee28464b0eed5, 0x5d30eadd314d7087bd1658d1e344911f42dd7e6d1a432083ca8319f94c2f0c4cb0b7574bdd86bdfb137851a7a1805f859d365ab8969c494bb1cf49121a7071eefde4f241b876bd23779b, 0x1570ea8ee69523c557eacb35ef7d82cee7a121c92c64e61fd1e2da2686a82508646bffefb73934d713da7cc1bef9c4c5514431a4dbb99b613867e7a3114e3712520ff7b787edb6f9ed941,
  0x466cb38e9a382b3ed8453e7268387c5df7ca08f85fd45d406e8fdca4dcba5c96cd6e1e7da1da8a8c32b2b44513a4fbab1c97113440b635edb41d728164ed0dade18a73d894f0e73dd928f, 0xceb18a2c365ebbc7f74e8d4847f3155f638a588e5be559a20ed5ab9d5500cf90d46cb17f8beaa55bf4ae3d39fb299f5134fe8e513c43bda54811a789b076391f3643add20f272d719bda9, 0x21ec72aa3d7ad5168d445e1411d6352199c1ecbc778dc7d5b65f342117d343f87340b16bfddab5a9345a875d758420946590e6683bb7a420426caf79c7d7ee46f7c6fa912c834dfabd5747,
  0x4fcc4f7a9566c6d3ce02ca5e39b186046ad4e1ddff1e52fb85ac2e3fa3b38216f312f169dde074c26d9238f45ad113e73b048d4554ab28ef59e136d72df3bed3f11b4eed94dfe9f219ddb4, 0xa84ff8095720c84e8d8aa683c09cc0190468b703918914e2baa6c76b7f77a60554bea7e24a7a3ac710969b7ca58884610c635237f1c698a2e07e5cb21f4f612996218ebb46068b777ca78c, 0x13e9a908cb75bcc97931ebd3ad244a31ddb29c3edd2020f2cc68e5f0e967e810baca0b68e814e9fe9869a0f407e6fe19411dcf067f607102166bb65024f89d4c7db6275f1c33dc0a27c9314,
  0x21da5c7c339748773c7abfce086c1245f6fcb52a1f206339683f1a93d90dddfdd29d1d0407375474d645e36cba20a84292bcf75ddb266c1a7985cb45bef6f127787ee60be3036e05c1600ac, 0x33b848ce173f1fe40161824eba183170f2d5d194e101bce31454151a258dd1415d16c491ee500ddcd8ca3ce8f7146bfac166ebf5d65e1dc5cd5a288e990e7f262c3b28911c735b266fbdb64, 0x470b0429b72642946138058f4fa2096efdc8e45f93e8681e466a8904948c8d4c148942d58067eacfcbca5b0febeea1a07561323ef5441077f2163fd7432273f517ab1f29bd57017d62cdfdc,
  0x57c50f045d816bcb6409ba7327e99a68c531ca239bbe825a4f52a9a09ce72f6b70ffcc9e2796e4539249f66d673c829d6e831d5c3b7929ec4cfd2f7ffaa79efd0eb97d757ae7758eb7e0f84, 0x618d01f0a91a0b66ab3767b3db06d9d8701c80d84c3f1e10b6bd3687353da97f724b8f3520ad331bca31422f49a1b7459acd9eb49ac67292d6ad377ab419dafb914e41933497fb11c43043c, 0x618d01f0a91a0b66ab3767b3db06d9d8701c80d84c3f1e10b6bd3687353da97f724b8f3520ad331bca31422f49a1b7459acd9eb49ac67292d6ad377ab419dafb914e41933497fb11c43043c,
  0x57c50f045d816bcb6409ba7327e99a68c531ca239bbe825a4f52a9a09ce72f6b70ffcc9e2796e4539249f66d673c829d6e831d5c3b7929ec4cfd2f7ffaa79efd0eb97d757ae7758eb7e0f84, 0x470b0429b72642946138058f4fa2096efdc8e45f93e8681e466a8904948c8d4c148942d58067eacfcbca5b0febeea1a07561323ef5441077f2163fd7432273f517ab1f29bd57017d62cdfdc, 0x33b848ce173f1fe40161824eba183170f2d5d194e101bce31454151a258dd1415d16c491ee500ddcd8ca3ce8f7146bfac166ebf5d65e1dc5cd5a288e990e7f262c3b28911c735b266fbdb64,
  0x21da5c7c339748773c7abfce086c1245f6fcb52a1f206339683f1a93d90dddfdd29d1d0407375474d645e36cba20a84292bcf75ddb266c1a7985cb45bef6f127787ee60be3036e05c1600ac, 0x13e9a908cb75bcc97931ebd3ad244a31ddb29c3edd2020f2cc68e5f0e967e810baca0b68e814e9fe9869a0f407e6fe19411dcf067f607102166bb65024f89d4c7db6275f1c33dc0a27c9314, 0xa84ff8095720c84e8d8aa683c09cc0190468b703918914e2baa6c76b7f77a60554bea7e24a7a3ac710969b7ca58884610c635237f1c698a2e07e5cb21f4f612996218ebb46068b777ca78c,
  0x4fcc4f7a9566c6d3ce02ca5e39b186046ad4e1ddff1e52fb85ac2e3fa3b38216f312f169dde074c26d9238f45ad113e73b048d4554ab28ef59e136d72df3bed3f11b4eed94dfe9f219ddb4, 0x21ec72aa3d7ad5168d445e1411d6352199c1ecbc778dc7d5b65f342117d343f87340b16bfddab5a9345a875d758420946590e6683bb7a420426caf79c7d7ee46f7c6fa912c834dfabd5747, 0xceb18a2c365ebbc7f74e8d4847f3155f638a588e5be559a20ed5ab9d5500cf90d46cb17f8beaa55bf4ae3d39fb299f5134fe8e513c43bda54811a789b076391f3643add20f272d719bda9,
  0x466cb38e9a382b3ed8453e7268387c5df7ca08f85fd45d406e8fdca4dcba5c96cd6e1e7da1da8a8c32b2b44513a4fbab1c97113440b635edb41d728164ed0dade18a73d894f0e73dd928f, 0x1570ea8ee69523c557eacb35ef7d82cee7a121c92c64e61fd1e2da2686a82508646bffefb73934d713da7cc1bef9c4c5514431a4dbb99b613867e7a3114e3712520ff7b787edb6f9ed941, 0x5d30eadd314d7087bd1658d1e344911f42dd7e6d1a432083ca8319f94c2f0c4cb0b7574bdd86bdfb137851a7a1805f859d365ab8969c494bb1cf49121a7071eefde4f241b876bd23779b,
  0x168ce5bc09159b58e6fbe454144a932c484d4858d2e5a9dd6561560157f92fce750ea4ffe47cd2711f3303c38561775fb0365f5c4b32eb489d6e44b1038a6f5ed0151b2ee28464b0eed5, 0x4da15cc271c7f97b7697ebff487c66ba707267935f6ac3bf1364aeb125137c63ecfd380079d5f7c81bbd0500327e4657e029b6be97fc6ad92df26602b635e3f15bdda442e9982529f73, 0xed24337a1bfbc2b5e3bac8c3eda7eea563354aaf071520864b1a67766a38b353b2a01537147d6b2ac34cbc94501fa78436ab54a7c8fd38fb360d9b74d3b1f0e46df0afe8579ebda75d,
  0x2815f36ef6a4686604d89507ea963723e376500534b9a2ac3d1ef1604261f4f85af6953917a36cd5c87925f348e1e7ccfc73f42db462da9481ae60a9dc7bae9601b8be4364bbc43e89, 0x5fc07680fb5e4179301d4f9eca9320cf232f7853be6a6e7ee025a52c2c565719e4ccdfae61809d60d04479de7279f97248b0d6a378e22e77aeacca9259d48c312bbf72189dcd5f507, 0xc974699ebc9684ef8073b13c10d8ffe4b12fdd15b11e438d1b353f057a48ac6076efecad93a64f3032b8cfc3f95685538198102dfa647c485362d8b31ff3d1e8c54941d93d03d8a1,
  0x17434512254ea0919b59921a2f57339f843affdcbe13bf2a6fe59bad98659db4ceb58627d2636d5e92180ed2d01cb140acf34a269f0682f0475a3f363856c71b07387b6cf9c9b80f, 0x259e7c891552fdbfe867bcf98a4350a6b70529517ef70453bf1bece5383103c7ef9ae9581134f6b82454b467f9a2a85e1c4a6e4e1c4b2acc6c9efebd95d80a6c64d111157d56fbd, 0x350dfa78097db6fbd169c9bf0878ae8ca7ad59ea9b60c0e5830d0d6896308f39ebdd7447a760b3ec4afbc6ca88fc11873c03c021907cbf2fde7326ddee075f0f57efa0c5178ad3,
  0x40fe6515485d1f22a89df04e4006c2c496a14ededb4d4372b181698568247cc2cef80f4086b156596c182ec38912354a8e574833370903ca9241ee65c0a433d4574e625e13205, 0x44db1d4010cf5ab70c0869fb570a1d688527af9f7027b6d9b615c498c635f2126dcd0f81938e9248a9121807cf91e39c4d7efa1387b25326c9ba42171b9737af2ad75fb1e52b, 0x3ec7afa5b03146216ae0b9c244b6588666b7e76db8a7c9375fcb7aa6c8d7d30984b602153e83508e266a5c4cadca2288f6e356f61f84218a0890ac09dd508d7f0bcd7a7c4de,
  0x30ff783e2beb80844273ae6ca146fc6b08c97a4b4dbd6a90f27a3f553dbe1c8862dcf8cc88a27c8e51e2022c77aa0fd40a2a783ce0a1ea9970ae68c5e9025e90b9ed7f9402, 0x208a59090e509044f9cd52669f0d3d765de4c37df261dca4054895a9b947c810b71621112170c483ce89391a0b5d096d2df101ff9ec8f7dcf10a6add6b425901be08d5b6e, 0x1244896809cde60b60f93567704b6f365ed8ac8dd3df38de447637a01ec2f385a620fe46bf62e62fd91be9d5ec18573738c036b25c4a77403df9ed2ea9948e29cefdad32,
  0x89aee04bc70fa902635b3a78766de2100be9d11a78a7cbfb31269769b971cd968a6253fa948a0a2813f99ab5568acd39a766b883e4e1037d86fd61c24be4fab35af766, 0x35f9b1a19a33631b971435e19e8843cc03094597cc86fd587cb715a08c3f095587af08aa823d4f737a5f2657f303d670c41483680845126fbeec95116d3a30d6fbe7a, 0x11729dcd87232eac79e860cb907123c1aa0c6e6e00bfa57207b686e22c2e3fe602163ed62f74edcc7aa79a45c4d02743d86af4046e1e8dae90e4ad9071c6c5c0ed16,
  0x49a3e42b941cced117b536626a04c2af66190d82b22514bcfcd749da0cbfd4c2f436ba3fb1af095cccb328c354d7ec8f903a40e59ce1be1d084219bfd305f9b78a, 0xfaab0e12dd7ece1b990aeb0a248bc575d46d0d67bb2c3f1598d11e69720787e127cff37678640cd889227bb55f1dbbcfde8818f2c654b7df46649f58ff5e389a, 0x2a7086b5d80f0dadcd442391b04e17fb57226cdaafef31802a8c665177b587b07abe68b157b3bd0147024cf42e51db6c4327586bc9a6480a57607fe9bbbb506,
  0x5a1a9a9f1dd117d84daa3e623b4566771905383a22c48ae8f4867417ed0a10d7ab78201193ce9dd1926934d090dbef2eeb837763278367dac9f3168fd270a, 0x9353e1d7bc83df63b6bc130e7336c8072af202d697ad06bc98594fca56ac3c7ce4f8603bb79d0b94dd83de75101f6f259cb6983154ddd2dd70b741319d6, 0xb5cc2992bb2e79d9cc066a0382d819bf281f8070cbc83a0aa0e4f24f2606fb214231218c629b553d1908e3c14c60dd12a93c984a98ba00ae64632f602,
  0xa55930cc12ed124e34da882581cf48fa3f597f6827281a04351d986447d1b7596b261e8a0b6df3a0cacae195bba87f8bd568560aec8968be631339e, 0x6bd0f9d20f2d433f95b772aaa9d5da98ac066e66f0560a30637c2292724a178a1ce0d4309e8c0385e577e5e6f12f1d6e7315deeb79ccea4e4fb52, 0x30c64e00aeb19b148895ccdc8406134566dce6439e8a056d3c6a80085ea13999b94ff9e5bf385db5cfda84392f41b24a5eba91b285c83a5488e,
  0xeb84e05eb088827f2f0d1252dd3f72a9287896d3bef1af4bd0c5057c85f0344c5e3e9fa6c23e1d65350c141bce4f03224f44f5e0dddcc86d, 0x2d3a07959258ba0bd556535ed8903ecc49c118c7eaa5fb8f5b1e694af2bb9d640034b015f44b9e8368a975a7b080c3bddc7100a613e9e3, 0x5374f4d87294c5c6186a2d12e26d9e3e9393988ede6ff51da8951723bd4f1c08e03ae9f5e5c52662809c5e0ec1c441202e1bbd46505,
  0x561f796bdbca632876842fdd212dde7468bc7f1dccaa896af60b0898994453b3726ad58e1698569944a24a664d1d38ac52f31ceb, 0x2d73649485b1933f290ca3f2f9d0ff879e667a0440895ec2f298d75ed6f089f5937e0fef91df48e68d54eaac3ad693b0b2369, 0xaf2a2c0f0f54505e412a22a123a53053f995bf2c54a1719c4f1b83134e2869076db8967ba5d49423f353edc57af5f9d67,
  0x109e59cbdc60de7e323ca146ac93d5af900527a4eee0e27d4faaab466ed0097129980077a7db47a3131264cdd2b931, 0x82ce977e255c19c4026a12567c7053b7ed2e8e9d5cf5a135afe41b54e2f8fb778452279461ea517d2031cebbf, 0xfffda1aeef0897c4b647c1eb613805cf074eaeadb1ee3c836d716b0900e19bc01ecb39abd8747f1349fb,
  0x55d999108d2e9ef9f82042d4b6f83808c6373335cc0c356a51db02e54d702ccdf16fa811519f0b5, 0x2dc0cfe06f6b31e221dd0a1e0fd299e7d14d7ec6b00f2d8a9b94b88f83061976c2be365c3, 0x10a1f5b7a2246653c0c3094f5577631241f5c73b76dbe866be52346c7f7a9b304d,
  0xfffffffffebcde40a14eb9c8421642f1133350c9ed159007f5548637, 0x2dc0d055e7429456c2efb99e2183495b084639c69cb79, 0xffffffffffffffffffffffffff8f,
  0x1]

private theorem eulerianCoefficients_eq : descentCoeffs 112 = eulerianCoefficients := by
  decide +kernel

private theorem upper : upperOK (descentCoeffs 112) first gaps = true := by
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

private theorem lower (i : Fin (lastRepresentative 113 - 2)) :
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

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 113) :
    StrictNegativeInterlacing (originalQuotient 113 k) (eulerian 112) 110 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N113
