import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentPackedData.C127L120.N120

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N120

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L120.N120 LongCycleBounds.DescentNecklace.Packed.C127L120.N120.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L120.N120 LongCycleBounds.DescentNecklace.Packed.C127L120.N120.rows

private theorem actual : RepresentativeChecks 120 previousNodes rows :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L120.N120 LongCycleBounds.DescentNecklace.Packed.C127L120.N120.dataChecks

private def first : LongCycleFinite.Dyadic := ⟨-664613997892457936451903530140172288, 0⟩

private def gaps : List Window := [
  ⟨⟨-664592447832254056552078086185680896, 0⟩, ⟨-914741882913917239296, 0⟩⟩,
  ⟨⟨-896292887040394002432, 0⟩, ⟨-766149151162368, 0⟩⟩,
  ⟨⟨-730316239011840, 0⟩, ⟨-349663395840, 0⟩⟩,
  ⟨⟨-316039757824, 0⟩, ⟨-2570567680, 0⟩⟩,
  ⟨⟨-2553446400, 0⟩, ⟨-87225344, 0⟩⟩,
  ⟨⟨-87098880, 0⟩, ⟨-7234000, 0⟩⟩,
  ⟨⟨-7229808, 0⟩, ⟨-1070768, 0⟩⟩,
  ⟨⟨-1070440, 0⟩, ⟨-471305, 1⟩⟩,
  ⟨⟨-471213, 1⟩, ⟨-137641, 1⟩⟩,
  ⟨⟨-68811, 0⟩, ⟨-198215, 3⟩⟩,
  ⟨⟨-198195, 3⟩, ⟨-167287, 4⟩⟩,
  ⟨⟨-83637, 3⟩, ⟨-159755, 5⟩⟩,
  ⟨⟨-159745, 5⟩, ⟨-336561, 7⟩⟩,
  ⟨⟨-336543, 7⟩, ⟨-95909, 6⟩⟩,
  ⟨⟨-191809, 7⟩, ⟨-466491, 9⟩⟩,
  ⟨⟨-466473, 9⟩, ⟨-299197, 9⟩⟩,
  ⟨⟨-299187, 9⟩, ⟨-401379, 10⟩⟩,
  ⟨⟨-401367, 10⟩, ⟨-139811, 9⟩⟩,
  ⟨⟨-139807, 9⟩, ⟨-50299, 8⟩⟩,
  ⟨⟨-201191, 10⟩, ⟨-297671, 11⟩⟩,
  ⟨⟨-4651, 5⟩, ⟨-451127, 12⟩⟩,
  ⟨⟨-451117, 12⟩, ⟨-349069, 12⟩⟩,
  ⟨⟨-349063, 12⟩, ⟨-275099, 12⟩⟩,
  ⟨⟨-137547, 11⟩, ⟨-440651, 13⟩⟩,
  ⟨⟨-110161, 11⟩, ⟨-178999, 12⟩⟩,
  ⟨⟨-44749, 10⟩, ⟨-147277, 12⟩⟩,
  ⟨⟨-147275, 12⟩, ⟨-122557, 12⟩⟩,
  ⟨⟨-490221, 14⟩, ⟨-103023, 12⟩⟩,
  ⟨⟨-206043, 13⟩, ⟨-349575, 14⟩⟩,
  ⟨⟨-174785, 13⟩, ⟨-298977, 14⟩⟩,
  ⟨⟨-298973, 14⟩, ⟨-515203, 15⟩⟩,
  ⟨⟨-515197, 15⟩, ⟨-446883, 15⟩⟩,
  ⟨⟨-223439, 14⟩, ⟨-48747, 12⟩⟩,
  ⟨⟨-97493, 13⟩, ⟨-171101, 14⟩⟩,
  ⟨⟨-171099, 14⟩, ⟨-37723, 12⟩⟩,
  ⟨⟨-301781, 15⟩, ⟨-267363, 15⟩⟩,
  ⟨⟨-8355, 10⟩, ⟨-118927, 14⟩⟩,
  ⟨⟨-59463, 13⟩, ⟨-424815, 16⟩⟩,
  ⟨⟨-424811, 16⟩, ⟨-190345, 15⟩⟩,
  ⟨⟨-190343, 15⟩, ⟨-85557, 14⟩⟩,
  ⟨⟨-342225, 16⟩, ⟨-308545, 16⟩⟩,
  ⟨⟨-154271, 15⟩, ⟨-278913, 16⟩⟩,
  ⟨⟨-278911, 16⟩, ⟨-505469, 17⟩⟩,
  ⟨⟨-505465, 17⟩, ⟨-459033, 17⟩⟩,
  ⟨⟨-459029, 17⟩, ⟨-417693, 17⟩⟩,
  ⟨⟨-208845, 16⟩, ⟨-380763, 17⟩⟩,
  ⟨⟨-47595, 14⟩, ⟨-173833, 16⟩⟩,
  ⟨⟨-347663, 17⟩, ⟨-39739, 14⟩⟩,
  ⟨⟨-317909, 17⟩, ⟨-291085, 17⟩⟩,
  ⟨⟨-145541, 16⟩, ⟨-16677, 13⟩⟩,
  ⟨⟨-133415, 16⟩, ⟨-61213, 15⟩⟩,
  ⟨⟨-122425, 16⟩, ⟨-449763, 18⟩⟩,
  ⟨⟨-449759, 18⟩, ⟨-103349, 16⟩⟩,
  ⟨⟨-413393, 18⟩, ⟨-380213, 18⟩⟩,
  ⟨⟨-190105, 17⟩, ⟨-349873, 18⟩⟩,
  ⟨⟨-174935, 17⟩, ⟨-322083, 18⟩⟩,
  ⟨⟨-322081, 18⟩, ⟨-37073, 15⟩⟩,
  ⟨⟨-148291, 17⟩, ⟨-273151, 18⟩⟩,
  ⟨⟨-273149, 18⟩, ⟨-503167, 19⟩⟩,
  ⟨⟨-503163, 19⟩, ⟨-231705, 18⟩⟩,
  ⟨⟨-463407, 19⟩, ⟨-426721, 19⟩⟩,
  ⟨⟨-213359, 18⟩, ⟨-392829, 19⟩⟩,
  ⟨⟨-196413, 18⟩, ⟨-361483, 19⟩⟩,
  ⟨⟨-45185, 16⟩, ⟨-332465, 19⟩⟩,
  ⟨⟨-332463, 19⟩, ⟨-305583, 19⟩⟩,
  ⟨⟨-76395, 17⟩, ⟨-280659, 19⟩⟩,
  ⟨⟨-280657, 19⟩, ⟨-64385, 17⟩⟩,
  ⟨⟨-128769, 18⟩, ⟨-472165, 20⟩⟩,
  ⟨⟨-472161, 20⟩, ⟨-432323, 20⟩⟩,
  ⟨⟨-6755, 14⟩, ⟨-197661, 19⟩⟩,
  ⟨⟨-395319, 20⟩, ⟨-705, 11⟩⟩,
  ⟨⟨-360957, 20⟩, ⟨-329047, 20⟩⟩,
  ⟨⟨-82261, 18⟩, ⟨-149707, 19⟩⟩,
  ⟨⟨-299411, 20⟩, ⟨-271907, 20⟩⟩,
  ⟨⟨-271905, 20⟩, ⟨-492771, 21⟩⟩,
  ⟨⟨-492767, 21⟩, ⟨-55681, 18⟩⟩,
  ⟨⟨-111361, 19⟩, ⟨-401605, 21⟩⟩,
  ⟨⟨-200801, 20⟩, ⟨-45129, 18⟩⟩,
  ⟨⟨-361029, 21⟩, ⟨-323529, 21⟩⟩,
  ⟨⟨-323525, 21⟩, ⟨-288919, 21⟩⟩,
  ⟨⟨-72229, 19⟩, ⟨-128515, 20⟩⟩,
  ⟨⟨-514055, 22⟩, ⟨-455425, 22⟩⟩,
  ⟨⟨-455421, 22⟩, ⟨-401637, 22⟩⟩,
  ⟨⟨-401633, 22⟩, ⟨-22027, 18⟩⟩,
  ⟨⟨-88107, 20⟩, ⟨-307555, 22⟩⟩,
  ⟨⟨-9611, 17⟩, ⟨-266771, 22⟩⟩,
  ⟨⟨-266767, 22⟩, ⟨-229851, 22⟩⟩,
  ⟨⟨-459697, 23⟩, ⟨-196583, 22⟩⟩,
  ⟨⟨-196581, 22⟩, ⟨-20845, 19⟩⟩,
  ⟨⟨-83379, 21⟩, ⟨-140181, 22⟩⟩,
  ⟨⟨-140179, 22⟩, ⟨-466603, 24⟩⟩,
  ⟨⟨-466597, 24⟩, ⟨-23995, 20⟩⟩,
  ⟨⟨-383915, 24⟩, ⟨-311903, 24⟩⟩,
  ⟨⟨-155949, 23⟩, ⟨-124903, 23⟩⟩,
  ⟨⟨-124901, 23⟩, ⟨-196867, 24⟩⟩,
  ⟨⟨-393727, 25⟩, ⟨-38083, 22⟩⟩,
  ⟨⟨-152329, 24⟩, ⟨-461723, 26⟩⟩,
  ⟨⟨-230857, 25⟩, ⟨-5337, 20⟩⟩,
  ⟨⟨-341561, 26⟩, ⟨-245763, 26⟩⟩,
  ⟨⟨-491515, 27⟩, ⟨-85605, 25⟩⟩,
  ⟨⟨-85603, 25⟩, ⟨-459367, 28⟩⟩,
  ⟨⟨-114839, 26⟩, ⟨-294637, 28⟩⟩,
  ⟨⟨-294629, 28⟩, ⟨-358261, 29⟩⟩,
  ⟨⟨-179125, 28⟩, ⟨-204195, 29⟩⟩,
  ⟨⟨-408377, 30⟩, ⟨-215083, 30⟩⟩,
  ⟨⟨-215075, 30⟩, ⟨-102705, 30⟩⟩,
  ⟨⟨-410803, 32⟩, ⟨-173365, 32⟩⟩,
  ⟨⟨-346715, 33⟩, ⟨-499283, 35⟩⟩,
  ⟨⟨-249629, 34⟩, ⟨-291645, 36⟩⟩,
  ⟨⟨-291629, 36⟩, ⟨-513457, 39⟩⟩,
  ⟨⟨-256713, 38⟩, ⟨-152067, 40⟩⟩,
  ⟨⟨-152057, 40⟩, ⟨-403787, 45⟩⟩,
  ⟨⟨-201879, 44⟩, ⟨-6845, 44⟩⟩,
  ⟨⟨-438047, 50⟩, ⟨-213115, 56⟩⟩,
  ⟨⟨-106549, 55⟩, ⟨-400463, 68⟩⟩,
  ⟨⟨-400429, 68⟩, ⟨-343399, 88⟩⟩,
  ⟨⟨-343367, 88⟩, ⟨-262149, 137⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private def eulerianCoefficients : List ℤ := [
  0x1, 0x7fffffffffffffffffffffffffff88, 0x186de33cddea5c979c905f6b9e84c93acafafef93afa32af,
  0x3ffffffffff48c7d7b77fa2498e06e53458db1c1ac70da587b2c5ac107d0, 0x13d3e2386229bb4fc50fa658916950bbc4d9023f6293927102c0d696bf199c0d231063, 0xc36f19523a323d6d1b8625170c31d174594929d871f36f463c9c55294e63ba42ea842dc364628,
  0x436d109ff82e7a0e076b8c2b08311d24b36388983a81822a6e33832078a5c2736f0fd051f4113e0c94cd, 0x1fffe064deda9d7ebbf7e481818ce145c7c6f07c65dc97a7542aae7194de65b4dba4f989095bf9cdf0c8edea40, 0x254bac6bc7e7944befd6af2cdeb9353b03851bce403b8fde599dd10f23b31f070daa14edd8284cd1b86b63c59257526,
  0x9e8d961276ed2f13523ef65c75447d0a2159b1dbc9d55e3b02b7ae10d05c58cec59d6747ba6c5f360fe2e3d8a52c716a670, 0xcbb36440af7a262fab23e534e37b48a9fa6d0f014ead146d256a77b57423905cbd3d48c302e7364249e9cc3208e079ad659d7ba, 0x6157ff4b5a05d790ecf3bffc2410ad0f7016c715c34fc48b9c747a29c496a49c5c73b292a7c93aedfabe16d17422aad884ed2bfd720,
  0x143f4ec423c85cd26bc6d3008fd5a8f734c77c18d9d3c51d3cab27fe5bd419c2c5d620802728b9e9b5f4222563b9de8d05fe347f046764a, 0x211e039b04ca2b131ee52676f65965c963cfe9f476c8f873a91b31fe490ed92908bd446f4258a19357a79de5873689e8614947017924239ef0, 0x1d4b5f5e08dc0fb640a9184a2699bb0703d5bbebe325c80b8b7496273461871df77eada26c39bacdf9b9aab383a5701ca2d8ad9c47d942e7a2496,
  0xf2099ced7cab692aaa3b81f27e06ae26c07f06a504dfcca78644e9ffde27d55354da21480cc52eb8e926b8ff3600d0a70c2488f879d45d4c3a49f40, 0x4da06adf17f9453917f50eb136301d8a02bef7250a684447ebad487f880e2aeed04427c259a3cfca69d11a0460f5fde3beeed27c7b51aabcd3f2b3c3b7, 0x1044c5f300a173ecfaf2428dd17bd54996a4accb285b3ded3299efea1011cbdc1e8ffb626e032626218c4c90d6300165a09fe8a5d16f5520a29a679cfe578,
  0x252e3702e63452773f2c3c67f2f5959ce9ecfb5cc93dbdb4db3c4caec184cd736fc9841871b0a9a352e03e1e39451d21bbd44312523e2bb6f19f8d82a197959, 0x3bfe20e0ee36c04bb6b2a7e84ec121b9b017a3fd19ddc81e95f67fc9a2a93b1615b91959f07ef20b91df78b13e87964a6baf03e609a55d02ac116abe33d6950f0, 0x46693505d083139f2d9baf29a317d295807b489495a17203adc5d1d8f06c1309c3eceba4521ca157aab2347232cb76680bb3f71c880882202d12ad5ca838a6c0e0d,
  0x3da7a22a713e3193b886b797cfe1693457262b8f017dea6a0d8663f7a4d2fadbed72d851aa6f9dce356154d85a39aaa120f2861e4292154153455fc74f2728bdc4418, 0x292aa3e843b54a4857c4be7eb93d57b48066f5e40a2c56687b311e651d551b9c97eb5a2a97a38835481f7d28d3e20902b7a7180a90d7b858e730085ae15730074ba8983, 0x155b9c309afc79969cae5d84a308414030ad36a7a3287cdb96b018870c75a4a1c982b09b3ef24769ee16e90cd8f75406caa918731b774d1480cc7a1e41e0f560c2f24b980,
  0x8c09e72cb8b86696c0c8b4cdbde7dc53c26725d309bb826f510be96cd3078c159fff60ae945b0da2116db10a77ec772e2cb6b4d27d40ed49267bd0159f371c2b8c68602b6c, 0x2dfc00ccd4bba66728aec1c528dfcafcb96e02a0ba47b43bc2f48e3ab23aed97ee68b3e58f2369d773de74ab79915aaf395889973cb2d70b39237a30646f6039cd049100cae0, 0xc40d5ad3785b42dfef0a52984b8ea688736854b24c1dc3bee24c32e4feb8fbd976905e0c952d50958e3f21add5e77bc1cf0d2d873a9528900ada5fd124d4597ca07bf35e56d54,
  0x2ade80a988f547ec24e06158b06e8a6f1cc48e542d2b8d6b84ef62d1de2e20bf42e58a988fefa7c2b5e5a9cb8192532c6d0777fd1e82e7bfa50e4dfe8008ba68314607851260d40, 0x7c4d985f9d505d4d1043dc49ac3478ba55f49a920a47bfe1d7a5805a952b58ef59015737a21294bb5806b95deaad3b2c25df75d7f40fc3f43ab18a451b5dbd0e4b2d2be3fc888f14, 0x12d6078dc547d182a52b92cada017aa081fc455b965cdea090537f38e325a997f52f2e4bc62c5494241f73396d46c1ebfad76319703785e411c0fc40afa4249fa2c2a2a90df649c8e0,
  0x267d91480c9fb8ccce899a1b922d1d3e5fd5a0fe1bdb78c001208523244386d9ab0ed2130cd3b3be32b49e3022d6261a74d44ba108d4b518a5fe9eb370b1202c15ccdd2bbca5f4591ac, 0x42c3d1e3c9feb40ccdd44430c88cf846049a46c0c7d01d6315ece9f31d8fa57657e3b70335911e7cd26bb5f9731b6f9a053e09e656609949eef4d92f77e0992a175ed9dfe2c0bbcca580, 0x62f0319812e780134fc038873357b0884e554b25260d166146ac2c3e7691981494fcebbd84fce99f468151a9fab8692cb3a6d59fd3604d03d12e0187170795a3fa00f9adfc6b01873ced1,
  0x7dfc726f2058042e81dabb325b88a2ba11009cb592b4600457d408dcae381cfee0e94adda9d662eff540315c2d6cfc483c6a232bd9182d43a10d37b85deff1a0573eac94457197df331388, 0x8a9516ee808f79752c853bfa95a65ae4973a81c538d7d44019ba147c72aa328d0de530969c3bed1605b69651266c6d28aa1c2440c158f07f63ac40a1462ace4d80ae28ed865a7335ad01e5f, 0x844f78c9a2c2e4e82ef56e78626ac5eb5fb17817058dcc9ec2825d8a98d384d20b0f750346b044318dd93cee12855d929e4e11c939af3a91235aeb005ce072a218058941ed0f7a554e9c6e50,
  0x6e1eca1b8f3f3e4a5b951314f0e6b6c6b62f74d9a11343ddebae1c502b757bad2f692c252b962b36aebd04cea266a9860e11b4d4cf9a6fda673d639b494710ff3300226ab8752fd2d3f0b5303, 0x5036946cd6313584da39936b5b4ba53305346e25480f8ac93a97ae893f9426b21e2a3e70cccfcf1e56c6337bc137b899ed05ec01adf2dd6a98d2ac3f55fecf807c34aa8016fb4f532e618c3da8, 0x33523c511846fdf1098c8cc78e2df2ac9cf33704569245847d8a28c58f661171dbb01af781165204cefe5920a13fe967eab26c23e6a4dd96c9a698f16d7bae7029934d7be4ec71e340fe49992ad,
  0x1cefd766105223ee6990f253dec82f3f94c0be5cdc1c82e7edbc6cd809909626d85f6c2c747e83dba8b68bbc5404d8cb030df81071b5f2cc146b215c4e39268fb3eb4db79264ea09ebb67b8a12c0, 0xe6bf51aec485af5b8c82fcb3ce19ddb3a8a123375b148b9a045728e3bbe72ef67d68d48b4b4b6399f1a793737f341715721b3bc277842efb41dc8b625d5ec24f5e2c69d012e54ce27a77c9a1756a, 0x65ee56d80082e949c6ae0aaadaa2a9feacb029513a62959300cc4ff83522d49aa2dba5774093cfcc64eb64a6ec4cca3495aabe470c4c473a9ec337bd78144132e0e75be6aee01a1701d6c5c3c0310,
  0x2802a2b422f26777ac7870d5679da70de0db60bd0c729a94e00945d8dcffce8153728703df6662ed20e4bf676e22075acf3608b534a95d1511da7f22bc1073e20117a45ac692974ecef20951a8e1b6, 0xdfcb658746f95f19676ea16df785cef2bf2d5cc7615a8edf0d27e69778743d94a8b728e05fe23c7609ecd5185fbe887d17fb12ff376f5d6d479acfd6e3d24b4b87a7e606e2eb691324c7f218d15ae0, 0x45d31b824806c9245391856fb41b306c839b514fa15df53d92ab4c79249622a9da6a25057b8b72828249e83769f17695422f6cafba78095cd98dc4858d647a00cbcc1e3d2fe8aabd7ba0c29ff9ef286,
  0x137afbd9ef1256791d26ea6030eeba2b7eca69be00e539fabfffea9451115c6b32e7d67564d79264ef5f62a6eceac0e6d8f83b4fc2e1c9fc8b9eebec0dfe1634828125590fe3c8b2e1bada34c0609d90, 0x4de441704b18cf21b94606d6ccfbf11035e6aca0769f1b6bb7a405149279855464c86523f359cb4e9709ae43e451cab2d7d41049fccad817498e175612e5be339d4ba3affd12b8e46eb729a426386a9a, 0x1176a5a873fcf02af8431940cfde55fada4870554709d4125f7606b172efecdd20d54041fd9a433a1bee598c9ccd3b0b7038bee43ec3ee46dee01b74cb410d91f568a6629d8af5df2eff1bb99dcfd1bc0,
  0x38485d53585de4e82a561bfeac4a4192253ef12d10c7f256d718f52594bfdc6cbea5e904c49fb9219afb44be97f1b31d39594a6c6429c1d50a5f6e90215e06f80a48ca81d2d573d735db03c9709e7bb4f, 0xa32d617056d1248b5996208f3cf321aa6a2e60b46d70cbc25fbfbc40ac61f4fb7d035a013b8599c65c31c5f1b00e6563c2c1f9093b4ef416db3257b5dedda81bdf1a97c082bb116e6d63ffa0fe622c2b8, 0x1aa1263cd209e44a14e2525dcd429d60af67326e216ffcd8438885a6bfedd48db0e5c766933d035b26c79d29a10b1ed69d39437536bacd4ebdef76e3416629aab9c0d7107c73b7a488780c6d64d1c5ecc1,
  0x3eaf76744aa9384f327eff573993a420e779ce6b1bf5ce0a86862d2923f616ada87e9f105c6e19f027bddbd711860c5e25c6b04fb23395fb120681a4acf99675d46cff3a69da95fd62cc87902355a438f0, 0x8526481c8ef15bbb9a8696cd58251ca4618164339da5f0b31c0259fbd51733e6152e2caaa2345426dcc24fe35d0fec134e4f8b10e6c2d27ab7f5d600df9d377b9b8c39cef152b3afdc6528c4cbbe54f765, 0xff6673af10259c4a7b366595fb1682939a37e968ab4d5325a2962d228d30ab904e58497b37da49987b938b05b4b077bce9c3e3308fbefc2e061085bcbd5e1bc5ea1cfa5e7d180061235b5863e0d3a27cd8,
  0x1bab0f9b67e98551552b051c0b013967aca577f80fd189d100fc04c36471deacac35869df412ee0f775666a0c466df541ddf46b05197ee42d562cf90af5e90fc3d53cce5289643685f40749301d883ce12b, 0x2b5c79ec856a6f5783e332dd5cdd6e95131c323dbb644dcd60110b01d42d77cb79adeb5df84faa6c70782cba72da46f52b198fd6aacc9d0b0b0eacb3e3d483629a796521e43c3b000b08aae9baeeff4e900, 0x3d7833eb011f5387e9741759e182a48fc719bd6d4d292f6443a15b9bfcc3372b2c73d89c167fb3d8afad3f0cb3e4d222ea488fa0594c11e307de2a63c0954ff665f47b92b6d50fbdd0834ea0c135c33e928,
  0x4ed9e4e7c6966fb710b482f3d2b7bc8029532f3bd8b12f2f456535077e08d7ff521889114cb466d4279059ad017f81d7e577975ed97453e77995cd7aaf9865366e4ff09e957cd2493852e991f6d94778640, 0x5b8c8e0dd1fce90e9e91abbc6e729c0f3469f1138dd031a3b6db60391697ae9a05717d8a316604bfa6511a5c80c0b8efe7ca833990d835b7626ba9c285bb9553619ff714e4c2e4e90834b32da13bf10c158, 0x60381fd6a00c1813e40f1251d1d39269cf4ef0f9caaa1ae988418abb2e18028e4b24536a5e00b2b671b539d326aab38ab6d1ffcba599eaac145edcd8a34c8352cfb368abe58966fe51353c51c598dbb8180,
  0x5b8c8e0dd1fce90e9e91abbc6e729c0f3469f1138dd031a3b6db60391697ae9a05717d8a316604bfa6511a5c80c0b8efe7ca833990d835b7626ba9c285bb9553619ff714e4c2e4e90834b32da13bf10c158, 0x4ed9e4e7c6966fb710b482f3d2b7bc8029532f3bd8b12f2f456535077e08d7ff521889114cb466d4279059ad017f81d7e577975ed97453e77995cd7aaf9865366e4ff09e957cd2493852e991f6d94778640, 0x3d7833eb011f5387e9741759e182a48fc719bd6d4d292f6443a15b9bfcc3372b2c73d89c167fb3d8afad3f0cb3e4d222ea488fa0594c11e307de2a63c0954ff665f47b92b6d50fbdd0834ea0c135c33e928,
  0x2b5c79ec856a6f5783e332dd5cdd6e95131c323dbb644dcd60110b01d42d77cb79adeb5df84faa6c70782cba72da46f52b198fd6aacc9d0b0b0eacb3e3d483629a796521e43c3b000b08aae9baeeff4e900, 0x1bab0f9b67e98551552b051c0b013967aca577f80fd189d100fc04c36471deacac35869df412ee0f775666a0c466df541ddf46b05197ee42d562cf90af5e90fc3d53cce5289643685f40749301d883ce12b, 0xff6673af10259c4a7b366595fb1682939a37e968ab4d5325a2962d228d30ab904e58497b37da49987b938b05b4b077bce9c3e3308fbefc2e061085bcbd5e1bc5ea1cfa5e7d180061235b5863e0d3a27cd8,
  0x8526481c8ef15bbb9a8696cd58251ca4618164339da5f0b31c0259fbd51733e6152e2caaa2345426dcc24fe35d0fec134e4f8b10e6c2d27ab7f5d600df9d377b9b8c39cef152b3afdc6528c4cbbe54f765, 0x3eaf76744aa9384f327eff573993a420e779ce6b1bf5ce0a86862d2923f616ada87e9f105c6e19f027bddbd711860c5e25c6b04fb23395fb120681a4acf99675d46cff3a69da95fd62cc87902355a438f0, 0x1aa1263cd209e44a14e2525dcd429d60af67326e216ffcd8438885a6bfedd48db0e5c766933d035b26c79d29a10b1ed69d39437536bacd4ebdef76e3416629aab9c0d7107c73b7a488780c6d64d1c5ecc1,
  0xa32d617056d1248b5996208f3cf321aa6a2e60b46d70cbc25fbfbc40ac61f4fb7d035a013b8599c65c31c5f1b00e6563c2c1f9093b4ef416db3257b5dedda81bdf1a97c082bb116e6d63ffa0fe622c2b8, 0x38485d53585de4e82a561bfeac4a4192253ef12d10c7f256d718f52594bfdc6cbea5e904c49fb9219afb44be97f1b31d39594a6c6429c1d50a5f6e90215e06f80a48ca81d2d573d735db03c9709e7bb4f, 0x1176a5a873fcf02af8431940cfde55fada4870554709d4125f7606b172efecdd20d54041fd9a433a1bee598c9ccd3b0b7038bee43ec3ee46dee01b74cb410d91f568a6629d8af5df2eff1bb99dcfd1bc0,
  0x4de441704b18cf21b94606d6ccfbf11035e6aca0769f1b6bb7a405149279855464c86523f359cb4e9709ae43e451cab2d7d41049fccad817498e175612e5be339d4ba3affd12b8e46eb729a426386a9a, 0x137afbd9ef1256791d26ea6030eeba2b7eca69be00e539fabfffea9451115c6b32e7d67564d79264ef5f62a6eceac0e6d8f83b4fc2e1c9fc8b9eebec0dfe1634828125590fe3c8b2e1bada34c0609d90, 0x45d31b824806c9245391856fb41b306c839b514fa15df53d92ab4c79249622a9da6a25057b8b72828249e83769f17695422f6cafba78095cd98dc4858d647a00cbcc1e3d2fe8aabd7ba0c29ff9ef286,
  0xdfcb658746f95f19676ea16df785cef2bf2d5cc7615a8edf0d27e69778743d94a8b728e05fe23c7609ecd5185fbe887d17fb12ff376f5d6d479acfd6e3d24b4b87a7e606e2eb691324c7f218d15ae0, 0x2802a2b422f26777ac7870d5679da70de0db60bd0c729a94e00945d8dcffce8153728703df6662ed20e4bf676e22075acf3608b534a95d1511da7f22bc1073e20117a45ac692974ecef20951a8e1b6, 0x65ee56d80082e949c6ae0aaadaa2a9feacb029513a62959300cc4ff83522d49aa2dba5774093cfcc64eb64a6ec4cca3495aabe470c4c473a9ec337bd78144132e0e75be6aee01a1701d6c5c3c0310,
  0xe6bf51aec485af5b8c82fcb3ce19ddb3a8a123375b148b9a045728e3bbe72ef67d68d48b4b4b6399f1a793737f341715721b3bc277842efb41dc8b625d5ec24f5e2c69d012e54ce27a77c9a1756a, 0x1cefd766105223ee6990f253dec82f3f94c0be5cdc1c82e7edbc6cd809909626d85f6c2c747e83dba8b68bbc5404d8cb030df81071b5f2cc146b215c4e39268fb3eb4db79264ea09ebb67b8a12c0, 0x33523c511846fdf1098c8cc78e2df2ac9cf33704569245847d8a28c58f661171dbb01af781165204cefe5920a13fe967eab26c23e6a4dd96c9a698f16d7bae7029934d7be4ec71e340fe49992ad,
  0x5036946cd6313584da39936b5b4ba53305346e25480f8ac93a97ae893f9426b21e2a3e70cccfcf1e56c6337bc137b899ed05ec01adf2dd6a98d2ac3f55fecf807c34aa8016fb4f532e618c3da8, 0x6e1eca1b8f3f3e4a5b951314f0e6b6c6b62f74d9a11343ddebae1c502b757bad2f692c252b962b36aebd04cea266a9860e11b4d4cf9a6fda673d639b494710ff3300226ab8752fd2d3f0b5303, 0x844f78c9a2c2e4e82ef56e78626ac5eb5fb17817058dcc9ec2825d8a98d384d20b0f750346b044318dd93cee12855d929e4e11c939af3a91235aeb005ce072a218058941ed0f7a554e9c6e50,
  0x8a9516ee808f79752c853bfa95a65ae4973a81c538d7d44019ba147c72aa328d0de530969c3bed1605b69651266c6d28aa1c2440c158f07f63ac40a1462ace4d80ae28ed865a7335ad01e5f, 0x7dfc726f2058042e81dabb325b88a2ba11009cb592b4600457d408dcae381cfee0e94adda9d662eff540315c2d6cfc483c6a232bd9182d43a10d37b85deff1a0573eac94457197df331388, 0x62f0319812e780134fc038873357b0884e554b25260d166146ac2c3e7691981494fcebbd84fce99f468151a9fab8692cb3a6d59fd3604d03d12e0187170795a3fa00f9adfc6b01873ced1,
  0x42c3d1e3c9feb40ccdd44430c88cf846049a46c0c7d01d6315ece9f31d8fa57657e3b70335911e7cd26bb5f9731b6f9a053e09e656609949eef4d92f77e0992a175ed9dfe2c0bbcca580, 0x267d91480c9fb8ccce899a1b922d1d3e5fd5a0fe1bdb78c001208523244386d9ab0ed2130cd3b3be32b49e3022d6261a74d44ba108d4b518a5fe9eb370b1202c15ccdd2bbca5f4591ac, 0x12d6078dc547d182a52b92cada017aa081fc455b965cdea090537f38e325a997f52f2e4bc62c5494241f73396d46c1ebfad76319703785e411c0fc40afa4249fa2c2a2a90df649c8e0,
  0x7c4d985f9d505d4d1043dc49ac3478ba55f49a920a47bfe1d7a5805a952b58ef59015737a21294bb5806b95deaad3b2c25df75d7f40fc3f43ab18a451b5dbd0e4b2d2be3fc888f14, 0x2ade80a988f547ec24e06158b06e8a6f1cc48e542d2b8d6b84ef62d1de2e20bf42e58a988fefa7c2b5e5a9cb8192532c6d0777fd1e82e7bfa50e4dfe8008ba68314607851260d40, 0xc40d5ad3785b42dfef0a52984b8ea688736854b24c1dc3bee24c32e4feb8fbd976905e0c952d50958e3f21add5e77bc1cf0d2d873a9528900ada5fd124d4597ca07bf35e56d54,
  0x2dfc00ccd4bba66728aec1c528dfcafcb96e02a0ba47b43bc2f48e3ab23aed97ee68b3e58f2369d773de74ab79915aaf395889973cb2d70b39237a30646f6039cd049100cae0, 0x8c09e72cb8b86696c0c8b4cdbde7dc53c26725d309bb826f510be96cd3078c159fff60ae945b0da2116db10a77ec772e2cb6b4d27d40ed49267bd0159f371c2b8c68602b6c, 0x155b9c309afc79969cae5d84a308414030ad36a7a3287cdb96b018870c75a4a1c982b09b3ef24769ee16e90cd8f75406caa918731b774d1480cc7a1e41e0f560c2f24b980,
  0x292aa3e843b54a4857c4be7eb93d57b48066f5e40a2c56687b311e651d551b9c97eb5a2a97a38835481f7d28d3e20902b7a7180a90d7b858e730085ae15730074ba8983, 0x3da7a22a713e3193b886b797cfe1693457262b8f017dea6a0d8663f7a4d2fadbed72d851aa6f9dce356154d85a39aaa120f2861e4292154153455fc74f2728bdc4418, 0x46693505d083139f2d9baf29a317d295807b489495a17203adc5d1d8f06c1309c3eceba4521ca157aab2347232cb76680bb3f71c880882202d12ad5ca838a6c0e0d,
  0x3bfe20e0ee36c04bb6b2a7e84ec121b9b017a3fd19ddc81e95f67fc9a2a93b1615b91959f07ef20b91df78b13e87964a6baf03e609a55d02ac116abe33d6950f0, 0x252e3702e63452773f2c3c67f2f5959ce9ecfb5cc93dbdb4db3c4caec184cd736fc9841871b0a9a352e03e1e39451d21bbd44312523e2bb6f19f8d82a197959, 0x1044c5f300a173ecfaf2428dd17bd54996a4accb285b3ded3299efea1011cbdc1e8ffb626e032626218c4c90d6300165a09fe8a5d16f5520a29a679cfe578,
  0x4da06adf17f9453917f50eb136301d8a02bef7250a684447ebad487f880e2aeed04427c259a3cfca69d11a0460f5fde3beeed27c7b51aabcd3f2b3c3b7, 0xf2099ced7cab692aaa3b81f27e06ae26c07f06a504dfcca78644e9ffde27d55354da21480cc52eb8e926b8ff3600d0a70c2488f879d45d4c3a49f40, 0x1d4b5f5e08dc0fb640a9184a2699bb0703d5bbebe325c80b8b7496273461871df77eada26c39bacdf9b9aab383a5701ca2d8ad9c47d942e7a2496,
  0x211e039b04ca2b131ee52676f65965c963cfe9f476c8f873a91b31fe490ed92908bd446f4258a19357a79de5873689e8614947017924239ef0, 0x143f4ec423c85cd26bc6d3008fd5a8f734c77c18d9d3c51d3cab27fe5bd419c2c5d620802728b9e9b5f4222563b9de8d05fe347f046764a, 0x6157ff4b5a05d790ecf3bffc2410ad0f7016c715c34fc48b9c747a29c496a49c5c73b292a7c93aedfabe16d17422aad884ed2bfd720,
  0xcbb36440af7a262fab23e534e37b48a9fa6d0f014ead146d256a77b57423905cbd3d48c302e7364249e9cc3208e079ad659d7ba, 0x9e8d961276ed2f13523ef65c75447d0a2159b1dbc9d55e3b02b7ae10d05c58cec59d6747ba6c5f360fe2e3d8a52c716a670, 0x254bac6bc7e7944befd6af2cdeb9353b03851bce403b8fde599dd10f23b31f070daa14edd8284cd1b86b63c59257526,
  0x1fffe064deda9d7ebbf7e481818ce145c7c6f07c65dc97a7542aae7194de65b4dba4f989095bf9cdf0c8edea40, 0x436d109ff82e7a0e076b8c2b08311d24b36388983a81822a6e33832078a5c2736f0fd051f4113e0c94cd, 0xc36f19523a323d6d1b8625170c31d174594929d871f36f463c9c55294e63ba42ea842dc364628,
  0x13d3e2386229bb4fc50fa658916950bbc4d9023f6293927102c0d696bf199c0d231063, 0x3ffffffffff48c7d7b77fa2498e06e53458db1c1ac70da587b2c5ac107d0, 0x186de33cddea5c979c905f6b9e84c93acafafef93afa32af,
  0x7fffffffffffffffffffffffffff88, 0x1]

private theorem eulerianCoefficients_eq : descentCoeffs 119 = eulerianCoefficients := by
  decide +kernel

private theorem upper : upperOK (descentCoeffs 119) first gaps = true := by
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

private theorem lower (i : Fin (lastRepresentative 120 - 2)) :
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

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 120) :
    StrictNegativeInterlacing (originalQuotient 120 k) (eulerian 119) 117 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N120
