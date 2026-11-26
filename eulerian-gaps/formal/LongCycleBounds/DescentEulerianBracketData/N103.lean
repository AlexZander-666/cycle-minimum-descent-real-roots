import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentPackedData.C127L104.N103

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N103

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L104.N103 LongCycleBounds.DescentNecklace.Packed.C127L104.N103.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L104.N103 LongCycleBounds.DescentNecklace.Packed.C127L104.N103.rows

private theorem actual : RepresentativeChecks 103 previousNodes rows :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L104.N103 LongCycleBounds.DescentNecklace.Packed.C127L104.N103.dataChecks

private def first : LongCycleFinite.Dyadic := ⟨-5070602400912917605986812821504, 0⟩

private def gaps : List Window := [
  ⟨⟨-5070437987001450016419052781568, 0⟩, ⟨-1036914231783456768, 0⟩⟩,
  ⟨⟨-892799043707600896, 0⟩, ⟨-5560774688768, 0⟩⟩,
  ⟨⟨-5524737228800, 0⟩, ⟨-7789215744, 0⟩⟩,
  ⟨⟨-7535951872, 0⟩, ⟨-114045696, 0⟩⟩,
  ⟨⟨-113683968, 0⟩, ⟨-6190944, 0⟩⟩,
  ⟨⟨-6185472, 0⟩, ⟨-724546, 0⟩⟩,
  ⟨⟨-724260, 0⟩, ⟨-139398, 0⟩⟩,
  ⟨⟨-278733, 1⟩, ⟨-301503, 3⟩⟩,
  ⟨⟨-150729, 2⟩, ⟨-25979, 1⟩⟩,
  ⟨⟨-103905, 3⟩, ⟨-171431, 5⟩⟩,
  ⟨⟨-171417, 5⟩, ⟨-324119, 7⟩⟩,
  ⟨⟨-162049, 6⟩, ⟨-340677, 8⟩⟩,
  ⟨⟨-170329, 7⟩, ⟨-194725, 8⟩⟩,
  ⟨⟨-389433, 9⟩, ⟨-476409, 10⟩⟩,
  ⟨⟨-476391, 10⟩, ⟨-307979, 10⟩⟩,
  ⟨⟨-1203, 2⟩, ⟨-26053, 7⟩⟩,
  ⟨⟨-104209, 9⟩, ⟨-293127, 11⟩⟩,
  ⟨⟨-293119, 11⟩, ⟨-425831, 12⟩⟩,
  ⟨⟨-425821, 12⟩, ⟨-621, 3⟩⟩,
  ⟨⟨-317945, 12⟩, ⟨-243099, 12⟩⟩,
  ⟨⟨-486189, 13⟩, ⟨-11857, 8⟩⟩,
  ⟨⟨-379417, 13⟩, ⟨-150711, 12⟩⟩,
  ⟨⟨-37677, 10⟩, ⟨-486427, 14⟩⟩,
  ⟨⟨-486419, 14⟩, ⟨-99473, 12⟩⟩,
  ⟨⟨-397885, 14⟩, ⟨-164715, 13⟩⟩,
  ⟨⟨-329425, 14⟩, ⟨-137839, 13⟩⟩,
  ⟨⟨-137837, 13⟩, ⟨-116451, 13⟩⟩,
  ⟨⟨-232899, 14⟩, ⟨-198437, 14⟩⟩,
  ⟨⟨-396869, 15⟩, ⟨-340715, 15⟩⟩,
  ⟨⟨-340711, 15⟩, ⟨-294495, 15⟩⟩,
  ⟨⟨-294491, 15⟩, ⟨-512195, 16⟩⟩,
  ⟨⟨-256095, 15⟩, ⟨-447859, 16⟩⟩,
  ⟨⟨-447855, 16⟩, ⟨-393537, 16⟩⟩,
  ⟨⟨-393533, 16⟩, ⟨-43417, 13⟩⟩,
  ⟨⟨-86833, 14⟩, ⟨-76945, 14⟩⟩,
  ⟨⟨-307777, 16⟩, ⟨-68427, 14⟩⟩,
  ⟨⟨-273705, 16⟩, ⟨-488381, 17⟩⟩,
  ⟨⟨-488377, 17⟩, ⟨-218485, 16⟩⟩,
  ⟨⟨-218483, 16⟩, ⟨-48997, 14⟩⟩,
  ⟨⟨-391973, 17⟩, ⟨-176211, 16⟩⟩,
  ⟨⟨-176209, 16⟩, ⟨-79375, 15⟩⟩,
  ⟨⟨-317497, 17⟩, ⟨-286549, 17⟩⟩,
  ⟨⟨-143273, 16⟩, ⟨-129507, 16⟩⟩,
  ⟨⟨-64753, 15⟩, ⟨-58609, 15⟩⟩,
  ⟨⟨-117217, 16⟩, ⟨-424857, 18⟩⟩,
  ⟨⟨-424853, 18⟩, ⟨-24083, 14⟩⟩,
  ⟨⟨-385325, 18⟩, ⟨-349733, 18⟩⟩,
  ⟨⟨-174865, 17⟩, ⟨-79399, 16⟩⟩,
  ⟨⟨-317593, 18⟩, ⟨-288515, 18⟩⟩,
  ⟨⟨-288513, 18⟩, ⟨-262145, 18⟩⟩,
  ⟨⟨-524285, 19⟩, ⟨-476369, 19⟩⟩,
  ⟨⟨-476365, 19⟩, ⟨-27047, 15⟩⟩,
  ⟨⟨-432749, 19⟩, ⟨-392987, 19⟩⟩,
  ⟨⟨-49123, 16⟩, ⟨-178341, 18⟩⟩,
  ⟨⟨-356679, 19⟩, ⟨-40437, 16⟩⟩,
  ⟨⟨-323493, 19⟩, ⟨-293129, 19⟩⟩,
  ⟨⟨-293127, 19⟩, ⟨-265315, 19⟩⟩,
  ⟨⟨-8291, 14⟩, ⟨-479639, 20⟩⟩,
  ⟨⟨-479635, 20⟩, ⟨-216441, 19⟩⟩,
  ⟨⟨-216439, 19⟩, ⟨-389987, 20⟩⟩,
  ⟨⟨-389983, 20⟩, ⟨-350633, 20⟩⟩,
  ⟨⟨-175315, 19⟩, ⟨-314531, 20⟩⟩,
  ⟨⟨-9829, 15⟩, ⟨-70355, 18⟩⟩,
  ⟨⟨-281417, 20⟩, ⟨-502141, 21⟩⟩,
  ⟨⟨-502137, 21⟩, ⟨-446553, 21⟩⟩,
  ⟨⟨-446549, 21⟩, ⟨-98925, 19⟩⟩,
  ⟨⟨-24731, 17⟩, ⟨-349245, 21⟩⟩,
  ⟨⟨-349241, 21⟩, ⟨-306883, 21⟩⟩,
  ⟨⟨-4795, 15⟩, ⟨-16771, 17⟩⟩,
  ⟨⟨-268333, 21⟩, ⟨-466699, 22⟩⟩,
  ⟨⟨-233347, 21⟩, ⟨-100847, 20⟩⟩,
  ⟨⟨-50423, 19⟩, ⟨-86577, 20⟩⟩,
  ⟨⟨-346303, 22⟩, ⟨-147531, 21⟩⟩,
  ⟨⟨-147529, 21⟩, ⟨-249277, 22⟩⟩,
  ⟨⟨-124637, 21⟩, ⟨-52151, 20⟩⟩,
  ⟨⟨-417203, 23⟩, ⟨-345419, 23⟩⟩,
  ⟨⟨-172707, 22⟩, ⟨-70639, 21⟩⟩,
  ⟨⟨-282551, 23⟩, ⟨-56997, 21⟩⟩,
  ⟨⟨-455969, 24⟩, ⟨-362237, 24⟩⟩,
  ⟨⟨-362231, 24⟩, ⟨-4417, 18⟩⟩,
  ⟨⟨-282683, 24⟩, ⟨-432267, 25⟩⟩,
  ⟨⟨-432259, 25⟩, ⟨-322763, 25⟩⟩,
  ⟨⟨-80689, 23⟩, ⟨-468885, 26⟩⟩,
  ⟨⟨-468875, 26⟩, ⟨-164859, 25⟩⟩,
  ⟨⟨-329711, 26⟩, ⟨-223139, 26⟩⟩,
  ⟨⟨-223133, 26⟩, ⟨-288501, 27⟩⟩,
  ⟨⟨-72123, 25⟩, ⟨-88229, 26⟩⟩,
  ⟨⟨-352905, 28⟩, ⟨-403453, 29⟩⟩,
  ⟨⟨-403439, 29⟩, ⟨-424059, 30⟩⟩,
  ⟨⟨-424043, 30⟩, ⟨-400889, 31⟩⟩,
  ⟨⟨-50109, 28⟩, ⟨-330673, 32⟩⟩,
  ⟨⟨-165329, 31⟩, ⟨-227959, 33⟩⟩,
  ⟨⟨-455895, 34⟩, ⟨-123269, 34⟩⟩,
  ⟨⟨-493047, 36⟩, ⟨-189761, 37⟩⟩,
  ⟨⟨-189749, 37⟩, ⟨-177719, 40⟩⟩,
  ⟨⟨-355413, 41⟩, ⟨-77197, 43⟩⟩,
  ⟨⟨-77191, 43⟩, ⟨-74471, 49⟩⟩,
  ⟨⟨-74465, 49⟩, ⟨-416591, 61⟩⟩,
  ⟨⟨-104139, 59⟩, ⟨-330403, 78⟩⟩,
  ⟨⟨-82593, 76⟩, ⟨-262165, 120⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private def eulerianCoefficients : List ℤ := [
  0x1, 0x3fffffffffffffffffffffff99, 0x32c78f21da0f291493551b3248b38680448f8c6de,
  0xffffffffeb91b5696143e62508b8c20ec4bfc4e2646a3ed8b5e, 0x1c931e844871732f828d4d339bea3f4bc177f384a63f8724e8aade2fd261, 0xcb1e310836f422dca7fc60e57f225d4e352af568fd7ee142e3a8b5b3884a544889,
  0x519501c2bfe1cca19b32c2ad28652c35672d8155f3c8e5b133f2f77bff1ffbd540aee670, 0x3ffdf2cfbb108d0928ae3ae1ade425ecd97d1539cf28335141f7cb5a854e168972cc895ad0770, 0xa10f37f99e0bc46d848cd5407494d17ddb0d50f2e7753889df7b04c0e51d3cbef6d74529f7a48935c,
  0x720ba7d078ad64572196b517e2c44130c58c1e0a3ad42a625c796ca1d8bceb5d8baaedbfb6a245120057c, 0x1ce6e7261e45a0a70c3aefb6159c863a19c1a379e4e4801dad7773e4e7314cf8bc017a084e3936e63b0c8ee58, 0x320ceb744aa882aaec2dff2b50d8c98a528f8109aa2003613211ac39b90ea97ffa62393116ee10e0d08f29976958,
  0x2a4a2b27827770e928465247f36401397828f2484d84ea2ed5b5935c76c5930195fb766a7c2780793538b3d620c8eec, 0x1350fb16024f412a7092c12234e4fc59df467a560ed55a6c00d70befbda3fba9bf535bd328f9cadd8419ed4ee50692d14c, 0x52b2b3a7941d44c22034be1fa818472a1f9bb4760c571b028f83c916ee8d1829a1c96d3d7621dfa6151e402412da88d3d490,
  0xdd1e59201cc30a76215fec92b01b74ed5315ef90f3890006cc4e4189e0d046bce32c47fdf853e86064013c6b0ea46a464a1990, 0x184d83f4cbe5899a14c2248136d76fbccf3bada5f36b7646ec79f7f4cd79f0ce693aaa047605905d9244538c191b66af5e6ee727a, 0x1d52c4fe23dc004ddd22cd94d6f1c12b1c65735331dd3b759ea8c2de8d2b2a5ce6960059f39e79ddf9260c782313a937497b9167b6a,
  0x192458756d64875032d09d5b5df018f2e1349170e64629a74ef429df107572a84349bd1bfa88d572e0b24a5966f9c7a8a641bccb8693c, 0xfc6424d2653c91da6646daed7101c6a70958a1d3a6dbd620d1eeacac44432c14fe109916a00773537290d541935adb25ca664e50aa6f3c, 0x76c8d5dcf4db9ea606bf467ee3055abf0a855a44b80afe414be9aea1089a7c0ac9083bebdbf676ab017dc1be6b3436e74b566c2179714bca,
  0x2ad474a88823435b3238647272f19773af05b7e6d3a29a8b5b631d72a7a3210ca25b14fdc124d0ac142c7a0e782458733b294f26609fba0fda, 0xc0c441633fcce61e82dc5c79a1651bdf8959a7581b8514362985d497e9b08ac4f6dbb8c3fad553fa09a7a8f643152f0934827d7d5b081acc8d0, 0x2af8d3a6398d0cc850c6c85eb7c76836c2633941f44838006aaa88ce1b964aaefcdc78a4e781dcdd06aad3b2b97833b5d6dc468ab18d24e95afd0,
  0x7b2223d69358ee7f2ec3fbfa969aabb4dee3f09028b3f8f26857e69117fec59dc451e7d3100e967aa663d1253b2e90a9a6e302abf2e444f802485c, 0x11edc73b838b6ccc5672fde0a4108633c99f9bd70b8e84ea1b6b1f28d083d9f40b1878db29126438265102693e441d37488e7e2bd4bcff8a9f09317c, 0x22515484c14428a77ae05d95dcae423d58f4957160e8d103d6081dd42681fa62a16c1592a25a997ed574fcaf6cc76769425232928dd313b4ec019bdf8,
  0x3679550406d41e0e65035f989f9c568a532647b3ed95366909362b493e62f85ca859f26a7095f6d0eab726c000a10ae82ac72c3451985a3c9c0f4286f8, 0x484d0319435896185f916b8710bceb998e23af2dfbd9533007e93d6c16037e40a1eb6b6614ff6cc6b2ae40a84feebaac7bda305267bdab844b4d045ed4c, 0x50d443cc06292d7094a637e833e0c9b63ca0c564f788edecba8f55fe7ab001fcd7e9e6bf195929d7ab7e9f1269d2cdcd59121348a9f7fb2a0dfc6018a5ac,
  0x4c9d3bc94ee8cacdb22ec6a504eed45cbc7b2026a699aa43fc504152217abfcc1e480685fb2b06e0f75f36dfd730b1539db1b78da971c71b0582457ce5830, 0x3dee9516c754a4f13b7b10a629694fef366aaa4a735da58d354be477c9a78b5f3335b4d1d4ad5dca5256354cf59bc465787d5047d4cb97611a0cf8a7a6d330, 0x2aebcdcf1c39b5b4d4a57f92324c0ea7ce42f8e2079f3dd488500c29983576dfe5823f50cae58ed8e3a558ea157784cedb4db3628352d0a9ecbc27cb03d9817,
  0x199f83f4db7645573a1825b09a173b3a53682b72754aeedea0701b691677b46ebdede8aac07abc8eb057bf7e4399c9bfda7a78709d285b726049bc27ef1e9e3f, 0xd3b8c40b333f72ef4496a27848ca46640768e9085022e01e0de01c427f72e729a1cc344ee4db17a9c8177dcb169a1bff8da06711abf90fb2894d8dff399c3bc2, 0x5ef33aeddeb867ba78c203bb4a697372b02c1ac972c69f7b13800c5cfd3547ebe24db9d1a463a838bd6f2481e7f69bde81d93a0bce72fca10eb23bccfc26c6242,
  0x251b08af856542b700a60247e80a53881041bf169f3ad947586324122f42dcdf9cf4d259b39b295d90e85102b5b82a1d29ae2f202f1358039769678c95ae52fd27, 0xcacc694e6ab074f59807dbcf1ced442ffbe1714cbb692d69b77b8419610d56c73968817b2b4e3b6581bfbd65b5c77227488f31c7ddc8b59ace76aff29e4f953bbf, 0x3cb8af848d87b330d079836e9c98fa17a485661b84a6d6a41963683ec781323944a5cfb8642690b81461e78bcd04fcaaa816257eec7d818490c343136847a87d160,
  0xff9f0f243abd4053e4e603552a65f9947256443c2dacd200d8443836347a578d03b9c7d48b2088f5401802d88ea3fe2c6bb1b6cd8d9949b7b51e9f774cf691b9b60, 0x3b3b8ce04de806fb6ae894b29c7ffda2885941d38f8dd1f03f568d4af169fecff587e117fa9aec92493d4a3072b1df9b74337571ea83c37cadf7f0e0f37cc6d07178, 0xc1cb01e7c10d908e04b58a46ef774d353886459cac9239caeb1d761aa7586f82fd937415dbc0d68b530cba388d0a84a8e9ddc53331d33d58ee8e605949d406246bb8,
  0x2307f8ca5c749fa63fb08def85fa530d505339bfbda6ae0d5633bc21728fb6d86d4ea1b45e9b0998dda7b517e77593202476f999f0c9260ad18d48bbfadc0e6e69ab0, 0x59b4cbeb9d03c72f7b12e27c8f3e5e71a89c4f6575dccef6702d24db634422cdd5fa7cca0b053e3a2f65e87168d798b10a4caf3790bb7f9505a821f7dc9ab523ed8b0, 0xcba9620cdbeebbfe88526aa2aedb4e51c85ea7f1b1d303fa63af8adcbe29be727a956aa6c409cd3eca0a8768ce73948db5e6ac979eb528a6cd3f0498f9c3cc29c9918,
  0x19a68e76f22d01c7e7585ac87f71ae1b3a4ba43eea9e7e3cdbfb1bf0c95ffd710276547515636804d49c435648603bcaaf8699651512db8d58f5402d75744ea502b3d8, 0x2dece68b78e891d59073197230a56936bf5302408740b3005e650e5d6d8592706e9e85b5a44b2ea24e1c593815b66467dd9a033b7237a0cb5d8801e4983faeeac980a0, 0x491d5785c0e74adc5bbbf12bdc7643008081ba6020511d084f494e7d706532bb248a43e775b3b26b3b6f802c7869bdf402737f217d2944c54b471f05ac20efb56192a0,
  0x6791926f25b80f8494afa65f6dbb752b8b261bae37d0959eae488f1b61874bd6fa54e916b717a2f3e1329669f729f17331bc2178a2b5f1226714c7eb06728b9e66e94c, 0x8298a5935a1cd9728bc1a7ed8ebcfabef18722917fdf97f8b37e2a66524f37669a7e6bb44bfa522cfcac59e8ef1c6f984faf198368672707ee8c9caac66615b29a136c, 0x92a3769255e0ff59ff4351b7cf1fd3262c46c46b49713d8e76718e8b5af4b4f4b14da6e300be51a4c4b4645772f71f575e20a170f0d005518d5015d48beebd1dcc2748,
  0x92a3769255e0ff59ff4351b7cf1fd3262c46c46b49713d8e76718e8b5af4b4f4b14da6e300be51a4c4b4645772f71f575e20a170f0d005518d5015d48beebd1dcc2748, 0x8298a5935a1cd9728bc1a7ed8ebcfabef18722917fdf97f8b37e2a66524f37669a7e6bb44bfa522cfcac59e8ef1c6f984faf198368672707ee8c9caac66615b29a136c, 0x6791926f25b80f8494afa65f6dbb752b8b261bae37d0959eae488f1b61874bd6fa54e916b717a2f3e1329669f729f17331bc2178a2b5f1226714c7eb06728b9e66e94c,
  0x491d5785c0e74adc5bbbf12bdc7643008081ba6020511d084f494e7d706532bb248a43e775b3b26b3b6f802c7869bdf402737f217d2944c54b471f05ac20efb56192a0, 0x2dece68b78e891d59073197230a56936bf5302408740b3005e650e5d6d8592706e9e85b5a44b2ea24e1c593815b66467dd9a033b7237a0cb5d8801e4983faeeac980a0, 0x19a68e76f22d01c7e7585ac87f71ae1b3a4ba43eea9e7e3cdbfb1bf0c95ffd710276547515636804d49c435648603bcaaf8699651512db8d58f5402d75744ea502b3d8,
  0xcba9620cdbeebbfe88526aa2aedb4e51c85ea7f1b1d303fa63af8adcbe29be727a956aa6c409cd3eca0a8768ce73948db5e6ac979eb528a6cd3f0498f9c3cc29c9918, 0x59b4cbeb9d03c72f7b12e27c8f3e5e71a89c4f6575dccef6702d24db634422cdd5fa7cca0b053e3a2f65e87168d798b10a4caf3790bb7f9505a821f7dc9ab523ed8b0, 0x2307f8ca5c749fa63fb08def85fa530d505339bfbda6ae0d5633bc21728fb6d86d4ea1b45e9b0998dda7b517e77593202476f999f0c9260ad18d48bbfadc0e6e69ab0,
  0xc1cb01e7c10d908e04b58a46ef774d353886459cac9239caeb1d761aa7586f82fd937415dbc0d68b530cba388d0a84a8e9ddc53331d33d58ee8e605949d406246bb8, 0x3b3b8ce04de806fb6ae894b29c7ffda2885941d38f8dd1f03f568d4af169fecff587e117fa9aec92493d4a3072b1df9b74337571ea83c37cadf7f0e0f37cc6d07178, 0xff9f0f243abd4053e4e603552a65f9947256443c2dacd200d8443836347a578d03b9c7d48b2088f5401802d88ea3fe2c6bb1b6cd8d9949b7b51e9f774cf691b9b60,
  0x3cb8af848d87b330d079836e9c98fa17a485661b84a6d6a41963683ec781323944a5cfb8642690b81461e78bcd04fcaaa816257eec7d818490c343136847a87d160, 0xcacc694e6ab074f59807dbcf1ced442ffbe1714cbb692d69b77b8419610d56c73968817b2b4e3b6581bfbd65b5c77227488f31c7ddc8b59ace76aff29e4f953bbf, 0x251b08af856542b700a60247e80a53881041bf169f3ad947586324122f42dcdf9cf4d259b39b295d90e85102b5b82a1d29ae2f202f1358039769678c95ae52fd27,
  0x5ef33aeddeb867ba78c203bb4a697372b02c1ac972c69f7b13800c5cfd3547ebe24db9d1a463a838bd6f2481e7f69bde81d93a0bce72fca10eb23bccfc26c6242, 0xd3b8c40b333f72ef4496a27848ca46640768e9085022e01e0de01c427f72e729a1cc344ee4db17a9c8177dcb169a1bff8da06711abf90fb2894d8dff399c3bc2, 0x199f83f4db7645573a1825b09a173b3a53682b72754aeedea0701b691677b46ebdede8aac07abc8eb057bf7e4399c9bfda7a78709d285b726049bc27ef1e9e3f,
  0x2aebcdcf1c39b5b4d4a57f92324c0ea7ce42f8e2079f3dd488500c29983576dfe5823f50cae58ed8e3a558ea157784cedb4db3628352d0a9ecbc27cb03d9817, 0x3dee9516c754a4f13b7b10a629694fef366aaa4a735da58d354be477c9a78b5f3335b4d1d4ad5dca5256354cf59bc465787d5047d4cb97611a0cf8a7a6d330, 0x4c9d3bc94ee8cacdb22ec6a504eed45cbc7b2026a699aa43fc504152217abfcc1e480685fb2b06e0f75f36dfd730b1539db1b78da971c71b0582457ce5830,
  0x50d443cc06292d7094a637e833e0c9b63ca0c564f788edecba8f55fe7ab001fcd7e9e6bf195929d7ab7e9f1269d2cdcd59121348a9f7fb2a0dfc6018a5ac, 0x484d0319435896185f916b8710bceb998e23af2dfbd9533007e93d6c16037e40a1eb6b6614ff6cc6b2ae40a84feebaac7bda305267bdab844b4d045ed4c, 0x3679550406d41e0e65035f989f9c568a532647b3ed95366909362b493e62f85ca859f26a7095f6d0eab726c000a10ae82ac72c3451985a3c9c0f4286f8,
  0x22515484c14428a77ae05d95dcae423d58f4957160e8d103d6081dd42681fa62a16c1592a25a997ed574fcaf6cc76769425232928dd313b4ec019bdf8, 0x11edc73b838b6ccc5672fde0a4108633c99f9bd70b8e84ea1b6b1f28d083d9f40b1878db29126438265102693e441d37488e7e2bd4bcff8a9f09317c, 0x7b2223d69358ee7f2ec3fbfa969aabb4dee3f09028b3f8f26857e69117fec59dc451e7d3100e967aa663d1253b2e90a9a6e302abf2e444f802485c,
  0x2af8d3a6398d0cc850c6c85eb7c76836c2633941f44838006aaa88ce1b964aaefcdc78a4e781dcdd06aad3b2b97833b5d6dc468ab18d24e95afd0, 0xc0c441633fcce61e82dc5c79a1651bdf8959a7581b8514362985d497e9b08ac4f6dbb8c3fad553fa09a7a8f643152f0934827d7d5b081acc8d0, 0x2ad474a88823435b3238647272f19773af05b7e6d3a29a8b5b631d72a7a3210ca25b14fdc124d0ac142c7a0e782458733b294f26609fba0fda,
  0x76c8d5dcf4db9ea606bf467ee3055abf0a855a44b80afe414be9aea1089a7c0ac9083bebdbf676ab017dc1be6b3436e74b566c2179714bca, 0xfc6424d2653c91da6646daed7101c6a70958a1d3a6dbd620d1eeacac44432c14fe109916a00773537290d541935adb25ca664e50aa6f3c, 0x192458756d64875032d09d5b5df018f2e1349170e64629a74ef429df107572a84349bd1bfa88d572e0b24a5966f9c7a8a641bccb8693c,
  0x1d52c4fe23dc004ddd22cd94d6f1c12b1c65735331dd3b759ea8c2de8d2b2a5ce6960059f39e79ddf9260c782313a937497b9167b6a, 0x184d83f4cbe5899a14c2248136d76fbccf3bada5f36b7646ec79f7f4cd79f0ce693aaa047605905d9244538c191b66af5e6ee727a, 0xdd1e59201cc30a76215fec92b01b74ed5315ef90f3890006cc4e4189e0d046bce32c47fdf853e86064013c6b0ea46a464a1990,
  0x52b2b3a7941d44c22034be1fa818472a1f9bb4760c571b028f83c916ee8d1829a1c96d3d7621dfa6151e402412da88d3d490, 0x1350fb16024f412a7092c12234e4fc59df467a560ed55a6c00d70befbda3fba9bf535bd328f9cadd8419ed4ee50692d14c, 0x2a4a2b27827770e928465247f36401397828f2484d84ea2ed5b5935c76c5930195fb766a7c2780793538b3d620c8eec,
  0x320ceb744aa882aaec2dff2b50d8c98a528f8109aa2003613211ac39b90ea97ffa62393116ee10e0d08f29976958, 0x1ce6e7261e45a0a70c3aefb6159c863a19c1a379e4e4801dad7773e4e7314cf8bc017a084e3936e63b0c8ee58, 0x720ba7d078ad64572196b517e2c44130c58c1e0a3ad42a625c796ca1d8bceb5d8baaedbfb6a245120057c,
  0xa10f37f99e0bc46d848cd5407494d17ddb0d50f2e7753889df7b04c0e51d3cbef6d74529f7a48935c, 0x3ffdf2cfbb108d0928ae3ae1ade425ecd97d1539cf28335141f7cb5a854e168972cc895ad0770, 0x519501c2bfe1cca19b32c2ad28652c35672d8155f3c8e5b133f2f77bff1ffbd540aee670,
  0xcb1e310836f422dca7fc60e57f225d4e352af568fd7ee142e3a8b5b3884a544889, 0x1c931e844871732f828d4d339bea3f4bc177f384a63f8724e8aade2fd261, 0xffffffffeb91b5696143e62508b8c20ec4bfc4e2646a3ed8b5e,
  0x32c78f21da0f291493551b3248b38680448f8c6de, 0x3fffffffffffffffffffffff99, 0x1]

private theorem eulerianCoefficients_eq : descentCoeffs 102 = eulerianCoefficients := by
  decide +kernel

private theorem upper : upperOK (descentCoeffs 102) first gaps = true := by
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

private theorem lower (i : Fin (lastRepresentative 103 - 2)) :
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

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 103) :
    StrictNegativeInterlacing (originalQuotient 103 k) (eulerian 102) 100 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N103
