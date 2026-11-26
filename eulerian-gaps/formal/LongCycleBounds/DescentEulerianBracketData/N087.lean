import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentPackedData.C127L088.N087

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N087

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L088.N087 LongCycleBounds.DescentNecklace.Packed.C127L088.N087.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L088.N087 LongCycleBounds.DescentNecklace.Packed.C127L088.N087.rows

private theorem actual : RepresentativeChecks 87 previousNodes rows :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L088.N087 LongCycleBounds.DescentNecklace.Packed.C127L088.N087.dataChecks

private def first : LongCycleFinite.Dyadic := ⟨-77371252455336267181195264, 0⟩

private def gaps : List Window := [
  ⟨⟨-77368743698142242682175488, 0⟩, ⟨-1394666075324416, 0⟩⟩,
  ⟨⟨-1392462757101568, 0⟩, ⟨-55341744128, 0⟩⟩,
  ⟨⟨-55286300672, 0⟩, ⟨-211560448, 0⟩⟩,
  ⟨⟨-209036800, 0⟩, ⟨-6021520, 0⟩⟩,
  ⟨⟨-6011520, 0⟩, ⟨-508107, 0⟩⟩,
  ⟨⟨-507827, 0⟩, ⟨-328251, 2⟩⟩,
  ⟨⟨-328161, 2⟩, ⟨-322711, 4⟩⟩,
  ⟨⟨-161329, 3⟩, ⟨-422831, 6⟩⟩,
  ⟨⟨-422783, 6⟩, ⟨-340065, 7⟩⟩,
  ⟨⟨-85009, 5⟩, ⟨-318209, 8⟩⟩,
  ⟨⟨-79547, 6⟩, ⟨-334069, 9⟩⟩,
  ⟨⟨-334051, 9⟩, ⟨-191763, 9⟩⟩,
  ⟨⟨-383509, 10⟩, ⟨-472607, 11⟩⟩,
  ⟨⟨-236295, 10⟩, ⟨-154145, 10⟩⟩,
  ⟨⟨-38535, 8⟩, ⟨-421381, 12⟩⟩,
  ⟨⟨-421369, 12⟩, ⟨-299283, 12⟩⟩,
  ⟨⟨-299275, 12⟩, ⟨-439031, 13⟩⟩,
  ⟨⟨-439021, 13⟩, ⟨-330877, 13⟩⟩,
  ⟨⟨-330869, 13⟩, ⟨-510373, 14⟩⟩,
  ⟨⟨-510363, 14⟩, ⟨-100369, 12⟩⟩,
  ⟨⟨-100367, 12⟩, ⟨-160621, 13⟩⟩,
  ⟨⟨-80309, 12⟩, ⟨-65215, 12⟩⟩,
  ⟨⟨-32607, 11⟩, ⟨-429137, 15⟩⟩,
  ⟨⟨-214565, 14⟩, ⟨-178483, 14⟩⟩,
  ⟨⟨-356961, 15⟩, ⟨-299869, 15⟩⟩,
  ⟨⟨-299865, 15⟩, ⟨-508189, 16⟩⟩,
  ⟨⟨-508183, 16⟩, ⟨-216955, 15⟩⟩,
  ⟨⟨-27119, 12⟩, ⟨-93247, 14⟩⟩,
  ⟨⟨-372983, 16⟩, ⟨-322529, 16⟩⟩,
  ⟨⟨-322525, 16⟩, ⟨-280357, 16⟩⟩,
  ⟨⟨-140177, 15⟩, ⟨-244823, 16⟩⟩,
  ⟨⟨-489641, 17⟩, ⟨-107331, 15⟩⟩,
  ⟨⟨-53665, 14⟩, ⟨-47221, 14⟩⟩,
  ⟨⟨-94441, 15⟩, ⟨-20839, 13⟩⟩,
  ⟨⟨-333421, 17⟩, ⟨-295071, 17⟩⟩,
  ⟨⟨-73767, 15⟩, ⟨-523437, 18⟩⟩,
  ⟨⟨-65429, 15⟩, ⟨-465153, 18⟩⟩,
  ⟨⟨-116287, 16⟩, ⟨-413995, 18⟩⟩,
  ⟨⟨-413991, 18⟩, ⟨-368915, 18⟩⟩,
  ⟨⟨-23057, 14⟩, ⟨-164521, 17⟩⟩,
  ⟨⟨-329039, 18⟩, ⟨-73413, 16⟩⟩,
  ⟨⟨-293649, 18⟩, ⟨-262145, 18⟩⟩,
  ⟨⟨-524285, 19⟩, ⟨-468041, 19⟩⟩,
  ⟨⟨-117009, 17⟩, ⟨-417701, 19⟩⟩,
  ⟨⟨-417697, 19⟩, ⟨-372551, 19⟩⟩,
  ⟨⟨-372547, 19⟩, ⟨-331985, 19⟩⟩,
  ⟨⟨-165991, 18⟩, ⟨-147737, 18⟩⟩,
  ⟨⟨-295471, 19⟩, ⟨-131287, 18⟩⟩,
  ⟨⟨-262571, 19⟩, ⟨-465789, 20⟩⟩,
  ⟨⟨-58223, 17⟩, ⟨-206103, 19⟩⟩,
  ⟨⟨-412201, 20⟩, ⟨-363823, 20⟩⟩,
  ⟨⟨-363819, 20⟩, ⟨-80033, 18⟩⟩,
  ⟨⟨-2501, 13⟩, ⟨-280691, 20⟩⟩,
  ⟨⟨-17543, 16⟩, ⟨-122559, 19⟩⟩,
  ⟨⟨-490231, 21⟩, ⟨-426137, 21⟩⟩,
  ⟨⟨-426133, 21⟩, ⟨-184243, 20⟩⟩,
  ⟨⟨-368481, 21⟩, ⟨-316749, 21⟩⟩,
  ⟨⟨-316745, 21⟩, ⟨-270451, 21⟩⟩,
  ⟨⟨-270447, 21⟩, ⟨-458337, 22⟩⟩,
  ⟨⟨-458331, 22⟩, ⟨-385025, 22⟩⟩,
  ⟨⟨-96255, 20⟩, ⟨-160137, 21⟩⟩,
  ⟨⟨-320269, 22⟩, ⟨-263437, 22⟩⟩,
  ⟨⟨-263433, 22⟩, ⟨-427847, 23⟩⟩,
  ⟨⟨-427841, 23⟩, ⟨-171169, 22⟩⟩,
  ⟨⟨-342333, 23⟩, ⟨-269297, 23⟩⟩,
  ⟨⟨-269293, 23⟩, ⟨-207695, 23⟩⟩,
  ⟨⟨-415383, 24⟩, ⟨-156531, 23⟩⟩,
  ⟨⟨-313055, 24⟩, ⟨-459241, 25⟩⟩,
  ⟨⟨-14351, 20⟩, ⟨-163089, 24⟩⟩,
  ⟨⟨-163085, 24⟩, ⟨-222911, 25⟩⟩,
  ⟨⟨-445811, 26⟩, ⟨-145409, 25⟩⟩,
  ⟨⟨-145405, 25⟩, ⟨-358365, 27⟩⟩,
  ⟨⟨-179177, 26⟩, ⟨-51427, 25⟩⟩,
  ⟨⟨-205701, 27⟩, ⟨-431927, 29⟩⟩,
  ⟨⟨-431911, 29⟩, ⟨-202093, 29⟩⟩,
  ⟨⟨-50521, 27⟩, ⟨-325063, 31⟩⟩,
  ⟨⟨-325047, 31⟩, ⟨-425935, 33⟩⟩,
  ⟨⟨-53239, 30⟩, ⟨-418807, 35⟩⟩,
  ⟨⟨-418781, 35⟩, ⟨-270639, 37⟩⟩,
  ⟨⟨-67655, 35⟩, ⟨-365635, 41⟩⟩,
  ⟨⟨-45701, 38⟩, ⟨-334953, 46⟩⟩,
  ⟨⟨-167463, 45⟩, ⟨-81379, 52⟩⟩,
  ⟨⟨-20343, 50⟩, ⟨-423897, 69⟩⟩,
  ⟨⟨-423857, 69⟩, ⟨-262165, 104⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private def eulerianCoefficients : List ℤ := [
  0x1, 0x3fffffffffffffffffffa9, 0x13ca812f32303676a097758c87596ed7bb6,
  0xfffffff9462e18f5f161adaf6c870d3e009b54e4e76, 0xcde6f7ee09abe13a5168ed2e3470a8130225448274f3847f05, 0x4f29bec3499524911cf776236aa7670615ec5dc2d887f54143bab73d,
  0x2b2e2d0d198e01424827290f3aa954f7494e8b7e26d29a7e537d255656c68, 0x3ff15304b4b27bf86a59db6e511bb8c7917317656a97251342a557e091eb250e8, 0x18653849244cc9fa08435da68d3ec7942575a556bf0d4e52887cb45079f6e98cec11a,
  0x32f4dd2e7e9fdc4c3a168018b8a73c2fbec965ab5b69787e389f825eeaf9e0d1d6e379ea, 0x2c845ec059d879c1ef81f5db1ae44cb8dbc063b427857beb808fc0d95f4a634a593e250a494, 0x12d574d184b3ee068fc81e1dabc5d530e9c1e6d2fcfe071cb62c56840dac5947725e84f8596694,
  0x44e79e776a141372229a62b78bc46694b7bae2b6a6635acce79c710c094772f6760aea81ffa0700a, 0x94363d47f6d017d1ca4b40948c27f15c5e6ae5f32b0a3accce16cd7cb70926d68428953682be34103a, 0xc82a796f81aae0c7c41bf1151d351253236b3f74c96659f6751b2b0b62b00ed43b5fd8c12026e42c83a8,
  0xb2d708d351b268e2fc32a20944ce0fcea58cd0698f31bfd91f16507f961aea2de497ac897d30a23ba32b28, 0x6e42efa4ef29d821ff521e2430afadb7fa256dfed68d6e000e4f2a41aa91a8133e020b0eb5ef74b87dfaec49, 0x308eb021b363e96438a9a6cf6b5c9a5bb9cb950bc1b106a01749ceb26dfffa4e4456609851ce0722654da689f1,
  0xfb791320a8cea810b23c7ce6f2c075fcc1f2e84270f1802e0768741c493b6ab33a57f16937ce8d8446473880a3e, 0x3d465fbceb1c7010733955ddf49b29dd3b10a056c60629242f84d451855da7ef9297824aec01b161115f0df74747e, 0xb78185ccc649ae2d1035de3bd3294bae4a4591c295dea2ffd7be2d047741b1b096c88e23d54f960802bf1d56780ea5,
  0x1ad7e7156a40868c4dbda59207b96455a7d00fdbcc8c33e7c613a00e3ed24cc95ecfa572fb206a7f7fd36cd33de9a59d, 0x31d4f5ba8488536fd13baa700bfd2554495e29d280999252f35c7ad44477292773db248d79d6eded16598c7dde02bbe20, 0x4a51459f7a43a8c501bdde54a170313ebb20834098e28c1f3519e1651b45211f8497748645fe9a7fc9d959d1b4a9f89020,
  0x5a08e108fa42cae758dc4263380a88d5edc99c553bb00018e1c1b366814d4b3328409acf6793162578ba2daf3840a7a0e98, 0x59781179b202c31531422ed1ab079568bedffe6d54f51686bc7771d675a921d7efe3a229bfc301a7754c9a8d13d4e4583558, 0x498c20e32cc59f07531e8c2443db3358cedbc9c2870cb733634252e73777e6d2cb36eeb13b1256eb5f9eb2af5c754ea69fff0,
  0x32638f8b4eca6267bf6a7adeffdc8673dd88a975c8277382c9e9f6196312503925ba72c89e14af6346fea35e8884f4a0f44bf0, 0x1cf6544970f40b0cd5bde12be2c20a1874226d34b7cd1d7742bc63c0fb72aabf9a904480e980230e81191ce39e99624cf6d9218, 0xe0bfc8339b3dbdc9d783daa957170c9da119bce4f8542fe61ca7a906b2c3fe70b81840378132e76d02365c7827e1eb3e90ac158,
  0x5c73d63c88ac8ef0243ee18fcc2249233b3bd925dc04f3b81a758db47b0e679a97638ea478699c5613d347ddb5f50133d6ddd0a0, 0x2067068ad7c88d127a38cfc789ff282854af76c88b71cb2b3ef5820d12c55970312711dd4b0c47b76abdad9fce51b10a364c5c6a0, 0x9b6d5f55da3d75395cbb1b5cfe1a2b79cd3973b69abebaab6b2d4d086ff366f7e1eccf9011c6c65652684960118fa69a546e68382,
  0x27ffbf6b99e5b268d0085590fc9953b0a31fda0b4a470666831a5d6e929f895a6d441020a20269c49a290a0488db42d3a4e2a511d2, 0x8dd040674db9a2258b25e0c07d02e2757f3243b5b479a49981ba863edb2612a2213c9da624060fe39712e2c9e366aa7d2a7a69f3cc, 0x1b21523a79e69891bc39cdeb6e26c2a6769e6f50df8d9c6d52a281f240e3e8587721329e01984a711d528842fa32aaeb7b84ec8f74c,
  0x47dc8125f29f0615f901096fa5228556517882862aa66ad0c478ae938bb890ffadcd558eed1dbf4e0d2f56d281b23bd82c6e52774ea, 0xa509648a2be222cdc75365273188367843679940e1501d81a1b81ce3cf96232665db4f28b2c2288d518c151560951a10d0662ca215a, 0x1492c384519229801c99e16463d7775beb7118c25c94615c1d05e681cc7f231d1d7d5cd07f1318edb27fca518efc8f334bf04e45a3b0,
  0x23af7929d9423425a7b56eda8826391f737d535bcfdf17ca929095f1da14cce9d56f8e13ff7b7e89c7183ea1e4543bd4d6ec511b0ab0, 0x35e30fd5b5803426913618d346ee2688ba2bef842457b89e7f7da83f715fd9807a039b5c80e91deea21d27d46a8b779a92c75ee870bc, 0x46e57635f7b567ddf9895b98fdeeda086cf23252bb624fcb5f2d4828320a4ce1e22640de06883125d55cab8a57391c2bade5c386b09c,
  0x514f0db7e15bf83984b74ac5018f293ee8299484b4ff9e09aa25bd831624876410da5184bfb013f13c23a3fcd141677afcfb387c74f8, 0x514f0db7e15bf83984b74ac5018f293ee8299484b4ff9e09aa25bd831624876410da5184bfb013f13c23a3fcd141677afcfb387c74f8, 0x46e57635f7b567ddf9895b98fdeeda086cf23252bb624fcb5f2d4828320a4ce1e22640de06883125d55cab8a57391c2bade5c386b09c,
  0x35e30fd5b5803426913618d346ee2688ba2bef842457b89e7f7da83f715fd9807a039b5c80e91deea21d27d46a8b779a92c75ee870bc, 0x23af7929d9423425a7b56eda8826391f737d535bcfdf17ca929095f1da14cce9d56f8e13ff7b7e89c7183ea1e4543bd4d6ec511b0ab0, 0x1492c384519229801c99e16463d7775beb7118c25c94615c1d05e681cc7f231d1d7d5cd07f1318edb27fca518efc8f334bf04e45a3b0,
  0xa509648a2be222cdc75365273188367843679940e1501d81a1b81ce3cf96232665db4f28b2c2288d518c151560951a10d0662ca215a, 0x47dc8125f29f0615f901096fa5228556517882862aa66ad0c478ae938bb890ffadcd558eed1dbf4e0d2f56d281b23bd82c6e52774ea, 0x1b21523a79e69891bc39cdeb6e26c2a6769e6f50df8d9c6d52a281f240e3e8587721329e01984a711d528842fa32aaeb7b84ec8f74c,
  0x8dd040674db9a2258b25e0c07d02e2757f3243b5b479a49981ba863edb2612a2213c9da624060fe39712e2c9e366aa7d2a7a69f3cc, 0x27ffbf6b99e5b268d0085590fc9953b0a31fda0b4a470666831a5d6e929f895a6d441020a20269c49a290a0488db42d3a4e2a511d2, 0x9b6d5f55da3d75395cbb1b5cfe1a2b79cd3973b69abebaab6b2d4d086ff366f7e1eccf9011c6c65652684960118fa69a546e68382,
  0x2067068ad7c88d127a38cfc789ff282854af76c88b71cb2b3ef5820d12c55970312711dd4b0c47b76abdad9fce51b10a364c5c6a0, 0x5c73d63c88ac8ef0243ee18fcc2249233b3bd925dc04f3b81a758db47b0e679a97638ea478699c5613d347ddb5f50133d6ddd0a0, 0xe0bfc8339b3dbdc9d783daa957170c9da119bce4f8542fe61ca7a906b2c3fe70b81840378132e76d02365c7827e1eb3e90ac158,
  0x1cf6544970f40b0cd5bde12be2c20a1874226d34b7cd1d7742bc63c0fb72aabf9a904480e980230e81191ce39e99624cf6d9218, 0x32638f8b4eca6267bf6a7adeffdc8673dd88a975c8277382c9e9f6196312503925ba72c89e14af6346fea35e8884f4a0f44bf0, 0x498c20e32cc59f07531e8c2443db3358cedbc9c2870cb733634252e73777e6d2cb36eeb13b1256eb5f9eb2af5c754ea69fff0,
  0x59781179b202c31531422ed1ab079568bedffe6d54f51686bc7771d675a921d7efe3a229bfc301a7754c9a8d13d4e4583558, 0x5a08e108fa42cae758dc4263380a88d5edc99c553bb00018e1c1b366814d4b3328409acf6793162578ba2daf3840a7a0e98, 0x4a51459f7a43a8c501bdde54a170313ebb20834098e28c1f3519e1651b45211f8497748645fe9a7fc9d959d1b4a9f89020,
  0x31d4f5ba8488536fd13baa700bfd2554495e29d280999252f35c7ad44477292773db248d79d6eded16598c7dde02bbe20, 0x1ad7e7156a40868c4dbda59207b96455a7d00fdbcc8c33e7c613a00e3ed24cc95ecfa572fb206a7f7fd36cd33de9a59d, 0xb78185ccc649ae2d1035de3bd3294bae4a4591c295dea2ffd7be2d047741b1b096c88e23d54f960802bf1d56780ea5,
  0x3d465fbceb1c7010733955ddf49b29dd3b10a056c60629242f84d451855da7ef9297824aec01b161115f0df74747e, 0xfb791320a8cea810b23c7ce6f2c075fcc1f2e84270f1802e0768741c493b6ab33a57f16937ce8d8446473880a3e, 0x308eb021b363e96438a9a6cf6b5c9a5bb9cb950bc1b106a01749ceb26dfffa4e4456609851ce0722654da689f1,
  0x6e42efa4ef29d821ff521e2430afadb7fa256dfed68d6e000e4f2a41aa91a8133e020b0eb5ef74b87dfaec49, 0xb2d708d351b268e2fc32a20944ce0fcea58cd0698f31bfd91f16507f961aea2de497ac897d30a23ba32b28, 0xc82a796f81aae0c7c41bf1151d351253236b3f74c96659f6751b2b0b62b00ed43b5fd8c12026e42c83a8,
  0x94363d47f6d017d1ca4b40948c27f15c5e6ae5f32b0a3accce16cd7cb70926d68428953682be34103a, 0x44e79e776a141372229a62b78bc46694b7bae2b6a6635acce79c710c094772f6760aea81ffa0700a, 0x12d574d184b3ee068fc81e1dabc5d530e9c1e6d2fcfe071cb62c56840dac5947725e84f8596694,
  0x2c845ec059d879c1ef81f5db1ae44cb8dbc063b427857beb808fc0d95f4a634a593e250a494, 0x32f4dd2e7e9fdc4c3a168018b8a73c2fbec965ab5b69787e389f825eeaf9e0d1d6e379ea, 0x18653849244cc9fa08435da68d3ec7942575a556bf0d4e52887cb45079f6e98cec11a,
  0x3ff15304b4b27bf86a59db6e511bb8c7917317656a97251342a557e091eb250e8, 0x2b2e2d0d198e01424827290f3aa954f7494e8b7e26d29a7e537d255656c68, 0x4f29bec3499524911cf776236aa7670615ec5dc2d887f54143bab73d,
  0xcde6f7ee09abe13a5168ed2e3470a8130225448274f3847f05, 0xfffffff9462e18f5f161adaf6c870d3e009b54e4e76, 0x13ca812f32303676a097758c87596ed7bb6,
  0x3fffffffffffffffffffa9, 0x1]

private theorem eulerianCoefficients_eq : descentCoeffs 86 = eulerianCoefficients := by
  decide +kernel

private theorem upper : upperOK (descentCoeffs 86) first gaps = true := by
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

private theorem lower (i : Fin (lastRepresentative 87 - 2)) :
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

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 87) :
    StrictNegativeInterlacing (originalQuotient 87 k) (eulerian 86) 84 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N087
