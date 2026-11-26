import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentPackedData.C127L088.N086

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N086

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L088.N086 LongCycleBounds.DescentNecklace.Packed.C127L088.N086.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L088.N086 LongCycleBounds.DescentNecklace.Packed.C127L088.N086.rows

private theorem actual : RepresentativeChecks 86 previousNodes rows :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L088.N086 LongCycleBounds.DescentNecklace.Packed.C127L088.N086.dataChecks

private def first : LongCycleFinite.Dyadic := ⟨-38685626227668133590597632, 0⟩

private def gaps : List Window := [
  ⟨⟨-38684371849071121341087744, 0⟩, ⟨-929027195928576, 0⟩⟩,
  ⟨⟨-927925536817152, 0⟩, ⟨-41525444608, 0⟩⟩,
  ⟨⟨-41488351232, 0⟩, ⟨-169613824, 0⟩⟩,
  ⟨⟨-167721984, 0⟩, ⟨-5006560, 0⟩⟩,
  ⟨⟨-4998640, 0⟩, ⟨-434332, 0⟩⟩,
  ⟨⟨-434099, 0⟩, ⟨-143161, 1⟩⟩,
  ⟨⟨-143123, 1⟩, ⟨-285809, 4⟩⟩,
  ⟨⟨-142881, 3⟩, ⟨-23685, 2⟩⟩,
  ⟨⟨-189459, 5⟩, ⟨-307709, 7⟩⟩,
  ⟨⟨-76921, 5⟩, ⟨-145095, 7⟩⟩,
  ⟨⟨-290171, 8⟩, ⟨-306625, 9⟩⟩,
  ⟨⟨-306609, 9⟩, ⟨-353937, 10⟩⟩,
  ⟨⟨-176961, 9⟩, ⟨-438161, 11⟩⟩,
  ⟨⟨-438145, 11⟩, ⟨-286937, 11⟩⟩,
  ⟨⟨-286927, 11⟩, ⟨-196757, 11⟩⟩,
  ⟨⟨-393503, 12⟩, ⟨-280305, 12⟩⟩,
  ⟨⟨-140149, 11⟩, ⟨-412229, 13⟩⟩,
  ⟨⟨-412219, 13⟩, ⟨-311357, 13⟩⟩,
  ⟨⟨-155675, 12⟩, ⟨-481179, 14⟩⟩,
  ⟨⟨-240585, 13⟩, ⟨-379139, 14⟩⟩,
  ⟨⟨-94783, 12⟩, ⟨-75951, 12⟩⟩,
  ⟨⟨-151899, 13⟩, ⟨-247001, 14⟩⟩,
  ⟨⟨-493995, 15⟩, ⟨-203383, 14⟩⟩,
  ⟨⟨-50845, 12⟩, ⟨-338657, 15⟩⟩,
  ⟨⟨-84663, 13⟩, ⟨-142349, 14⟩⟩,
  ⟨⟨-142347, 14⟩, ⟨-120693, 14⟩⟩,
  ⟨⟨-241383, 15⟩, ⟨-206201, 15⟩⟩,
  ⟨⟨-412397, 16⟩, ⟨-354623, 16⟩⟩,
  ⟨⟨-354619, 16⟩, ⟨-306717, 16⟩⟩,
  ⟨⟨-153357, 15⟩, ⟨-266645, 16⟩⟩,
  ⟨⟨-133321, 15⟩, ⟨-116427, 15⟩⟩,
  ⟨⟨-465703, 17⟩, ⟨-408293, 17⟩⟩,
  ⟨⟨-408289, 17⟩, ⟨-359187, 17⟩⟩,
  ⟨⟨-22449, 13⟩, ⟨-316929, 17⟩⟩,
  ⟨⟨-316925, 17⟩, ⟨-140177, 16⟩⟩,
  ⟨⟨-280351, 17⟩, ⟨-248535, 17⟩⟩,
  ⟨⟨-497065, 18⟩, ⟨-110359, 16⟩⟩,
  ⟨⟨-55179, 15⟩, ⟨-392591, 18⟩⟩,
  ⟨⟨-392587, 18⟩, ⟨-10923, 13⟩⟩,
  ⟨⟨-349533, 18⟩, ⟨-155721, 17⟩⟩,
  ⟨⟨-311439, 18⟩, ⟨-138815, 17⟩⟩,
  ⟨⟨-277627, 18⟩, ⟨-247525, 18⟩⟩,
  ⟨⟨-247523, 18⟩, ⟨-441303, 19⟩⟩,
  ⟨⟨-441299, 19⟩, ⟨-393209, 19⟩⟩,
  ⟨⟨-393205, 19⟩, ⟨-350085, 19⟩⟩,
  ⟨⟨-175041, 18⟩, ⟨-77837, 17⟩⟩,
  ⟨⟨-311345, 19⟩, ⟨-276501, 19⟩⟩,
  ⟨⟨-138249, 18⟩, ⟨-490239, 20⟩⟩,
  ⟨⟨-245117, 19⟩, ⟨-216831, 19⟩⟩,
  ⟨⟨-216829, 19⟩, ⟨-382643, 20⟩⟩,
  ⟨⟨-382639, 20⟩, ⟨-336623, 20⟩⟩,
  ⟨⟨-84155, 18⟩, ⟨-147561, 19⟩⟩,
  ⟨⟨-147559, 19⟩, ⟨-257721, 20⟩⟩,
  ⟨⟨-128859, 19⟩, ⟨-112025, 19⟩⟩,
  ⟨⟨-14003, 16⟩, ⟨-387567, 21⟩⟩,
  ⟨⟨-193781, 20⟩, ⟨-83317, 19⟩⟩,
  ⟨⟨-20829, 17⟩, ⟨-142345, 20⟩⟩,
  ⟨⟨-142343, 20⟩, ⟨-120689, 20⟩⟩,
  ⟨⟨-241375, 21⟩, ⟨-405839, 22⟩⟩,
  ⟨⟨-202917, 21⟩, ⟨-10559, 17⟩⟩,
  ⟨⟨-337883, 22⟩, ⟨-139109, 21⟩⟩,
  ⟨⟨-278213, 22⟩, ⟨-113101, 21⟩⟩,
  ⟨⟨-452397, 23⟩, ⟨-362507, 23⟩⟩,
  ⟨⟨-362501, 23⟩, ⟨-285633, 23⟩⟩,
  ⟨⟨-71407, 21⟩, ⟨-441421, 24⟩⟩,
  ⟨⟨-220707, 23⟩, ⟨-333407, 24⟩⟩,
  ⟨⟨-333401, 24⟩, ⟨-245163, 24⟩⟩,
  ⟨⟨-122579, 23⟩, ⟨-87317, 23⟩⟩,
  ⟨⟨-87315, 23⟩, ⟨-239501, 25⟩⟩,
  ⟨⟨-239495, 25⟩, ⟨-78423, 24⟩⟩,
  ⟨⟨-313683, 26⟩, ⟨-388337, 27⟩⟩,
  ⟨⟨-194163, 26⟩, ⟨-112063, 26⟩⟩,
  ⟨⟨-448237, 28⟩, ⟨-473641, 29⟩⟩,
  ⟨⟨-473623, 29⟩, ⟨-446689, 30⟩⟩,
  ⟨⟨-223335, 29⟩, ⟨-22669, 27⟩⟩,
  ⟨⟨-362687, 31⟩, ⟨-480951, 33⟩⟩,
  ⟨⟨-480925, 33⟩, ⟨-480155, 35⟩⟩,
  ⟨⟨-240063, 34⟩, ⟨-158289, 36⟩⟩,
  ⟨⟨-79139, 35⟩, ⟨-109909, 39⟩⟩,
  ⟨⟨-109901, 39⟩, ⟨-419149, 46⟩⟩,
  ⟨⟨-104779, 44⟩, ⟨-217069, 53⟩⟩,
  ⟨⟨-217051, 53⟩, ⟨-39741, 65⟩⟩,
  ⟨⟨-158949, 67⟩, ⟨-262149, 103⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private def eulerianCoefficients : List ℤ := [
  0x1, 0x1fffffffffffffffffffaa, 0x698d5ba660fda278add272ed7c87a487fa,
  0x3ffffffdc8a83361b68f7cb759b4d64382a6ebd8e1a, 0x292e3154685595b7971384e151037f47da456ee75f7ef5cbbd, 0xd319d9f47543d4256c40fe3b4ef5a10a9c670487abd755703fe3568,
  0x62b219549eba8a8b9fac7e3d8758ae61348761690c5be6625d3b956c1ad8, 0x7fded76aaf41587ebc90ee154397d90368e64811f340f01b023f5714c04ac108, 0x2b5a48bdd924cd862c2d60b1cf458ac6e9d00a958db4f9b54381d7bf74587200e1da,
  0x5172eb3dc8d5ad2a412b8a51051306d4ce54e9c0471628182e9053b4d70636bf4765abc, 0x409d5e03a8013d8f4ff258a00fc4101b63bebdcfa674eaadf65fe5d236b2421a521e7884cc, 0x19035e494cd79ce2090f98279bd6f3aaecfa3d41d6e0592546f18b3a4c1dc412c635f2b96353c,
  0x543feaf06b2838e8103baa937bc967e98b524b841aee379e48ddf11dabe1bcabd7a5289ccc900fa, 0xa7ab41e4a22cc97de4015bd4e84cc2cbbc6cd9b0b7361fec9fe74100b677eec1f26e8433acf7de9c8, 0xd25dd40774123aebca3dc76ecbdd9206fe838e89cadba06da6b70b1865d87acebe853b203b51a2f1e18,
  0xaf318876709f57fd85e12fe449256896a68368a10bbd91413882843e59d6f98cef2a3d531e2967f891d28, 0x64f524a58ffd4a5b54dab95cdc2cdc49ca6686aa6f0979135b43b3ff2753653bb9cec5e427ce962eb3486c9, 0x29a67f117a22a0f4f0b514f1d0cd6b76df9edf063b490c3e2e0e6d174893e5ec2d20f61f08c935898a95c5852,
  0xca733dca1e9f8b35962561209a592d00fec755118101c4265383e4529c97b08727096bd1a9a95a5aba7f86c472, 0x2e5ee421bd635cc79bdd4778fcdd76c09f1e314ed6fb27cbd8d27cd122be56fd16e9a245f1a296922ac1acc25a22, 0x82b49db3de10cf6eef4225f2c48c57ab2585ee833ed0acc0fb4f2b4e21c07957e0aae95fd9275de03fca0b465f19d,
  0x1203926c2e3618e9e5241db443fc4d3b4634171956cf48d8b2f9390a69c0dc4335adc52dbe5bcd818c3a62ecae90f20, 0x1f8864f480ae787e26eb92ca6bd222cc26d4459928f8deafd814fd9cfbd84f5dab6f1886fbfffc355b55882e65d26ee0, 0x2c5f232f89bb2613f97143788b44fc7453b6d96a9a88de369f4879fcfb8743ba4f9a13a8b3fc679f1aea3389866774da0,
  0x32be9dc4c6fa8a09493f4007b21e9bf6e23f91b6aa6839c7753c413026a57645247695ca9707a7128540eed98b54392b98, 0x2f9defed6b71e2944b9287baf9979026b7fa5df91c864f3c6fb6351c4c95f905d295c536725292fb1acc637825ed6dfb950, 0x24f85cd50dfa9ff47c17d3288f06eb978bb26f40158c95b4df73ec1f2932392924a8320e802a10df1f9bbae31513f24ba690,
  0x17ecc13a672ea44f162e478bcd15aca91b9f2a2edd40076eea85daacb0546c073cbb3f91df2ad9ffeab0ff994185590570850, 0xcfd11ef90515db229390b90ab324728e7a7ed0c3179b70d5055001db6e543760c94e128c084a66fbca6134ca2124d50675e58, 0x5f301e078d643332be37cd943e82191ff31b77afc009e869f6a6d9ed3f92cbcac1bedcd8b4fcfaee5f03952e7aef50f788c220,
  0x24f86b2ee82054829a22699872d1757e0f83039878c7a17c5908cd6fc8d9f52c829593c8cee023d7b52eb54805b603ddc6af260, 0xc3ad3c1e1f4cd75358db58be4aa13f51fad288164bf73bcc3ea4ef5074f42e1d08c778e934d100209685256aa8bcb1ac84e5da0, 0x3758a52a6c6e2e7349b0e430e5fe22f7850081754913aca21a29f1b8f403d3fee9bb81f7b2bb7c458cecb41ce1ec884d8bd45382,
  0xd6e4dc0db08e33253a8ce451cb2b0364d741dc2d3d59fd709439d5be5b23b83215a77a20c3cfcb981e0041b8e28231c0acb258b4, 0x2cdfe46fc82a664a0c759aaf7c39aaddb871c6d9d5f2e8bd8ca05ae4a884f1edb1c12fed7aa0d8ee07c31fbe52ebfc8495ab0e994, 0x815a6fc895810f953710e44a74a57d3af7fe5a519bf355c3fd4b1b4c179856645a6fb96164baa5287e683f8ea86119b244fee8314,
  0x14266af27ee283e901d65f807a192ac2137970d087ddca67feb3e5ba3de2f23762a792bf17f9a3e9933dd41193608c77129342365a, 0x2b8192f40312b566d18eaf71925c44da10be2f0e6c4dd844b18df825a949bb856191bbaeefb844735dbc191ac234cf1cb2522ff0b0, 0x517fcb3ecb73e2615ded241451638ccbb337620ae0f805504d01d87afe6482fa221a80d00df676c55b65e331807a788fdbeb9f65d0,
  0x84a0123ba5cc56f1c95f54ab87b941c056f4357ed0705ed21c54c7ae88cf058c3ab79c5852ae5e49e20372b1f18b3142bd19f89570, 0xbbaa73e0b97fea51ed702f85f6e629f48cc824dcc0ddd7ebab155ff404f15452e9eadc35e75c511b3516141bbc34cc8081deeec53c, 0xe70f3bfcbd91cd468af7b23fa7d1a27c9380176d45fbd45b19033287eec24f9a433cc4035a982a004f6c6dbfc9fef52b37468f9268,
  0xf7a355c7167c7caefefe54241c12a2a3b17a6e175f13d988f924db3fd6f4e0804f28ed1ecb1d51b3af8ee8ed44b01fcdc15fcf3d48, 0xe70f3bfcbd91cd468af7b23fa7d1a27c9380176d45fbd45b19033287eec24f9a433cc4035a982a004f6c6dbfc9fef52b37468f9268, 0xbbaa73e0b97fea51ed702f85f6e629f48cc824dcc0ddd7ebab155ff404f15452e9eadc35e75c511b3516141bbc34cc8081deeec53c,
  0x84a0123ba5cc56f1c95f54ab87b941c056f4357ed0705ed21c54c7ae88cf058c3ab79c5852ae5e49e20372b1f18b3142bd19f89570, 0x517fcb3ecb73e2615ded241451638ccbb337620ae0f805504d01d87afe6482fa221a80d00df676c55b65e331807a788fdbeb9f65d0, 0x2b8192f40312b566d18eaf71925c44da10be2f0e6c4dd844b18df825a949bb856191bbaeefb844735dbc191ac234cf1cb2522ff0b0,
  0x14266af27ee283e901d65f807a192ac2137970d087ddca67feb3e5ba3de2f23762a792bf17f9a3e9933dd41193608c77129342365a, 0x815a6fc895810f953710e44a74a57d3af7fe5a519bf355c3fd4b1b4c179856645a6fb96164baa5287e683f8ea86119b244fee8314, 0x2cdfe46fc82a664a0c759aaf7c39aaddb871c6d9d5f2e8bd8ca05ae4a884f1edb1c12fed7aa0d8ee07c31fbe52ebfc8495ab0e994,
  0xd6e4dc0db08e33253a8ce451cb2b0364d741dc2d3d59fd709439d5be5b23b83215a77a20c3cfcb981e0041b8e28231c0acb258b4, 0x3758a52a6c6e2e7349b0e430e5fe22f7850081754913aca21a29f1b8f403d3fee9bb81f7b2bb7c458cecb41ce1ec884d8bd45382, 0xc3ad3c1e1f4cd75358db58be4aa13f51fad288164bf73bcc3ea4ef5074f42e1d08c778e934d100209685256aa8bcb1ac84e5da0,
  0x24f86b2ee82054829a22699872d1757e0f83039878c7a17c5908cd6fc8d9f52c829593c8cee023d7b52eb54805b603ddc6af260, 0x5f301e078d643332be37cd943e82191ff31b77afc009e869f6a6d9ed3f92cbcac1bedcd8b4fcfaee5f03952e7aef50f788c220, 0xcfd11ef90515db229390b90ab324728e7a7ed0c3179b70d5055001db6e543760c94e128c084a66fbca6134ca2124d50675e58,
  0x17ecc13a672ea44f162e478bcd15aca91b9f2a2edd40076eea85daacb0546c073cbb3f91df2ad9ffeab0ff994185590570850, 0x24f85cd50dfa9ff47c17d3288f06eb978bb26f40158c95b4df73ec1f2932392924a8320e802a10df1f9bbae31513f24ba690, 0x2f9defed6b71e2944b9287baf9979026b7fa5df91c864f3c6fb6351c4c95f905d295c536725292fb1acc637825ed6dfb950,
  0x32be9dc4c6fa8a09493f4007b21e9bf6e23f91b6aa6839c7753c413026a57645247695ca9707a7128540eed98b54392b98, 0x2c5f232f89bb2613f97143788b44fc7453b6d96a9a88de369f4879fcfb8743ba4f9a13a8b3fc679f1aea3389866774da0, 0x1f8864f480ae787e26eb92ca6bd222cc26d4459928f8deafd814fd9cfbd84f5dab6f1886fbfffc355b55882e65d26ee0,
  0x1203926c2e3618e9e5241db443fc4d3b4634171956cf48d8b2f9390a69c0dc4335adc52dbe5bcd818c3a62ecae90f20, 0x82b49db3de10cf6eef4225f2c48c57ab2585ee833ed0acc0fb4f2b4e21c07957e0aae95fd9275de03fca0b465f19d, 0x2e5ee421bd635cc79bdd4778fcdd76c09f1e314ed6fb27cbd8d27cd122be56fd16e9a245f1a296922ac1acc25a22,
  0xca733dca1e9f8b35962561209a592d00fec755118101c4265383e4529c97b08727096bd1a9a95a5aba7f86c472, 0x29a67f117a22a0f4f0b514f1d0cd6b76df9edf063b490c3e2e0e6d174893e5ec2d20f61f08c935898a95c5852, 0x64f524a58ffd4a5b54dab95cdc2cdc49ca6686aa6f0979135b43b3ff2753653bb9cec5e427ce962eb3486c9,
  0xaf318876709f57fd85e12fe449256896a68368a10bbd91413882843e59d6f98cef2a3d531e2967f891d28, 0xd25dd40774123aebca3dc76ecbdd9206fe838e89cadba06da6b70b1865d87acebe853b203b51a2f1e18, 0xa7ab41e4a22cc97de4015bd4e84cc2cbbc6cd9b0b7361fec9fe74100b677eec1f26e8433acf7de9c8,
  0x543feaf06b2838e8103baa937bc967e98b524b841aee379e48ddf11dabe1bcabd7a5289ccc900fa, 0x19035e494cd79ce2090f98279bd6f3aaecfa3d41d6e0592546f18b3a4c1dc412c635f2b96353c, 0x409d5e03a8013d8f4ff258a00fc4101b63bebdcfa674eaadf65fe5d236b2421a521e7884cc,
  0x5172eb3dc8d5ad2a412b8a51051306d4ce54e9c0471628182e9053b4d70636bf4765abc, 0x2b5a48bdd924cd862c2d60b1cf458ac6e9d00a958db4f9b54381d7bf74587200e1da, 0x7fded76aaf41587ebc90ee154397d90368e64811f340f01b023f5714c04ac108,
  0x62b219549eba8a8b9fac7e3d8758ae61348761690c5be6625d3b956c1ad8, 0xd319d9f47543d4256c40fe3b4ef5a10a9c670487abd755703fe3568, 0x292e3154685595b7971384e151037f47da456ee75f7ef5cbbd,
  0x3ffffffdc8a83361b68f7cb759b4d64382a6ebd8e1a, 0x698d5ba660fda278add272ed7c87a487fa, 0x1fffffffffffffffffffaa,
  0x1]

private theorem eulerianCoefficients_eq : descentCoeffs 85 = eulerianCoefficients := by
  decide +kernel

private theorem upper : upperOK (descentCoeffs 85) first gaps = true := by
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

private theorem lower (i : Fin (lastRepresentative 86 - 2)) :
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

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 86) :
    StrictNegativeInterlacing (originalQuotient 86 k) (eulerian 85) 83 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N086
