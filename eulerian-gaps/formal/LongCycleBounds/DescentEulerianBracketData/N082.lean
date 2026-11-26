import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentPackedData.C127L088.N082

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N082

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L088.N082 LongCycleBounds.DescentNecklace.Packed.C127L088.N082.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L088.N082 LongCycleBounds.DescentNecklace.Packed.C127L088.N082.rows

private theorem actual : RepresentativeChecks 82 previousNodes rows :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L088.N082 LongCycleBounds.DescentNecklace.Packed.C127L088.N082.dataChecks

private def first : LongCycleFinite.Dyadic := ⟨-2417851639229258349412352, 0⟩

private def gaps : List Window := [
  ⟨⟨-2417773240566945083817984, 0⟩, ⟨-205834160177152, 0⟩⟩,
  ⟨⟨-135466221305856, 0⟩, ⟨-13115293696, 0⟩⟩,
  ⟨⟨-13107200000, 0⟩, ⟨-68870656, 0⟩⟩,
  ⟨⟨-68259072, 0⟩, ⟨-2394552, 0⟩⟩,
  ⟨⟨-2391320, 0⟩, ⟨-463729, 1⟩⟩,
  ⟨⟨-231755, 0⟩, ⟨-331119, 3⟩⟩,
  ⟨⟨-331039, 3⟩, ⟨-175641, 4⟩⟩,
  ⟨⟨-351229, 5⟩, ⟨-488499, 7⟩⟩,
  ⟨⟨-488449, 7⟩, ⟨-412019, 8⟩⟩,
  ⟨⟨-102997, 6⟩, ⟨-50105, 6⟩⟩,
  ⟨⟨-25051, 5⟩, ⟨-434581, 10⟩⟩,
  ⟨⟨-3395, 3⟩, ⟨-256283, 10⟩⟩,
  ⟨⟨-512545, 11⟩, ⟨-323103, 11⟩⟩,
  ⟨⟨-323091, 11⟩, ⟨-429811, 12⟩⟩,
  ⟨⟨-214899, 11⟩, ⟨-298691, 12⟩⟩,
  ⟨⟨-149341, 11⟩, ⟨-430435, 13⟩⟩,
  ⟨⟨-430425, 13⟩, ⟨-319663, 13⟩⟩,
  ⟨⟨-39957, 10⟩, ⟨-487037, 14⟩⟩,
  ⟨⟨-487027, 14⟩, ⟨-379143, 14⟩⟩,
  ⟨⟨-1481, 6⟩, ⟨-300653, 14⟩⟩,
  ⟨⟨-300647, 14⟩, ⟨-60559, 12⟩⟩,
  ⟨⟨-484465, 15⟩, ⟨-395743, 15⟩⟩,
  ⟨⟨-395737, 15⟩, ⟨-327145, 15⟩⟩,
  ⟨⟨-81785, 13⟩, ⟨-273263, 15⟩⟩,
  ⟨⟨-273259, 15⟩, ⟨-115169, 14⟩⟩,
  ⟨⟨-230335, 15⟩, ⟨-391409, 16⟩⟩,
  ⟨⟨-97851, 14⟩, ⟨-10465, 11⟩⟩,
  ⟨⟨-334875, 16⟩, ⟨-72065, 14⟩⟩,
  ⟨⟨-288257, 16⟩, ⟨-498917, 17⟩⟩,
  ⟨⟨-15591, 12⟩, ⟨-216881, 16⟩⟩,
  ⟨⟨-216879, 16⟩, ⟨-189321, 16⟩⟩,
  ⟨⟨-189319, 16⟩, ⟨-165837, 16⟩⟩,
  ⟨⟨-165835, 16⟩, ⟨-72849, 15⟩⟩,
  ⟨⟨-4553, 11⟩, ⟨-256649, 17⟩⟩,
  ⟨⟨-513293, 18⟩, ⟨-113257, 16⟩⟩,
  ⟨⟨-453023, 18⟩, ⟨-400497, 18⟩⟩,
  ⟨⟨-400493, 18⟩, ⟨-354505, 18⟩⟩,
  ⟨⟨-354501, 18⟩, ⟨-157039, 17⟩⟩,
  ⟨⟨-157037, 17⟩, ⟨-34801, 15⟩⟩,
  ⟨⟨-278405, 18⟩, ⟨-246833, 18⟩⟩,
  ⟨⟨-246831, 18⟩, ⟨-13675, 14⟩⟩,
  ⟨⟨-437595, 19⟩, ⟨-24231, 15⟩⟩,
  ⟨⟨-96923, 17⟩, ⟨-171587, 18⟩⟩,
  ⟨⟨-171585, 18⟩, ⟨-75845, 17⟩⟩,
  ⟨⟨-303377, 19⟩, ⟨-133879, 18⟩⟩,
  ⟨⟨-267755, 19⟩, ⟨-471661, 20⟩⟩,
  ⟨⟨-58957, 17⟩, ⟨-414385, 20⟩⟩,
  ⟨⟨-414381, 20⟩, ⟨-362983, 20⟩⟩,
  ⟨⟨-362979, 20⟩, ⟨-316857, 20⟩⟩,
  ⟨⟨-316853, 20⟩, ⟨-275479, 20⟩⟩,
  ⟨⟨-68869, 18⟩, ⟨-59599, 18⟩⟩,
  ⟨⟨-476787, 21⟩, ⟨-410419, 21⟩⟩,
  ⟨⟨-205207, 20⟩, ⟨-351141, 21⟩⟩,
  ⟨⟨-351137, 21⟩, ⟨-37293, 18⟩⟩,
  ⟨⟨-74585, 19⟩, ⟨-31435, 18⟩⟩,
  ⟨⟨-251477, 21⟩, ⟨-210061, 21⟩⟩,
  ⟨⟨-105029, 20⟩, ⟨-86825, 20⟩⟩,
  ⟨⟨-347295, 22⟩, ⟨-283693, 22⟩⟩,
  ⟨⟨-35461, 19⟩, ⟨-228571, 22⟩⟩,
  ⟨⟨-457135, 23⟩, ⟨-362505, 23⟩⟩,
  ⟨⟨-362499, 23⟩, ⟨-70549, 21⟩⟩,
  ⟨⟨-282191, 23⟩, ⟨-214979, 23⟩⟩,
  ⟨⟨-214975, 23⟩, ⟨-159655, 23⟩⟩,
  ⟨⟨-319303, 24⟩, ⟨-115037, 23⟩⟩,
  ⟨⟨-230069, 24⟩, ⟨-159887, 24⟩⟩,
  ⟨⟨-159883, 24⟩, ⟨-425379, 26⟩⟩,
  ⟨⟨-53171, 23⟩, ⟨-134077, 25⟩⟩,
  ⟨⟨-134073, 25⟩, ⟨-158131, 26⟩⟩,
  ⟨⟨-316251, 27⟩, ⟨-171449, 27⟩⟩,
  ⟨⟨-342885, 28⟩, ⟨-333587, 29⟩⟩,
  ⟨⟨-333573, 29⟩, ⟨-281371, 30⟩⟩,
  ⟨⟨-281357, 30⟩, ⟨-12227, 27⟩⟩,
  ⟨⟨-391243, 32⟩, ⟨-25943, 30⟩⟩,
  ⟨⟨-415063, 34⟩, ⟨-296501, 36⟩⟩,
  ⟨⟨-296481, 36⟩, ⟨-459613, 40⟩⟩,
  ⟨⟨-459579, 40⟩, ⟨-514157, 45⟩⟩,
  ⟨⟨-514117, 45⟩, ⟨-171721, 51⟩⟩,
  ⟨⟨-343413, 52⟩, ⟨-402365, 66⟩⟩,
  ⟨⟨-402327, 66⟩, ⟨-262149, 99⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private def eulerianCoefficients : List ℤ := [
  0x1, 0x1ffffffffffffffffffae, 0x14d98d5cea0a5e834b6bf0c69d56d89bc,
  0x3ffffff95250b83d070459f1d76ce0619a2ecaf9a, 0x10de144b369d2c4750e1aa9f0ba3020b305bfb1c7e6a37b4, 0x29b2c447a8d505214e60ce6be207d5013777d81062a744324c5be,
  0xa8590dd38dbc7e711f34e25d2ea82e1700b07800cb54d354323f4a484, 0x7fca114f455d12dce81a5831619657181a3f1930d990a1c3e88705999027a, 0x1b02780002a953b953ac43841060e7554b3021cc65f8304ac17668464d7f9f2ae,
  0x21315444ef60df2935f175d5d59a017720691b6ec6d5c65a0750f76424fc951117ca, 0x11e34d94017f9a09ecb50a2d4fd22c55f8e8039b3fbe8b729123e4ce8bed2e20a8f5424, 0x4d8fab9a0c6de42ac35a0654ef4876d9cb97f3bdd2a6da3ca68df5a9490f62a323093732e,
  0xbb597b1349bc97bddb92fd757f618ca8c44a57bd29c8ea73f0344dd0d009de25f8744d34214, 0x110a8e1cf5af81a16f07c2dcda6b15d2874e39f8c885a541fd8e0a79a9c2bdc09e32413a2c676a, 0xfe2bc7ee7cc897de7261675bd1bfb9196e17ffc9f559555d3b5a788f0bf47e65a137ad49320721c,
  0x9f539f3e60e21803c350966d1b0111bf5cc6f226286acdfc49c8ff40a65ee2cb46adbd268f3aad51e, 0x45d930846006370909d82dda0979f03120ba1c37d0dd281e31523b3d80a6c972722da5e240c079ff56d, 0x161d5f67d3cb988ce76771ac8ad7ecee43db2407878c358618bd9fae33a674afc66366258d53ccfad1df8,
  0x5316a74c5aafb86cd6cf4707007fc38233941e7ad7f088b9f30d52b619ba9700c50557c143fd6bba7c0bf0, 0xecbfc3944a9b2ed4dbb1bd190a56dc516ec4b14cbac58eb4d05790d358e7ae40005b14d2dfeb437d5806528, 0x209502db3863c2a272b3ac14ee4c53b0b7cb311a43eec8508dd9c80114f0b00005fcca6df7a8900637541d610,
  0x3856fde6c1a35fc47cd1c1b961f13f0b0ae12813e2ce5e6e4f0d2aa2321b1dc57c6ab48fd510bb5d4df8976db8, 0x4d8ff71232b1067a23110207e0fdfe96cfa0de3c08109e0f0a094d574f41bdfe2faa64df0549ff6357ccfd4bf10, 0x5607241cfd70d795fd48546062f1c1de9ef679acb519328388b2f69d1bf880d49137b7a89d35aad538824e106928,
  0x4dab538f3dbabb48a3af0b3bdbad69dfaa5d7a6f832de218931dc0035369ad956e033b5ca464f67ab74672b9e31a8, 0x3997db2a85e0887e1466a8de0681a57a4af92ffdc49b175d214ac830d5614ee2cc938ba3d747cc14f40418b1059708, 0x2359e35bc2615eab6cf565d2d441afb4f96efd087270794bf4e586b3a6c19382e5c6df28bc81724fef286893c86f8d0,
  0x1215c449b8522893a7eddf2cbae840363d8b0cc7d3350fb4ed1ade14d046afed706d38193d75827c214aea59ff075858, 0x7c1ee7240d26494b8f84cf84c348108cadfc5b0731730fe0a80f1db69e775625293ccee265f4608bbced777bd7464450, 0x2ce073faf257b6633b761e13203a789a81a29a294cc3ce6808bfea1b4821803345edd4b88f1588114325cdd7843307a08,
  0xdbd4c178427c4307137c3f43cc5f4cdc9bea8a0846a7f23e7df92242520eccd084b24c339ae74cd25298a1f9b19a33230, 0x39386c0cb896ead334a64542e86f424a87f6436ac913b1933fdff3b60bab42b78fe9e6f0117a4b18af7373c3dd2ae13098, 0xcb4fd639f247423de38299d51d576c127a9c5a1f9670f367536f6a74b4aad3b28f2a50c067aac769bf0bfe22d3b2ac6d92,
  0x26a2d7e71433afa08674962cf2152fd4b64c50e5adafa270371c462ec40706abbd6a06b37d79d2ca34ef1fb05b7b365a6a4, 0x64c9519ced3c8cd32869f6f7f8d4206d4dd85d63bf11610bb5c6299456617befe7f989f7aa87ff4160d787cef2e70598208, 0xe20dddfabc47affa502c71afbbe709fccc9984d1653c95ead9772c406c00c364aab06b8ee7b8bc8407bdedcb96c62ec87cc,
  0x1b4b9021a921a371fc4b7c98a2ad13fee0d39f784c8bbcf42d43441b7c500e054fad0e7f137e9342f3e7b4ae9e26397e6bd8, 0x2d7cb359030fdb8550400ebb6dd14139ddcd22f1c28f174a77ffb924d50e95bb5dac489b7f0d65ab272f1b8bcd82612a8304, 0x4175ee532a5671197c1a5e7cb32d340f31e72ab77b1ff9fbd913c7347954f5367abbc50337ffb2d529874eeda86118199378,
  0x516a1477d452f7a98df01e98f1c48fe1c4f20f18df8e4921790554d47a28f8245eeea7c64c331f7cdb6f23bdb7754b691b8c, 0x578c99cf3514d002c9dee77a8a70418fd0d4145c057494334f03fff9b306efab7367637aceea06d04387c05c9f55f1aef154, 0x516a1477d452f7a98df01e98f1c48fe1c4f20f18df8e4921790554d47a28f8245eeea7c64c331f7cdb6f23bdb7754b691b8c,
  0x4175ee532a5671197c1a5e7cb32d340f31e72ab77b1ff9fbd913c7347954f5367abbc50337ffb2d529874eeda86118199378, 0x2d7cb359030fdb8550400ebb6dd14139ddcd22f1c28f174a77ffb924d50e95bb5dac489b7f0d65ab272f1b8bcd82612a8304, 0x1b4b9021a921a371fc4b7c98a2ad13fee0d39f784c8bbcf42d43441b7c500e054fad0e7f137e9342f3e7b4ae9e26397e6bd8,
  0xe20dddfabc47affa502c71afbbe709fccc9984d1653c95ead9772c406c00c364aab06b8ee7b8bc8407bdedcb96c62ec87cc, 0x64c9519ced3c8cd32869f6f7f8d4206d4dd85d63bf11610bb5c6299456617befe7f989f7aa87ff4160d787cef2e70598208, 0x26a2d7e71433afa08674962cf2152fd4b64c50e5adafa270371c462ec40706abbd6a06b37d79d2ca34ef1fb05b7b365a6a4,
  0xcb4fd639f247423de38299d51d576c127a9c5a1f9670f367536f6a74b4aad3b28f2a50c067aac769bf0bfe22d3b2ac6d92, 0x39386c0cb896ead334a64542e86f424a87f6436ac913b1933fdff3b60bab42b78fe9e6f0117a4b18af7373c3dd2ae13098, 0xdbd4c178427c4307137c3f43cc5f4cdc9bea8a0846a7f23e7df92242520eccd084b24c339ae74cd25298a1f9b19a33230,
  0x2ce073faf257b6633b761e13203a789a81a29a294cc3ce6808bfea1b4821803345edd4b88f1588114325cdd7843307a08, 0x7c1ee7240d26494b8f84cf84c348108cadfc5b0731730fe0a80f1db69e775625293ccee265f4608bbced777bd7464450, 0x1215c449b8522893a7eddf2cbae840363d8b0cc7d3350fb4ed1ade14d046afed706d38193d75827c214aea59ff075858,
  0x2359e35bc2615eab6cf565d2d441afb4f96efd087270794bf4e586b3a6c19382e5c6df28bc81724fef286893c86f8d0, 0x3997db2a85e0887e1466a8de0681a57a4af92ffdc49b175d214ac830d5614ee2cc938ba3d747cc14f40418b1059708, 0x4dab538f3dbabb48a3af0b3bdbad69dfaa5d7a6f832de218931dc0035369ad956e033b5ca464f67ab74672b9e31a8,
  0x5607241cfd70d795fd48546062f1c1de9ef679acb519328388b2f69d1bf880d49137b7a89d35aad538824e106928, 0x4d8ff71232b1067a23110207e0fdfe96cfa0de3c08109e0f0a094d574f41bdfe2faa64df0549ff6357ccfd4bf10, 0x3856fde6c1a35fc47cd1c1b961f13f0b0ae12813e2ce5e6e4f0d2aa2321b1dc57c6ab48fd510bb5d4df8976db8,
  0x209502db3863c2a272b3ac14ee4c53b0b7cb311a43eec8508dd9c80114f0b00005fcca6df7a8900637541d610, 0xecbfc3944a9b2ed4dbb1bd190a56dc516ec4b14cbac58eb4d05790d358e7ae40005b14d2dfeb437d5806528, 0x5316a74c5aafb86cd6cf4707007fc38233941e7ad7f088b9f30d52b619ba9700c50557c143fd6bba7c0bf0,
  0x161d5f67d3cb988ce76771ac8ad7ecee43db2407878c358618bd9fae33a674afc66366258d53ccfad1df8, 0x45d930846006370909d82dda0979f03120ba1c37d0dd281e31523b3d80a6c972722da5e240c079ff56d, 0x9f539f3e60e21803c350966d1b0111bf5cc6f226286acdfc49c8ff40a65ee2cb46adbd268f3aad51e,
  0xfe2bc7ee7cc897de7261675bd1bfb9196e17ffc9f559555d3b5a788f0bf47e65a137ad49320721c, 0x110a8e1cf5af81a16f07c2dcda6b15d2874e39f8c885a541fd8e0a79a9c2bdc09e32413a2c676a, 0xbb597b1349bc97bddb92fd757f618ca8c44a57bd29c8ea73f0344dd0d009de25f8744d34214,
  0x4d8fab9a0c6de42ac35a0654ef4876d9cb97f3bdd2a6da3ca68df5a9490f62a323093732e, 0x11e34d94017f9a09ecb50a2d4fd22c55f8e8039b3fbe8b729123e4ce8bed2e20a8f5424, 0x21315444ef60df2935f175d5d59a017720691b6ec6d5c65a0750f76424fc951117ca,
  0x1b02780002a953b953ac43841060e7554b3021cc65f8304ac17668464d7f9f2ae, 0x7fca114f455d12dce81a5831619657181a3f1930d990a1c3e88705999027a, 0xa8590dd38dbc7e711f34e25d2ea82e1700b07800cb54d354323f4a484,
  0x29b2c447a8d505214e60ce6be207d5013777d81062a744324c5be, 0x10de144b369d2c4750e1aa9f0ba3020b305bfb1c7e6a37b4, 0x3ffffff95250b83d070459f1d76ce0619a2ecaf9a,
  0x14d98d5cea0a5e834b6bf0c69d56d89bc, 0x1ffffffffffffffffffae, 0x1]

private theorem eulerianCoefficients_eq : descentCoeffs 81 = eulerianCoefficients := by
  decide +kernel

private theorem upper : upperOK (descentCoeffs 81) first gaps = true := by
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

private theorem lower (i : Fin (lastRepresentative 82 - 2)) :
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

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 82) :
    StrictNegativeInterlacing (originalQuotient 82 k) (eulerian 81) 79 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N082
