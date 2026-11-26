import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentPackedData.C127L072.N071

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N071

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L072.N071 LongCycleBounds.DescentNecklace.Packed.C127L072.N071.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L072.N071 LongCycleBounds.DescentNecklace.Packed.C127L072.N071.rows

private theorem actual : RepresentativeChecks 71 previousNodes rows :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L072.N071 LongCycleBounds.DescentNecklace.Packed.C127L072.N071.dataChecks

private def first : LongCycleFinite.Dyadic := ⟨-1180591620717411303424, 0⟩

private def gaps : List Window := [
  ⟨⟨-1180553340120578654208, 0⟩, ⟨-2135500521472, 0⟩⟩,
  ⟨⟨-2101136588800, 0⟩, ⟨-608757760, 0⟩⟩,
  ⟨⟨-522481664, 0⟩, ⟨-5791712, 0⟩⟩,
  ⟨⟨-5765344, 0⟩, ⟨-312811, 0⟩⟩,
  ⟨⟨-312545, 0⟩, ⟨-81913, 1⟩⟩,
  ⟨⟨-327541, 3⟩, ⟨-291377, 5⟩⟩,
  ⟨⟨-291323, 5⟩, ⟨-364921, 7⟩⟩,
  ⟨⟨-364877, 7⟩, ⟨-288773, 8⟩⟩,
  ⟨⟨-288749, 8⟩, ⟨-67527, 7⟩⟩,
  ⟨⟨-270091, 9⟩, ⟨-142907, 9⟩⟩,
  ⟨⟨-35725, 7⟩, ⟨-332127, 11⟩⟩,
  ⟨⟨-332113, 11⟩, ⟨-415027, 12⟩⟩,
  ⟨⟨-103753, 10⟩, ⟨-274653, 12⟩⟩,
  ⟨⟨-68661, 10⟩, ⟨-380707, 13⟩⟩,
  ⟨⟨-380697, 13⟩, ⟨-273973, 13⟩⟩,
  ⟨⟨-136983, 12⟩, ⟨-101687, 12⟩⟩,
  ⟨⟨-406739, 14⟩, ⟨-77457, 12⟩⟩,
  ⟨⟨-154911, 13⟩, ⟨-120585, 13⟩⟩,
  ⟨⟨-120583, 13⟩, ⟨-382389, 15⟩⟩,
  ⟨⟨-191191, 14⟩, ⟨-307893, 15⟩⟩,
  ⟨⟨-19243, 11⟩, ⟨-502447, 16⟩⟩,
  ⟨⟨-502439, 16⟩, ⟨-414649, 16⟩⟩,
  ⟨⟨-414643, 16⟩, ⟨-345539, 16⟩⟩,
  ⟨⟨-172767, 15⟩, ⟨-290363, 16⟩⟩,
  ⟨⟨-290359, 16⟩, ⟨-245747, 16⟩⟩,
  ⟨⟨-491487, 17⟩, ⟨-418521, 17⟩⟩,
  ⟨⟨-104629, 15⟩, ⟨-179115, 16⟩⟩,
  ⟨⟨-179113, 16⟩, ⟨-307959, 17⟩⟩,
  ⟨⟨-307955, 17⟩, ⟨-66425, 15⟩⟩,
  ⟨⟨-8303, 12⟩, ⟨-229905, 17⟩⟩,
  ⟨⟨-459805, 18⟩, ⟨-99693, 16⟩⟩,
  ⟨⟨-398767, 18⟩, ⟨-173209, 17⟩⟩,
  ⟨⟨-173207, 17⟩, ⟨-301267, 18⟩⟩,
  ⟨⟨-301263, 18⟩, ⟨-262147, 18⟩⟩,
  ⟨⟨-524287, 19⟩, ⟨-456207, 19⟩⟩,
  ⟨⟨-228101, 18⟩, ⟨-99187, 17⟩⟩,
  ⟨⟨-49593, 16⟩, ⟨-172329, 18⟩⟩,
  ⟨⟨-172327, 18⟩, ⟨-149453, 18⟩⟩,
  ⟨⟨-298903, 19⟩, ⟨-517281, 20⟩⟩,
  ⟨⟨-517275, 20⟩, ⟨-55787, 17⟩⟩,
  ⟨⟨-446291, 20⟩, ⟨-191833, 19⟩⟩,
  ⟨⟨-191831, 19⟩, ⟨-328397, 20⟩⟩,
  ⟨⟨-328393, 20⟩, ⟨-279639, 20⟩⟩,
  ⟨⟨-279635, 20⟩, ⟨-236671, 20⟩⟩,
  ⟨⟨-59167, 18⟩, ⟨-397757, 21⟩⟩,
  ⟨⟨-49719, 18⟩, ⟨-41433, 18⟩⟩,
  ⟨⟨-331459, 21⟩, ⟨-34193, 18⟩⟩,
  ⟨⟨-68385, 19⟩, ⟨-446391, 22⟩⟩,
  ⟨⟨-27899, 18⟩, ⟨-359433, 22⟩⟩,
  ⟨⟨-359427, 22⟩, ⟨-71237, 20⟩⟩,
  ⟨⟨-284943, 22⟩, ⟨-443603, 23⟩⟩,
  ⟨⟨-443595, 23⟩, ⟨-168953, 22⟩⟩,
  ⟨⟨-84475, 21⟩, ⟨-501663, 24⟩⟩,
  ⟨⟨-501653, 24⟩, ⟨-361017, 24⟩⟩,
  ⟨⟨-361009, 24⟩, ⟨-500423, 25⟩⟩,
  ⟨⟨-500411, 25⟩, ⟨-331163, 25⟩⟩,
  ⟨⟨-165577, 24⟩, ⟨-413833, 26⟩⟩,
  ⟨⟨-413821, 26⟩, ⟨-480879, 27⟩⟩,
  ⟨⟨-480863, 27⟩, ⟨-254427, 27⟩⟩,
  ⟨⟨-508835, 28⟩, ⟨-475957, 29⟩⟩,
  ⟨⟨-475937, 29⟩, ⟨-188331, 29⟩⟩,
  ⟨⟨-94161, 28⟩, ⟨-235863, 31⟩⟩,
  ⟨⟨-117925, 30⟩, ⟨-419507, 34⟩⟩,
  ⟨⟨-52435, 31⟩, ⟨-219723, 36⟩⟩,
  ⟨⟨-219707, 36⟩, ⟨-190475, 40⟩⟩,
  ⟨⟨-47615, 38⟩, ⟨-255515, 47⟩⟩,
  ⟨⟨-510987, 48⟩, ⟨-135987, 58⟩⟩,
  ⟨⟨-67987, 57⟩, ⟨-262165, 88⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private def eulerianCoefficients : List ℤ := [
  0x1, 0x3fffffffffffffffb9, 0x7b6a43a7ddd01fd29f05f9e8418e,
  0xfffffddc5873c6efc472c95e557b097a38e, 0x5cbaa45b7767d20385c088be15812ff29df5344e9, 0x1ed8f56d22ce26f8938a605f7e832bfb0a2bec2a6361b1,
  0x16d3f91c389fb8fa640451d6cff864f5f74d798e5d00e7a7a0, 0x3f9aa01e579cfdf144223b251c9163254c766a4308f556136cba0, 0x3a6426ef40691d63ad3971da6691d3ee0f5b44cb3877fd01400912a8,
  0x162922037d58338a63062fc6654b6a340baff20a5925ca299dd7082f468, 0x413a41f0bbf20385383ec2ea15e0c6161525fa4dafe7969792bc9231cb190, 0x68725dab1fe56fafe24df7d899af90bc2e345f745c8051e3b1e8de1e468a590,
  0x632a5e0009da36be9957219cb9f5c3d34cfcb40668a5bcd5cfd4d8f8f22f972c8, 0x3b9f180113148c8325eb85a55348e991ef5ff0ea20fb3f96861107fa5cca6375a08, 0x17e56275ed16988183a538d0c105d2f1fb3af68d07fdeb7734ab6bb9d447404551ae0,
  0x6a68ea5a74257725c719f613c1d16a12821bdc53b418ccf67116a732999a3e02e89ee0, 0x154122fcde4066557f0e1f4ade3f9b89a55641d0f3411a011411a929386f44b7f4b4ed2c, 0x321540bc0c25f4fe9b94a7f2170874e73ec591f6dac5d194012054d42372178ac995bc7cc,
  0x58fab9e347d85aef6587f9a0d2672a4eadca3b28891f171ab7facc2f1f4462b2b7d4166588, 0x79709e73f35849fc8a4d54f483878c9b2bbebb116f70c76cfe3d067813ee12644203e1ec188, 0x81581e162d51042ed91f22d5fe6a5e17202d9cc50779133077ec311f13467ab1365333a3426c,
  0x6cf4b1dbbd3e993a7fee912009adae9cb2e8f0c7bdae9f0937236b49b17efa7249d3e368ae6cc, 0x496be29e75773bf5f16187bd25d39b70cde74e338e4d52f2f84eabd84b0018edbb8fee5ef005a0, 0x27f791cde40e6425177d1186d9ed4891769f3fc6ff107dd54ef62bf15d584497898c825706e79a0,
  0x11b8f71143f10b742f1970b189ea5563f8f1d4b96be9fc5253ba273f60747114618e921d0c201978, 0x672a5ce7fc0579299961d3df1961ae4128fde9959d4f43d0c35cd1a78841083560859cac6422c8b8, 0x1efc6df1532b41c04f3d3a3c36d203f85634c7d51a9ce31ebd5ece0b874c44fe302e942b771640ef0,
  0x7b948707067ace08d66353e74e2f8323c5511314d5fcab797b6e52f94485197916c2c46ce7351f2f0, 0x19adef6eb9ed844e3e2afda199fb2eed419c28f3034799c28c1f8651ca78303c2b7816a1f4eb6f0398, 0x477106b87999a894a1fd09dab37a27a7fdb1825964c7644f867344290b6557f963ef7c73c544b98958,
  0xa6d4f2ee63e9ab244853b67208c51afc121df05a4ce06f5f7d529bbcd7b3c0e364a3b209e4265a9fe0, 0x147d82bf768ac3282f8c1fcb06231504d8180096d7f6ccdcfd055746151720c43071f4e0e5a6d93b3e0, 0x21f3833780144bba1ea471d802c151aee68c3644db930e5125f92ac79997b224d81ea4a952502e6bad6,
  0x2f8092648c3886c34e91fa5712add8b17ce40b608ad3ad9dab361464573fb19989160ab6016e0fb7da6, 0x382cb310811bb301135bf1a9a70443cb2da28f6b54304d8e3b0c415e1dd52fcbf79752312dc8a669ad4, 0x382cb310811bb301135bf1a9a70443cb2da28f6b54304d8e3b0c415e1dd52fcbf79752312dc8a669ad4,
  0x2f8092648c3886c34e91fa5712add8b17ce40b608ad3ad9dab361464573fb19989160ab6016e0fb7da6, 0x21f3833780144bba1ea471d802c151aee68c3644db930e5125f92ac79997b224d81ea4a952502e6bad6, 0x147d82bf768ac3282f8c1fcb06231504d8180096d7f6ccdcfd055746151720c43071f4e0e5a6d93b3e0,
  0xa6d4f2ee63e9ab244853b67208c51afc121df05a4ce06f5f7d529bbcd7b3c0e364a3b209e4265a9fe0, 0x477106b87999a894a1fd09dab37a27a7fdb1825964c7644f867344290b6557f963ef7c73c544b98958, 0x19adef6eb9ed844e3e2afda199fb2eed419c28f3034799c28c1f8651ca78303c2b7816a1f4eb6f0398,
  0x7b948707067ace08d66353e74e2f8323c5511314d5fcab797b6e52f94485197916c2c46ce7351f2f0, 0x1efc6df1532b41c04f3d3a3c36d203f85634c7d51a9ce31ebd5ece0b874c44fe302e942b771640ef0, 0x672a5ce7fc0579299961d3df1961ae4128fde9959d4f43d0c35cd1a78841083560859cac6422c8b8,
  0x11b8f71143f10b742f1970b189ea5563f8f1d4b96be9fc5253ba273f60747114618e921d0c201978, 0x27f791cde40e6425177d1186d9ed4891769f3fc6ff107dd54ef62bf15d584497898c825706e79a0, 0x496be29e75773bf5f16187bd25d39b70cde74e338e4d52f2f84eabd84b0018edbb8fee5ef005a0,
  0x6cf4b1dbbd3e993a7fee912009adae9cb2e8f0c7bdae9f0937236b49b17efa7249d3e368ae6cc, 0x81581e162d51042ed91f22d5fe6a5e17202d9cc50779133077ec311f13467ab1365333a3426c, 0x79709e73f35849fc8a4d54f483878c9b2bbebb116f70c76cfe3d067813ee12644203e1ec188,
  0x58fab9e347d85aef6587f9a0d2672a4eadca3b28891f171ab7facc2f1f4462b2b7d4166588, 0x321540bc0c25f4fe9b94a7f2170874e73ec591f6dac5d194012054d42372178ac995bc7cc, 0x154122fcde4066557f0e1f4ade3f9b89a55641d0f3411a011411a929386f44b7f4b4ed2c,
  0x6a68ea5a74257725c719f613c1d16a12821bdc53b418ccf67116a732999a3e02e89ee0, 0x17e56275ed16988183a538d0c105d2f1fb3af68d07fdeb7734ab6bb9d447404551ae0, 0x3b9f180113148c8325eb85a55348e991ef5ff0ea20fb3f96861107fa5cca6375a08,
  0x632a5e0009da36be9957219cb9f5c3d34cfcb40668a5bcd5cfd4d8f8f22f972c8, 0x68725dab1fe56fafe24df7d899af90bc2e345f745c8051e3b1e8de1e468a590, 0x413a41f0bbf20385383ec2ea15e0c6161525fa4dafe7969792bc9231cb190,
  0x162922037d58338a63062fc6654b6a340baff20a5925ca299dd7082f468, 0x3a6426ef40691d63ad3971da6691d3ee0f5b44cb3877fd01400912a8, 0x3f9aa01e579cfdf144223b251c9163254c766a4308f556136cba0,
  0x16d3f91c389fb8fa640451d6cff864f5f74d798e5d00e7a7a0, 0x1ed8f56d22ce26f8938a605f7e832bfb0a2bec2a6361b1, 0x5cbaa45b7767d20385c088be15812ff29df5344e9,
  0xfffffddc5873c6efc472c95e557b097a38e, 0x7b6a43a7ddd01fd29f05f9e8418e, 0x3fffffffffffffffb9,
  0x1]

private theorem eulerianCoefficients_eq : descentCoeffs 70 = eulerianCoefficients := by
  decide +kernel

private theorem upper : upperOK (descentCoeffs 70) first gaps = true := by
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

private theorem lower (i : Fin (lastRepresentative 71 - 2)) :
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

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 71) :
    StrictNegativeInterlacing (originalQuotient 71 k) (eulerian 70) 68 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N071
