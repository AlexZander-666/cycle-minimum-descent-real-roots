import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentPackedData.C127L080.N073

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N073

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L080.N073 LongCycleBounds.DescentNecklace.Packed.C127L080.N073.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L080.N073 LongCycleBounds.DescentNecklace.Packed.C127L080.N073.rows

private theorem actual : RepresentativeChecks 73 previousNodes rows :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L080.N073 LongCycleBounds.DescentNecklace.Packed.C127L080.N073.dataChecks

private def first : LongCycleFinite.Dyadic := ⟨-4722366482869645213696, 0⟩

private def gaps : List Window := [
  ⟨⟨-4722213360482314616832, 0⟩, ⟨-4832710623232, 0⟩⟩,
  ⟨⟨-4695254892544, 0⟩, ⟨-1148018688, 0⟩⟩,
  ⟨⟨-953759744, 0⟩, ⟨-9067392, 0⟩⟩,
  ⟨⟨-9021440, 0⟩, ⟨-453541, 0⟩⟩,
  ⟨⟨-453121, 0⟩, ⟨-224785, 2⟩⟩,
  ⟨⟨-56176, 0⟩, ⟨-96039, 3⟩⟩,
  ⟨⟨-192041, 4⟩, ⟨-116717, 5⟩⟩,
  ⟨⟨-233405, 6⟩, ⟨-11279, 3⟩⟩,
  ⟨⟨-5639, 2⟩, ⟨-331361, 9⟩⟩,
  ⟨⟨-331339, 9⟩, ⟨-172691, 9⟩⟩,
  ⟨⟨-345363, 10⟩, ⟨-99097, 9⟩⟩,
  ⟨⟨-396371, 11⟩, ⟨-122561, 10⟩⟩,
  ⟨⟨-490227, 12⟩, ⟨-321633, 12⟩⟩,
  ⟨⟨-160811, 11⟩, ⟨-27663, 9⟩⟩,
  ⟨⟨-110649, 11⟩, ⟨-316571, 13⟩⟩,
  ⟨⟨-316563, 13⟩, ⟨-29223, 10⟩⟩,
  ⟨⟨-233779, 13⟩, ⟨-354615, 14⟩⟩,
  ⟨⟨-22163, 10⟩, ⟨-68757, 12⟩⟩,
  ⟨⟨-275023, 14⟩, ⟨-217375, 14⟩⟩,
  ⟨⟨-434743, 15⟩, ⟨-349199, 15⟩⟩,
  ⟨⟨-349193, 15⟩, ⟨-17773, 11⟩⟩,
  ⟨⟨-71091, 13⟩, ⟨-468657, 16⟩⟩,
  ⟨⟨-468651, 16⟩, ⟨-195067, 15⟩⟩,
  ⟨⟨-24383, 12⟩, ⟨-163809, 15⟩⟩,
  ⟨⟨-327613, 16⟩, ⟨-138603, 15⟩⟩,
  ⟨⟨-138601, 15⟩, ⟨-29509, 13⟩⟩,
  ⟨⟨-236069, 16⟩, ⟨-101081, 15⟩⟩,
  ⟨⟨-404319, 17⟩, ⟨-173941, 16⟩⟩,
  ⟨⟨-173939, 16⟩, ⟨-150255, 16⟩⟩,
  ⟨⟨-150253, 16⟩, ⟨-260443, 17⟩⟩,
  ⟨⟨-32555, 14⟩, ⟨-113161, 16⟩⟩,
  ⟨⟨-452639, 18⟩, ⟨-394165, 18⟩⟩,
  ⟨⟨-24635, 14⟩, ⟨-42971, 15⟩⟩,
  ⟨⟨-85941, 16⟩, ⟨-300121, 18⟩⟩,
  ⟨⟨-150059, 17⟩, ⟨-131073, 17⟩⟩,
  ⟨⟨-524285, 19⟩, ⟨-14311, 14⟩⟩,
  ⟨⟨-457947, 19⟩, ⟨-199903, 18⟩⟩,
  ⟨⟨-399801, 19⟩, ⟨-21793, 15⟩⟩,
  ⟨⟨-87171, 17⟩, ⟨-37955, 16⟩⟩,
  ⟨⟨-75909, 17⟩, ⟨-65965, 17⟩⟩,
  ⟨⟨-16491, 15⟩, ⟨-28585, 16⟩⟩,
  ⟨⟨-457355, 20⟩, ⟨-197539, 19⟩⟩,
  ⟨⟨-395073, 20⟩, ⟨-339927, 20⟩⟩,
  ⟨⟨-339923, 20⟩, ⟨-291099, 20⟩⟩,
  ⟨⟨-291095, 20⟩, ⟨-495811, 21⟩⟩,
  ⟨⟨-495805, 21⟩, ⟨-419513, 21⟩⟩,
  ⟨⟨-419507, 21⟩, ⟨-352295, 21⟩⟩,
  ⟨⟨-176145, 20⟩, ⟨-146633, 20⟩⟩,
  ⟨⟨-146631, 20⟩, ⟨-120829, 20⟩⟩,
  ⟨⟨-483309, 22⟩, ⟨-393589, 22⟩⟩,
  ⟨⟨-393583, 22⟩, ⟨-158069, 21⟩⟩,
  ⟨⟨-316133, 22⟩, ⟨-499739, 23⟩⟩,
  ⟨⟨-499731, 23⟩, ⟨-387581, 23⟩⟩,
  ⟨⟨-193787, 22⟩, ⟨-293949, 23⟩⟩,
  ⟨⟨-293943, 23⟩, ⟨-434153, 24⟩⟩,
  ⟨⟨-13567, 19⟩, ⟨-1213, 16⟩⟩,
  ⟨⟨-310521, 24⟩, ⟨-53415, 22⟩⟩,
  ⟨⟨-427309, 25⟩, ⟨-280363, 25⟩⟩,
  ⟨⟨-280355, 25⟩, ⟨-86687, 24⟩⟩,
  ⟨⟨-346737, 26⟩, ⟨-99489, 25⟩⟩,
  ⟨⟨-397943, 27⟩, ⟨-414787, 28⟩⟩,
  ⟨⟨-414771, 28⟩, ⟨-380815, 29⟩⟩,
  ⟨⟨-190399, 28⟩, ⟨-294415, 30⟩⟩,
  ⟨⟨-575, 21⟩, ⟨-357819, 32⟩⟩,
  ⟨⟨-178899, 31⟩, ⟨-305817, 34⟩⟩,
  ⟨⟨-305797, 34⟩, ⟨-303327, 37⟩⟩,
  ⟨⟨-303305, 37⟩, ⟨-242849, 41⟩⟩,
  ⟨⟨-121415, 40⟩, ⟨-287081, 48⟩⟩,
  ⟨⟨-17941, 44⟩, ⟨-483449, 61⟩⟩,
  ⟨⟨-120851, 59⟩, ⟨-262165, 90⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private def eulerianCoefficients : List ℤ := [
  0x1, 0xffffffffffffffffb7, 0x456bc60e723111e679735c92a00e5,
  0xfffffec344485e0c731e5475e1a9a307b923, 0x90e3c6beea49c4b08f501455031d9e11f479ce9d53, 0x456930fe932a057f3d726def0579ab29c1f586e3bc27735,
  0x45ef93a014dda657e6d4f375b29fe4d45e7fa52065a199561a7, 0xfec0bd2872b8594436a9e5609371a7e181cba8d52b7b4e4aec5f91, 0x128a730a80f13a41aa9d360ad428479a674e94aac27f88fe507b4d2688,
  0x8b9010981b865049bfe475084c3093ed92ff315825ca98bc72040fc3f538, 0x1f448165cdf887a8884bd5a4baf147b35f9a0d81b9a3bf7ebf6a88d85329828, 0x3c2402586c62ffbb154ef1c3d8ca581356a8dcece53f63319d2032c9ea3386a18,
  0x43d93d9f5ac8a6d2e35f6f05aee3c4b91479be74bfdf30ad857d6a5a51996076e78, 0x300f00edb884653ade52baf514931376daa01f63cabd10bfd2ef0e196ad26cdeb28c8, 0x1689ef9baf989c504614ba93b2e2edd1205d3018663f2724bbdf499e3a0427dbf242d18,
  0x74cf5483b80a027459982baf31c8b7759943d123a6ea329a570066f23e50add60f3751a8, 0x1b09e8830624f0ca76cac6820c08d7d98f4b4eb68143ba25758f1c3bdde4c1526720914acc, 0x4996bf83ad870ca27955e25c5c7744e737675c344cb46e1b90b5c91938a1441378656a8f1d4,
  0x969e4ecae3c24497ffd35ec500ffed2c19158ce7ce431cd3140492158b7e7258a2def8f43bfc, 0xec5d500e8152f009d99f9b35ac08f631e3b40b1a6dcdb5ced8919c49378d28b429c28af378c64, 0x121131ec986f1be16cc2e4a381a7d49cbee55d7a992671a3a4514bd30bcb42e485210e4606bb904,
  0x1175eddefbb02a6a1e56ce6db86e1bb12b8ae091bf52961e35f321127361dfa80bdb28cd2e9cf25c, 0xd7e45a42ea4267038fb96315a835e952c5d73c71169c23df4b18418ec7a4a9946eaed44aeea606f4, 0x86c4e1ee6985d0db3a00f7e4d58c96068a20accccebc43b897204bcd786b301ea56e76bc9b0125aac,
  0x448e140e21409b171f01a78c247848da2dd7a2e41dfee76c6830387344971e6af4f9e5669206c45b58, 0x1ca1de9ab978df3e92a39d5793942ccf3edef8455a7cc3fde9b3bd6313989977ab00a9c054ee26d65e8, 0x9e1e6246ae57ed29137304b391dc0b2d0da830a0e3d0fb970302962d9ee01f6789db309400d32d96a38,
  0x2d5a69df9ae5b052ee6dedde8eb6f5046631ed458d04cec0dc3b4a501f7664c1b67c9c21df5a1d887e88, 0xadccec02a198accb68efe95626a552784384b6767b9cfb817bf974fde200312c88ca07244211aaf34768, 0x22e6cef95fe2602f6a193cf0288239a9adf2abc732f440a93cdadf157ebd59ef5ba5d42f674221f52b258,
  0x5e58a5f39b872fcd3d56b33fcd8636fb8f94c69274c8f36544141ef0d4888e83adf5ab6b7b470b97fcc48, 0xd72f1ddc47ec83e6a6b70af80f2ae7f81f76314b6d084f6bdfd02e1fd930cded2a58ffb8e2c88c62d7bf8, 0x19f0e9a22148707e4dd604e5939af22c70ca6d2a6bf9ffba46c9dc1f0961b6db6d070fa7b43121d1f8ab76,
  0x2a6467dc9b7ca28efb3fd5e39939100483c72e597dc0fac6475fa19954d9d3f5020194d1fdb271349f515a, 0x3ac57bc5d1d3f408da577b6592980a5ef62e2415d974dbb57a3ea9a2b38cd72496321af55a8d4a2fdf7c0e, 0x452f541b34a2ddb97c41bae0a91cd6d271ec6c075e9af6502bb2347909d8b8d780269784003cf28ccbc5a2,
  0x452f541b34a2ddb97c41bae0a91cd6d271ec6c075e9af6502bb2347909d8b8d780269784003cf28ccbc5a2, 0x3ac57bc5d1d3f408da577b6592980a5ef62e2415d974dbb57a3ea9a2b38cd72496321af55a8d4a2fdf7c0e, 0x2a6467dc9b7ca28efb3fd5e39939100483c72e597dc0fac6475fa19954d9d3f5020194d1fdb271349f515a,
  0x19f0e9a22148707e4dd604e5939af22c70ca6d2a6bf9ffba46c9dc1f0961b6db6d070fa7b43121d1f8ab76, 0xd72f1ddc47ec83e6a6b70af80f2ae7f81f76314b6d084f6bdfd02e1fd930cded2a58ffb8e2c88c62d7bf8, 0x5e58a5f39b872fcd3d56b33fcd8636fb8f94c69274c8f36544141ef0d4888e83adf5ab6b7b470b97fcc48,
  0x22e6cef95fe2602f6a193cf0288239a9adf2abc732f440a93cdadf157ebd59ef5ba5d42f674221f52b258, 0xadccec02a198accb68efe95626a552784384b6767b9cfb817bf974fde200312c88ca07244211aaf34768, 0x2d5a69df9ae5b052ee6dedde8eb6f5046631ed458d04cec0dc3b4a501f7664c1b67c9c21df5a1d887e88,
  0x9e1e6246ae57ed29137304b391dc0b2d0da830a0e3d0fb970302962d9ee01f6789db309400d32d96a38, 0x1ca1de9ab978df3e92a39d5793942ccf3edef8455a7cc3fde9b3bd6313989977ab00a9c054ee26d65e8, 0x448e140e21409b171f01a78c247848da2dd7a2e41dfee76c6830387344971e6af4f9e5669206c45b58,
  0x86c4e1ee6985d0db3a00f7e4d58c96068a20accccebc43b897204bcd786b301ea56e76bc9b0125aac, 0xd7e45a42ea4267038fb96315a835e952c5d73c71169c23df4b18418ec7a4a9946eaed44aeea606f4, 0x1175eddefbb02a6a1e56ce6db86e1bb12b8ae091bf52961e35f321127361dfa80bdb28cd2e9cf25c,
  0x121131ec986f1be16cc2e4a381a7d49cbee55d7a992671a3a4514bd30bcb42e485210e4606bb904, 0xec5d500e8152f009d99f9b35ac08f631e3b40b1a6dcdb5ced8919c49378d28b429c28af378c64, 0x969e4ecae3c24497ffd35ec500ffed2c19158ce7ce431cd3140492158b7e7258a2def8f43bfc,
  0x4996bf83ad870ca27955e25c5c7744e737675c344cb46e1b90b5c91938a1441378656a8f1d4, 0x1b09e8830624f0ca76cac6820c08d7d98f4b4eb68143ba25758f1c3bdde4c1526720914acc, 0x74cf5483b80a027459982baf31c8b7759943d123a6ea329a570066f23e50add60f3751a8,
  0x1689ef9baf989c504614ba93b2e2edd1205d3018663f2724bbdf499e3a0427dbf242d18, 0x300f00edb884653ade52baf514931376daa01f63cabd10bfd2ef0e196ad26cdeb28c8, 0x43d93d9f5ac8a6d2e35f6f05aee3c4b91479be74bfdf30ad857d6a5a51996076e78,
  0x3c2402586c62ffbb154ef1c3d8ca581356a8dcece53f63319d2032c9ea3386a18, 0x1f448165cdf887a8884bd5a4baf147b35f9a0d81b9a3bf7ebf6a88d85329828, 0x8b9010981b865049bfe475084c3093ed92ff315825ca98bc72040fc3f538,
  0x128a730a80f13a41aa9d360ad428479a674e94aac27f88fe507b4d2688, 0xfec0bd2872b8594436a9e5609371a7e181cba8d52b7b4e4aec5f91, 0x45ef93a014dda657e6d4f375b29fe4d45e7fa52065a199561a7,
  0x456930fe932a057f3d726def0579ab29c1f586e3bc27735, 0x90e3c6beea49c4b08f501455031d9e11f479ce9d53, 0xfffffec344485e0c731e5475e1a9a307b923,
  0x456bc60e723111e679735c92a00e5, 0xffffffffffffffffb7, 0x1]

private theorem eulerianCoefficients_eq : descentCoeffs 72 = eulerianCoefficients := by
  decide +kernel

private theorem upper : upperOK (descentCoeffs 72) first gaps = true := by
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

private theorem lower (i : Fin (lastRepresentative 73 - 2)) :
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

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 73) :
    StrictNegativeInterlacing (originalQuotient 73 k) (eulerian 72) 70 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N073
