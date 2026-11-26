import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentPackedData.C127L072.N066

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N066

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L072.N066 LongCycleBounds.DescentNecklace.Packed.C127L072.N066.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L072.N066 LongCycleBounds.DescentNecklace.Packed.C127L072.N066.rows

private theorem actual : RepresentativeChecks 66 previousNodes rows :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L072.N066 LongCycleBounds.DescentNecklace.Packed.C127L072.N066.dataChecks

private def first : LongCycleFinite.Dyadic := ⟨-36893488147419103232, 0⟩

private def gaps : List Window := [
  ⟨⟨-36892291878768082944, 0⟩, ⟨-279563993088, 0⟩⟩,
  ⟨⟨-278489202688, 0⟩, ⟨-134224896, 0⟩⟩,
  ⟨⟨-122868992, 0⟩, ⟨-1871772, 0⟩⟩,
  ⟨⟨-1865748, 0⟩, ⟨-494547, 2⟩⟩,
  ⟨⟨-494207, 2⟩, ⟨-296725, 4⟩⟩,
  ⟨⟨-296639, 4⟩, ⟨-36405, 3⟩⟩,
  ⟨⟨-36399, 3⟩, ⟨-49125, 5⟩⟩,
  ⟨⟨-196479, 7⟩, ⟨-41199, 6⟩⟩,
  ⟨⟨-164783, 8⟩, ⟨-161421, 9⟩⟩,
  ⟨⟨-322823, 10⟩, ⟨-354595, 11⟩⟩,
  ⟨⟨-177289, 10⟩, ⟨-106211, 10⟩⟩,
  ⟨⟨-106207, 10⟩, ⟨-272243, 12⟩⟩,
  ⟨⟨-136117, 11⟩, ⟨-2875, 6⟩⟩,
  ⟨⟨-367989, 13⟩, ⟨-519151, 14⟩⟩,
  ⟨⟨-259569, 13⟩, ⟨-189569, 13⟩⟩,
  ⟨⟨-379129, 14⟩, ⟨-284919, 14⟩⟩,
  ⟨⟨-284913, 14⟩, ⟨-219253, 14⟩⟩,
  ⟨⟨-219249, 14⟩, ⟨-172101, 14⟩⟩,
  ⟨⟨-86049, 13⟩, ⟨-8585, 10⟩⟩,
  ⟨⟨-274715, 15⟩, ⟨-444747, 16⟩⟩,
  ⟨⟨-111185, 14⟩, ⟨-364323, 16⟩⟩,
  ⟨⟨-182159, 15⟩, ⟨-301479, 16⟩⟩,
  ⟨⟨-150737, 15⟩, ⟨-503239, 17⟩⟩,
  ⟨⟨-503233, 17⟩, ⟨-423059, 17⟩⟩,
  ⟨⟨-423053, 17⟩, ⟨-357813, 17⟩⟩,
  ⟨⟨-22363, 13⟩, ⟨-304157, 17⟩⟩,
  ⟨⟨-304153, 17⟩, ⟨-519209, 18⟩⟩,
  ⟨⟨-519203, 18⟩, ⟨-111151, 16⟩⟩,
  ⟨⟨-222299, 17⟩, ⟨-190829, 17⟩⟩,
  ⟨⟨-190827, 17⟩, ⟨-328189, 18⟩⟩,
  ⟨⟨-328185, 18⟩, ⟨-282503, 18⟩⟩,
  ⟨⟨-282499, 18⟩, ⟨-486513, 19⟩⟩,
  ⟨⟨-486507, 19⟩, ⟨-418785, 19⟩⟩,
  ⟨⟨-104695, 17⟩, ⟨-90029, 17⟩⟩,
  ⟨⟨-360111, 19⟩, ⟨-77283, 17⟩⟩,
  ⟨⟨-38641, 16⟩, ⟨-264711, 19⟩⟩,
  ⟨⟨-66177, 17⟩, ⟨-225937, 19⟩⟩,
  ⟨⟨-112967, 18⟩, ⟨-24007, 16⟩⟩,
  ⟨⟨-384107, 20⟩, ⟨-162437, 19⟩⟩,
  ⟨⟨-162435, 19⟩, ⟨-34139, 17⟩⟩,
  ⟨⟨-273109, 20⟩, ⟨-455889, 21⟩⟩,
  ⟨⟨-455883, 21⟩, ⟨-377249, 21⟩⟩,
  ⟨⟨-94311, 19⟩, ⟨-38629, 18⟩⟩,
  ⟨⟨-309027, 21⟩, ⟨-125073, 20⟩⟩,
  ⟨⟨-500285, 22⟩, ⟨-49913, 19⟩⟩,
  ⟨⟨-199649, 21⟩, ⟨-78357, 20⟩⟩,
  ⟨⟨-156711, 21⟩, ⟨-241191, 22⟩⟩,
  ⟨⟨-482373, 23⟩, ⟨-181255, 22⟩⟩,
  ⟨⟨-362503, 23⟩, ⟨-264749, 23⟩⟩,
  ⟨⟨-264743, 23⟩, ⟨-23343, 20⟩⟩,
  ⟨⟨-373479, 24⟩, ⟨-252425, 24⟩⟩,
  ⟨⟨-504837, 25⟩, ⟨-161755, 24⟩⟩,
  ⟨⟨-323501, 25⟩, ⟨-193799, 25⟩⟩,
  ⟨⟨-387585, 26⟩, ⟨-106437, 25⟩⟩,
  ⟨⟨-106433, 25⟩, ⟨-52127, 25⟩⟩,
  ⟨⟨-416999, 28⟩, ⟨-349759, 29⟩⟩,
  ⟨⟨-174871, 28⟩, ⟨-235977, 30⟩⟩,
  ⟨⟨-58991, 28⟩, ⟨-463289, 33⟩⟩,
  ⟨⟨-115815, 31⟩, ⟨-278061, 35⟩⟩,
  ⟨⟨-278041, 35⟩, ⟨-18371, 35⟩⟩,
  ⟨⟨-293913, 39⟩, ⟨-67575, 43⟩⟩,
  ⟨⟨-270277, 45⟩, ⟨-516411, 57⟩⟩,
  ⟨⟨-516363, 57⟩, ⟨-262149, 83⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private def eulerianCoefficients : List ℤ := [
  0x1, 0x1ffffffffffffffbe, 0x82047e0e2a6b9676a56c7c3f64,
  0x3ffffde7ad78047ca4335695a07f91e7a, 0x798a0b8e44232fe97d95969ed4c309b9e68a78, 0x103e9a663d62a59ef05f8444af69b45faa185425296,
  0x58e1e79d499e694ce3c81c8f1fc91e8ba83be04b2ab1ec, 0x7e90cfd21898ba420eff3679d4d0612e1c34f0d49fb43b092, 0x3ffb7a53f9685ec6658d4a6cc150a05000fe4e1ad44fb43a7f08,
  0xe252bbc225f22f1c536b155ab6755e049f90354de1c257f39f575e, 0x1951a86a53094c328f362614c24c75642478d49fb00342a0be1840b14, 0x197cd1ad4b929f0cca4443356ae20dfd83aefdb5de75cb1dec1145aab7a,
  0xf9ca52d64051cb6ef315cc7b0568c0a7c381cd56bf676defbeb7bf8f9428, 0x62e000d993a2f4fe3fdde74f9bc72b394d7d65227af60089ce32842e31ee36, 0x1a8244a2c93ac20d11b77858b4a42b57ee5f639f942a423144dcd0c50d477a5c,
  0x4ff420414641664af9c96c1668f7cb6f2da3a3f95f62edb41794835d723e0f012, 0xaebf99e981b8f152141390e32af60f157cb208a1459d6b0c68c6a1371c3098d1bc, 0x11bafb21872b6c2b73196035e0bab728b41dd90f0afe2abbdb1e37af8a146f694d76,
  0x15d1fe055ad52040b810dfa8ba4eaaab61f3fd137ebe102577278eafffa28d5500fd4, 0x14b4ff01239d583959c1b368e0f6c23a433a2382e3d18837ae562ec6bfd62be81e7be2, 0xf5f02befba46cdb5a78c19bec24b6762c42c49e0e685af11625ea1423d5be6f9a594b8,
  0x908ae1f357cc3284fe4367633c4c4fb056b71fee5fdaeb7638097df53f2bcadb9eff0ae, 0x43f36f93bc7bc06173f49a5673133fafe51c1bb65c23eab4bd2383b67cd1d60ccb5e27fc, 0x19c66e0bf3dfcaeb27d484444f2b41400af0e5289d1d97ffcded19c5b572445526eddfa5a,
  0x7f27a56f6a4bc82c6b59e66e6b14c7b9af02f2c83ecee23d99501fd5949474a0f86a311b8, 0x201126e09b79f9b8f882164c6cbc512cd9b5c577f7e9854d1402aec896dbea94def8e82c36, 0x6a631285e7d60eee155c59d6206618ca00effca54ad0d6fde98519da971b80ba0e56663404,
  0x12377c097872cd6a78eb82fc4b3a0a25b9f9fb42901e89863af9cf717b8290a989170def0c2, 0x295c4102d816fdc548f3344b776046ac8e1d8bc870fba89744bb302356a94f124c37ab48ca8, 0x4e0afa43c01ed242b6b0abadc39d1c8c5bfba870a126b68143d18b389aff11d864dd8da17ee,
  0x7aa4e44cc7242c888b0fc78540b579c3c69335c2b5c6fed079b07ace90a505dc86562791d6c, 0xa0c2758ece51cc755f8241b103ae0440dcca91feab023b3c2b016d5f19cb0f26f475a7d143a, 0xafeb138c49d4dadd7f751292ae2ad0709a104749698a77c17c7db4252f79c1350314d72bb06,
  0xa0c2758ece51cc755f8241b103ae0440dcca91feab023b3c2b016d5f19cb0f26f475a7d143a, 0x7aa4e44cc7242c888b0fc78540b579c3c69335c2b5c6fed079b07ace90a505dc86562791d6c, 0x4e0afa43c01ed242b6b0abadc39d1c8c5bfba870a126b68143d18b389aff11d864dd8da17ee,
  0x295c4102d816fdc548f3344b776046ac8e1d8bc870fba89744bb302356a94f124c37ab48ca8, 0x12377c097872cd6a78eb82fc4b3a0a25b9f9fb42901e89863af9cf717b8290a989170def0c2, 0x6a631285e7d60eee155c59d6206618ca00effca54ad0d6fde98519da971b80ba0e56663404,
  0x201126e09b79f9b8f882164c6cbc512cd9b5c577f7e9854d1402aec896dbea94def8e82c36, 0x7f27a56f6a4bc82c6b59e66e6b14c7b9af02f2c83ecee23d99501fd5949474a0f86a311b8, 0x19c66e0bf3dfcaeb27d484444f2b41400af0e5289d1d97ffcded19c5b572445526eddfa5a,
  0x43f36f93bc7bc06173f49a5673133fafe51c1bb65c23eab4bd2383b67cd1d60ccb5e27fc, 0x908ae1f357cc3284fe4367633c4c4fb056b71fee5fdaeb7638097df53f2bcadb9eff0ae, 0xf5f02befba46cdb5a78c19bec24b6762c42c49e0e685af11625ea1423d5be6f9a594b8,
  0x14b4ff01239d583959c1b368e0f6c23a433a2382e3d18837ae562ec6bfd62be81e7be2, 0x15d1fe055ad52040b810dfa8ba4eaaab61f3fd137ebe102577278eafffa28d5500fd4, 0x11bafb21872b6c2b73196035e0bab728b41dd90f0afe2abbdb1e37af8a146f694d76,
  0xaebf99e981b8f152141390e32af60f157cb208a1459d6b0c68c6a1371c3098d1bc, 0x4ff420414641664af9c96c1668f7cb6f2da3a3f95f62edb41794835d723e0f012, 0x1a8244a2c93ac20d11b77858b4a42b57ee5f639f942a423144dcd0c50d477a5c,
  0x62e000d993a2f4fe3fdde74f9bc72b394d7d65227af60089ce32842e31ee36, 0xf9ca52d64051cb6ef315cc7b0568c0a7c381cd56bf676defbeb7bf8f9428, 0x197cd1ad4b929f0cca4443356ae20dfd83aefdb5de75cb1dec1145aab7a,
  0x1951a86a53094c328f362614c24c75642478d49fb00342a0be1840b14, 0xe252bbc225f22f1c536b155ab6755e049f90354de1c257f39f575e, 0x3ffb7a53f9685ec6658d4a6cc150a05000fe4e1ad44fb43a7f08,
  0x7e90cfd21898ba420eff3679d4d0612e1c34f0d49fb43b092, 0x58e1e79d499e694ce3c81c8f1fc91e8ba83be04b2ab1ec, 0x103e9a663d62a59ef05f8444af69b45faa185425296,
  0x798a0b8e44232fe97d95969ed4c309b9e68a78, 0x3ffffde7ad78047ca4335695a07f91e7a, 0x82047e0e2a6b9676a56c7c3f64,
  0x1ffffffffffffffbe, 0x1]

private theorem eulerianCoefficients_eq : descentCoeffs 65 = eulerianCoefficients := by
  decide +kernel

private theorem upper : upperOK (descentCoeffs 65) first gaps = true := by
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

private theorem lower (i : Fin (lastRepresentative 66 - 2)) :
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

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 66) :
    StrictNegativeInterlacing (originalQuotient 66 k) (eulerian 65) 63 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N066
