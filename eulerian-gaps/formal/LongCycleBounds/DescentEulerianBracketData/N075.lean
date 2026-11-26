import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentPackedData.C127L080.N075

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N075

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L080.N075 LongCycleBounds.DescentNecklace.Packed.C127L080.N075.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L080.N075 LongCycleBounds.DescentNecklace.Packed.C127L080.N075.rows

private theorem actual : RepresentativeChecks 75 previousNodes rows :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L080.N075 LongCycleBounds.DescentNecklace.Packed.C127L080.N075.dataChecks

private def first : LongCycleFinite.Dyadic := ⟨-18889465931478580854784, 0⟩

private def gaps : List Window := [
  ⟨⟨-18888853441929258467328, 0⟩, ⟨-10948643389440, 0⟩⟩,
  ⟨⟨-10398887575552, 0⟩, ⟨-2062848000, 0⟩⟩,
  ⟨⟨-1629540352, 0⟩, ⟨-14258176, 0⟩⟩,
  ⟨⟨-14185856, 0⟩, ⟨-656304, 0⟩⟩,
  ⟨⟨-655642, 0⟩, ⟨-77037, 0⟩⟩,
  ⟨⟨-154015, 1⟩, ⟨-506169, 5⟩⟩,
  ⟨⟨-506067, 5⟩, ⟨-298467, 6⟩⟩,
  ⟨⟨-74607, 4⟩, ⟨-450799, 8⟩⟩,
  ⟨⟨-225379, 7⟩, ⟨-50775, 6⟩⟩,
  ⟨⟨-101543, 7⟩, ⟨-416979, 10⟩⟩,
  ⟨⟨-416957, 10⟩, ⟨-118155, 9⟩⟩,
  ⟨⟨-472599, 11⟩, ⟨-144619, 10⟩⟩,
  ⟨⟨-289227, 11⟩, ⟨-376221, 12⟩⟩,
  ⟨⟨-376209, 12⟩, ⟨-513925, 13⟩⟩,
  ⟨⟨-513911, 13⟩, ⟨-91323, 11⟩⟩,
  ⟨⟨-365283, 13⟩, ⟨-268343, 13⟩⟩,
  ⟨⟨-268337, 13⟩, ⟨-405211, 14⟩⟩,
  ⟨⟨-405203, 14⟩, ⟨-313083, 14⟩⟩,
  ⟨⟨-313077, 14⟩, ⟨-493343, 15⟩⟩,
  ⟨⟨-493335, 15⟩, ⟨-395225, 15⟩⟩,
  ⟨⟨-395219, 15⟩, ⟨-321167, 15⟩⟩,
  ⟨⟨-321161, 15⟩, ⟨-132103, 14⟩⟩,
  ⟨⟨-132101, 14⟩, ⟨-439315, 16⟩⟩,
  ⟨⟨-439309, 16⟩, ⟨-368599, 16⟩⟩,
  ⟨⟨-184297, 15⟩, ⟨-311721, 16⟩⟩,
  ⟨⟨-311717, 16⟩, ⟨-132713, 15⟩⟩,
  ⟨⟨-132711, 15⟩, ⟨-56835, 14⟩⟩,
  ⟨⟨-227337, 16⟩, ⟨-48927, 14⟩⟩,
  ⟨⟨-391411, 17⟩, ⟨-169205, 16⟩⟩,
  ⟨⟨-169203, 16⟩, ⟨-146823, 16⟩⟩,
  ⟨⟨-146821, 16⟩, ⟨-255575, 17⟩⟩,
  ⟨⟨-63893, 15⟩, ⟨-445975, 18⟩⟩,
  ⟨⟨-222985, 17⟩, ⟨-389855, 18⟩⟩,
  ⟨⟨-194925, 17⟩, ⟨-341281, 18⟩⟩,
  ⟨⟨-341277, 18⟩, ⟨-299037, 18⟩⟩,
  ⟨⟨-149517, 17⟩, ⟨-262145, 18⟩⟩,
  ⟨⟨-131071, 17⟩, ⟨-229805, 18⟩⟩,
  ⟨⟨-459605, 19⟩, ⟨-201359, 18⟩⟩,
  ⟨⟨-201357, 18⟩, ⟨-352541, 19⟩⟩,
  ⟨⟨-176269, 18⟩, ⟨-308181, 19⟩⟩,
  ⟨⟨-308177, 19⟩, ⟨-67221, 17⟩⟩,
  ⟨⟨-16805, 15⟩, ⟨-234023, 19⟩⟩,
  ⟨⟨-468041, 20⟩, ⟨-50767, 17⟩⟩,
  ⟨⟨-406131, 20⟩, ⟨-10973, 15⟩⟩,
  ⟨⟨-87783, 18⟩, ⟨-302279, 20⟩⟩,
  ⟨⟨-302275, 20⟩, ⟨-129453, 19⟩⟩,
  ⟨⟨-258903, 20⟩, ⟨-27557, 17⟩⟩,
  ⟨⟨-440907, 21⟩, ⟨-186437, 20⟩⟩,
  ⟨⟨-372869, 21⟩, ⟨-312851, 21⟩⟩,
  ⟨⟨-312847, 21⟩, ⟨-520203, 22⟩⟩,
  ⟨⟨-130049, 20⟩, ⟨-213971, 21⟩⟩,
  ⟨⟨-13373, 17⟩, ⟨-347753, 22⟩⟩,
  ⟨⟨-347747, 22⟩, ⟨-139295, 21⟩⟩,
  ⟨⟨-278585, 22⟩, ⟨-27437, 19⟩⟩,
  ⟨⟨-54873, 20⟩, ⟨-339187, 23⟩⟩,
  ⟨⟨-339181, 23⟩, ⟨-512193, 24⟩⟩,
  ⟨⟨-512183, 24⟩, ⟨-376247, 24⟩⟩,
  ⟨⟨-376239, 24⟩, ⟨-133719, 23⟩⟩,
  ⟨⟨-267431, 24⟩, ⟨-91331, 23⟩⟩,
  ⟨⟨-365315, 25⟩, ⟨-237599, 25⟩⟩,
  ⟨⟨-475185, 26⟩, ⟨-290817, 26⟩⟩,
  ⟨⟨-36351, 23⟩, ⟨-329619, 27⟩⟩,
  ⟨⟨-329607, 27⟩, ⟨-169189, 27⟩⟩,
  ⟨⟨-84591, 26⟩, ⟨-152453, 28⟩⟩,
  ⟨⟨-76223, 27⟩, ⟨-230255, 30⟩⟩,
  ⟨⟨-230243, 30⟩, ⟨-4243, 26⟩⟩,
  ⟨⟨-16971, 28⟩, ⟨-446097, 35⟩⟩,
  ⟨⟨-111517, 33⟩, ⟨-52361, 35⟩⟩,
  ⟨⟨-209429, 37⟩, ⟨-154869, 41⟩⟩,
  ⟨⟨-154857, 41⟩, ⟨-322587, 49⟩⟩,
  ⟨⟨-315, 39⟩, ⟨-53715, 59⟩⟩,
  ⟨⟨-429679, 62⟩, ⟨-262165, 92⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private def eulerianCoefficients : List ℤ := [
  0x1, 0x3ffffffffffffffffb5, 0x270c9f6821a09a11a450e41279b680,
  0xffffff48f4d4c7df96adcd4dc4d2e9659adb8, 0xe2640d9a4de81fb205b367c8e040f05f18553017ac2, 0x9c2e586ad94f1b6a434db2c16da8be58d6ad0b73aab7a082,
  0xd63c90ba467ae5b4e80ef25db95d7826df8eb83978b9c2c3bcb8, 0x3fc13576cdadec84c3ad7f506f2b0fc8338bd09acdf7356e42d98400, 0x5e22244a939ed3073cd76bd4f59899c341e6531f7d08017a3f612e64c0d,
  0x36dd0f6852f55239e7a7e6c90186cd68d607b70af60d3e12c37fd6b3ce62b9, 0xef4df05f7e56e35e3adc5a168aa2a9b340b1e5da468f481464b861bedeae4780, 0x22844c185e8140168f2df02db746883e2cf6054379e32e14737aafcec98e9d89f40,
  0x2e355360eecddd4a6f538dd6fd4a7ac7f3411216afc6a033e16b5bc23cf5a0c519ff0, 0x267fb39f7cdeb6dc308a039f4f18dfe5fa2f4b3cc123ffaeb92bb0a7e2247be1c70fb70, 0x1516cad009ba62265539e8df9ee50171f3bbc028fb946793c237b9b9b9d88e6cc50dee540,
  0x7ef21a228b3a5f28e974c9b3b4cf159774993d3220eb02eb556e5f8182d87d2f3fe5228a80, 0x21fa469e379b6d172134613ac09b8ee3e2318fed89274bf329508cfca4c227ffea063c521594, 0x6a8c6a615f014be6ecf14331309d65299a107c3b3c3032085b409856397c6196dde274cf006e4,
  0xfa92d55a1021f7c5376120a87294d9807c6fbc9e143e50be2312a875b345d5ee316410fd183280, 0x1c2db5ca44f504911cb4dfaf636c3643e94b27bdbd441fd8087ef1749774142e18750ed04c72d120, 0x2773a48ef6c9e38eedf2dc5878e0cc399edd92f2df40703c9c42433b5e5c953a4049a05bad2669ef8,
  0x2b99a80a398a59ee461b90e8aa5081d7ebd98b8ec90bd03258651bba9acae423fc13c38bcccef7d778, 0x268149264a2ae0028a1626906bf6bc3220bef2122bf717fd4dff04cda5ba146d887e8a7642079642320, 0x1b764eac03a77bc2a859a446fe8ed78c12c3e273ba29ecf5b305c5bb99e5f9859e89f8f9ed10eae4df80,
  0xff6520faaaffb4903c01cb3c2f3663e9756676e72ec175a5f3f0219276658af85270328c9fc9f09bcff4, 0x79ef745756c26f3038fb7e48c7af015a8fa7c554aa2c9fdb0707a315a9eed7dbc28371d83cb8da3dbe4e4, 0x30257f2ca7abe2489319620a03cdf215faad37d1c5c4a319d7cf1b277dfac976f95ab435f2b86af1f08380,
  0xfd0b4813dbbc6fa0dd9a42e3f99595820de79545573388b0f7e02048f9da5a702b45cef76a957f2999c8c0, 0x458062ffb885ffae4b50fc7150c9a3074ab3cd2d7d3251e649a492320ab741c52a3bb56c1a9c8e809d12b10, 0x10081969cc0cbf05fccf1339f6bfc7964b7146ff55042aeb8de5616bec2c5e7e11d64f21ad297ef3a3fb1090,
  0x31e0291730fe4a2e8f66368b10e9687f49d9315d923e0cea933d0aa53d017033fe5743dcdde18663c48c16c0, 0x8336683b4ae98bf2e4298156d016caf4f9ba54058f260bde7c8aff54e03a0d08d706eb1f8dc0cc50b79d2a80, 0x124ab756c346bca78fbebe7afc8a5ddba329a2fbb4218cc753b40df1216e2acd319a8508c9c2f868c3c9c08ce,
  0x22aa74728981bff1a0638daad26e448a09eca1dcdb2970c9ca807736b3fa6c37ce8b01f5f52c8e4b924677766, 0x37e9b770a2c29a82fbbb4bbd392fe5ab637ab25544801db0436206ca2ac0255887a7cb9f775fd9a648a753380, 0x4cd8c713e535bc8910acaf839f77f2e6bfdd9e484459c9e7a555451c2b9d1f0e74123ae0d3d3c1f83830a3d50,
  0x5a12b09242dcbc4c2f28bb360474a280afbd6403971f899ed8261b27714b4723acc9d9a3b1e9680bc44e7974c, 0x5a12b09242dcbc4c2f28bb360474a280afbd6403971f899ed8261b27714b4723acc9d9a3b1e9680bc44e7974c, 0x4cd8c713e535bc8910acaf839f77f2e6bfdd9e484459c9e7a555451c2b9d1f0e74123ae0d3d3c1f83830a3d50,
  0x37e9b770a2c29a82fbbb4bbd392fe5ab637ab25544801db0436206ca2ac0255887a7cb9f775fd9a648a753380, 0x22aa74728981bff1a0638daad26e448a09eca1dcdb2970c9ca807736b3fa6c37ce8b01f5f52c8e4b924677766, 0x124ab756c346bca78fbebe7afc8a5ddba329a2fbb4218cc753b40df1216e2acd319a8508c9c2f868c3c9c08ce,
  0x8336683b4ae98bf2e4298156d016caf4f9ba54058f260bde7c8aff54e03a0d08d706eb1f8dc0cc50b79d2a80, 0x31e0291730fe4a2e8f66368b10e9687f49d9315d923e0cea933d0aa53d017033fe5743dcdde18663c48c16c0, 0x10081969cc0cbf05fccf1339f6bfc7964b7146ff55042aeb8de5616bec2c5e7e11d64f21ad297ef3a3fb1090,
  0x458062ffb885ffae4b50fc7150c9a3074ab3cd2d7d3251e649a492320ab741c52a3bb56c1a9c8e809d12b10, 0xfd0b4813dbbc6fa0dd9a42e3f99595820de79545573388b0f7e02048f9da5a702b45cef76a957f2999c8c0, 0x30257f2ca7abe2489319620a03cdf215faad37d1c5c4a319d7cf1b277dfac976f95ab435f2b86af1f08380,
  0x79ef745756c26f3038fb7e48c7af015a8fa7c554aa2c9fdb0707a315a9eed7dbc28371d83cb8da3dbe4e4, 0xff6520faaaffb4903c01cb3c2f3663e9756676e72ec175a5f3f0219276658af85270328c9fc9f09bcff4, 0x1b764eac03a77bc2a859a446fe8ed78c12c3e273ba29ecf5b305c5bb99e5f9859e89f8f9ed10eae4df80,
  0x268149264a2ae0028a1626906bf6bc3220bef2122bf717fd4dff04cda5ba146d887e8a7642079642320, 0x2b99a80a398a59ee461b90e8aa5081d7ebd98b8ec90bd03258651bba9acae423fc13c38bcccef7d778, 0x2773a48ef6c9e38eedf2dc5878e0cc399edd92f2df40703c9c42433b5e5c953a4049a05bad2669ef8,
  0x1c2db5ca44f504911cb4dfaf636c3643e94b27bdbd441fd8087ef1749774142e18750ed04c72d120, 0xfa92d55a1021f7c5376120a87294d9807c6fbc9e143e50be2312a875b345d5ee316410fd183280, 0x6a8c6a615f014be6ecf14331309d65299a107c3b3c3032085b409856397c6196dde274cf006e4,
  0x21fa469e379b6d172134613ac09b8ee3e2318fed89274bf329508cfca4c227ffea063c521594, 0x7ef21a228b3a5f28e974c9b3b4cf159774993d3220eb02eb556e5f8182d87d2f3fe5228a80, 0x1516cad009ba62265539e8df9ee50171f3bbc028fb946793c237b9b9b9d88e6cc50dee540,
  0x267fb39f7cdeb6dc308a039f4f18dfe5fa2f4b3cc123ffaeb92bb0a7e2247be1c70fb70, 0x2e355360eecddd4a6f538dd6fd4a7ac7f3411216afc6a033e16b5bc23cf5a0c519ff0, 0x22844c185e8140168f2df02db746883e2cf6054379e32e14737aafcec98e9d89f40,
  0xef4df05f7e56e35e3adc5a168aa2a9b340b1e5da468f481464b861bedeae4780, 0x36dd0f6852f55239e7a7e6c90186cd68d607b70af60d3e12c37fd6b3ce62b9, 0x5e22244a939ed3073cd76bd4f59899c341e6531f7d08017a3f612e64c0d,
  0x3fc13576cdadec84c3ad7f506f2b0fc8338bd09acdf7356e42d98400, 0xd63c90ba467ae5b4e80ef25db95d7826df8eb83978b9c2c3bcb8, 0x9c2e586ad94f1b6a434db2c16da8be58d6ad0b73aab7a082,
  0xe2640d9a4de81fb205b367c8e040f05f18553017ac2, 0xffffff48f4d4c7df96adcd4dc4d2e9659adb8, 0x270c9f6821a09a11a450e41279b680,
  0x3ffffffffffffffffb5, 0x1]

private theorem eulerianCoefficients_eq : descentCoeffs 74 = eulerianCoefficients := by
  decide +kernel

private theorem upper : upperOK (descentCoeffs 74) first gaps = true := by
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

private theorem lower (i : Fin (lastRepresentative 75 - 2)) :
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

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 75) :
    StrictNegativeInterlacing (originalQuotient 75 k) (eulerian 74) 72 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N075
