import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentPackedData.C127L072.N072

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N072

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L072.N072 LongCycleBounds.DescentNecklace.Packed.C127L072.N072.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L072.N072 LongCycleBounds.DescentNecklace.Packed.C127L072.N072.rows

private theorem actual : RepresentativeChecks 72 previousNodes rows :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L072.N072 LongCycleBounds.DescentNecklace.Packed.C127L072.N072.dataChecks

private def first : LongCycleFinite.Dyadic := ⟨-2361183241434822606848, 0⟩

private def gaps : List Window := [
  ⟨⟨-2361106680241157308416, 0⟩, ⟨-3217819697152, 0⟩⟩,
  ⟨⟨-3149091831808, 0⟩, ⟨-824135680, 0⟩⟩,
  ⟨⟨-694876160, 0⟩, ⟨-7247840, 0⟩⟩,
  ⟨⟨-7213664, 0⟩, ⟨-376732, 0⟩⟩,
  ⟨⟨-376397, 0⟩, ⟨-191927, 2⟩⟩,
  ⟨⟨-47965, 0⟩, ⟨-334577, 5⟩⟩,
  ⟨⟨-167257, 4⟩, ⟨-412781, 7⟩⟩,
  ⟨⟨-412731, 7⟩, ⟨-80717, 6⟩⟩,
  ⟨⟨-40355, 5⟩, ⟨-149601, 8⟩⟩,
  ⟨⟨-149591, 8⟩, ⟨-157111, 9⟩⟩,
  ⟨⟨-314205, 10⟩, ⟨-90719, 9⟩⟩,
  ⟨⟨-90715, 9⟩, ⟨-112783, 10⟩⟩,
  ⟨⟨-112779, 10⟩, ⟨-74317, 10⟩⟩,
  ⟨⟨-148629, 11⟩, ⟨-205277, 12⟩⟩,
  ⟨⟨-410543, 13⟩, ⟨-73639, 11⟩⟩,
  ⟨⟨-73637, 11⟩, ⟨-436183, 14⟩⟩,
  ⟨⟨-436173, 14⟩, ⟨-331535, 14⟩⟩,
  ⟨⟨-41441, 11⟩, ⟨-515207, 15⟩⟩,
  ⟨⟨-515197, 15⟩, ⟨-407831, 15⟩⟩,
  ⟨⟨-25489, 11⟩, ⟨-81997, 13⟩⟩,
  ⟨⟨-163991, 14⟩, ⟨-66841, 13⟩⟩,
  ⟨⟨-8355, 10⟩, ⟨-55121, 13⟩⟩,
  ⟨⟨-220481, 15⟩, ⟨-183643, 15⟩⟩,
  ⟨⟨-22955, 12⟩, ⟨-308547, 16⟩⟩,
  ⟨⟨-154271, 15⟩, ⟨-522219, 17⟩⟩,
  ⟨⟨-130553, 15⟩, ⟨-444721, 17⟩⟩,
  ⟨⟨-111179, 15⟩, ⟨-95191, 15⟩⟩,
  ⟨⟨-380759, 17⟩, ⟨-81871, 15⟩⟩,
  ⟨⟨-40935, 14⟩, ⟨-70683, 15⟩⟩,
  ⟨⟨-35341, 14⟩, ⟨-61213, 15⟩⟩,
  ⟨⟨-244849, 17⟩, ⟨-425147, 18⟩⟩,
  ⟨⟨-212571, 17⟩, ⟨-369801, 18⟩⟩,
  ⟨⟨-369797, 18⟩, ⟨-322083, 18⟩⟩,
  ⟨⟨-322079, 18⟩, ⟨-140373, 17⟩⟩,
  ⟨⟨-140371, 17⟩, ⟨-244777, 18⟩⟩,
  ⟨⟨-489549, 19⟩, ⟨-426723, 19⟩⟩,
  ⟨⟨-213359, 18⟩, ⟨-185831, 18⟩⟩,
  ⟨⟨-185829, 18⟩, ⟨-161639, 18⟩⟩,
  ⟨⟨-161637, 18⟩, ⟨-70165, 17⟩⟩,
  ⟨⟨-17541, 15⟩, ⟨-486119, 20⟩⟩,
  ⟨⟨-243057, 19⟩, ⟨-419685, 20⟩⟩,
  ⟨⟨-13115, 15⟩, ⟨-180481, 19⟩⟩,
  ⟨⟨-360957, 20⟩, ⟨-309049, 20⟩⟩,
  ⟨⟨-309045, 20⟩, ⟨-263187, 20⟩⟩,
  ⟨⟨-263183, 20⟩, ⟨-55681, 18⟩⟩,
  ⟨⟨-222721, 20⟩, ⟨-187103, 20⟩⟩,
  ⟨⟨-374201, 21⟩, ⟨-311679, 21⟩⟩,
  ⟨⟨-311675, 21⟩, ⟨-257031, 21⟩⟩,
  ⟨⟨-514055, 22⟩, ⟨-104761, 20⟩⟩,
  ⟨⟨-209519, 21⟩, ⟨-84251, 20⟩⟩,
  ⟨⟨-168499, 21⟩, ⟨-133385, 21⟩⟩,
  ⟨⟨-266765, 22⟩, ⟨-414563, 23⟩⟩,
  ⟨⟨-414555, 23⟩, ⟨-315099, 23⟩⟩,
  ⟨⟨-78773, 21⟩, ⟨-466609, 24⟩⟩,
  ⟨⟨-58325, 21⟩, ⟨-334773, 24⟩⟩,
  ⟨⟨-167383, 23⟩, ⟨-462359, 25⟩⟩,
  ⟨⟨-115587, 23⟩, ⟨-304663, 25⟩⟩,
  ⟨⟨-304655, 25⟩, ⟨-378755, 26⟩⟩,
  ⟨⟨-47343, 23⟩, ⟨-437403, 27⟩⟩,
  ⟨⟨-109347, 25⟩, ⟨-459379, 28⟩⟩,
  ⟨⟨-229681, 27⟩, ⟨-53211, 26⟩⟩,
  ⟨⟨-425669, 29⟩, ⟨-332991, 30⟩⟩,
  ⟨⟨-166487, 29⟩, ⟨-102703, 30⟩⟩,
  ⟨⟨-410789, 32⟩, ⟨-358147, 34⟩⟩,
  ⟨⟨-89531, 32⟩, ⟨-182539, 36⟩⟩,
  ⟨⟨-91263, 35⟩, ⟨-304139, 41⟩⟩,
  ⟨⟨-304115, 41⟩, ⟨-383009, 48⟩⟩,
  ⟨⟨-382977, 48⟩, ⟨-181313, 59⟩⟩,
  ⟨⟨-11331, 55⟩, ⟨-262149, 89⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private def eulerianCoefficients : List ℤ := [
  0x1, 0x7fffffffffffffffb8, 0x1723ecaf7aab05f77dd11edb8b187,
  0x3fffff97de56ea52dc652649d2f5240ff7f0, 0x1cfa578c95477c537e9d36c207639a01c4945026b7, 0xb9173f10b6ce365fb78cc9f72b23209722d05491cc0e38,
  0x9fd3a4dbdd13e530a13bb3022809e207eddbe80b81c9916351, 0x1fd3050d72dca6e6e0aa1ea703fcafabe3b9087fe811eb43a04500, 0x20e7fcf3fbb2b02a8fd0147767d40efd4ed127d67642b2b0e2ccdc448,
  0xde7d9839c48b9ab9c07d1c59233f9b1daf5af6120ef4b6948f3e75010c0, 0x2d2c8a272e8442b01644ad97136cb7b414f6aae03063179af38b68516fddf8, 0x4f4a60b79eacdf511d4d653d6115b773f5769601e8b3e1df7dd4e9baefa16080,
  0x521392196f06ea86b5294ad145ce66816477b365321bc29bb07cfafd546ac8fc58, 0x3592ae95b0d5b1f93419f0ca8101e7458f6b06d9741730703c604a8d979f038aedc0, 0x173b73141219282dfea1fc4fd1ee2982f36c0cee79938bd2499e51aaa2ed5d434f9ee8,
  0x6fa317e4400268821be61a816c0ab0377110c2428dd85878849c26c34009d412127cf00, 0x1802fdd24313ad8468db6a7d700dd51edf4ae5b3623040e1b477819a89e63b389dffde20c, 0x3cd3a634e48c493477d4378a24caee532f7e7617c96e4742bb80191d59c7d2faf0669e13a0,
  0x74082324d3d4c7b4fec73f34189f42714e5f0d783e1fdfd35eb58407e077d413f607da9e654, 0xa9dfb3d31ac64ef44d8048e64f266459f1fb7dda072749f9ab2b398fab437b099fdbeef3be40, 0xc1f5170e34f4ec3acc8645a5941f9c8143f2dd07130260ea540c28c2b544eeb29073f9c8500f4,
  0xaf13aa6e790fe58196501c59d8ff9677fa4933b12045c06c233cd51d65d25c53c21f98c5d2cea0, 0x7e65ebced8146185bd78dce7083a6dde263b168057dd93ae087ede9006c971c59dc0752f826ae6c, 0x49b795328c1bf175c07de3bdbdfb99ff588a3e5429473c4d850002229a146b8fe17dc034575c7500,
  0x230775cfc707464858e7b64d2980b5bee9c119174171a15acc520f6456d92547aaaf903b5d36ad118, 0xda989d4a9cdde5d1a0a81c48f5c070a94e53df2835e1839fee2e058672b87271555302aba594cf640, 0x466c6bdc03a5f540d5ad8483d3f8925485adb346e98fae2f91e74c8de74422de53461693a68faadba8,
  0x12d7a1aa3f00ddd60511632fa5f94b069865f06ee7fa99ca920c5c7d3ebfaaa4eec54ef361c1a292380, 0x434d34a6df1520694cb09accc1394015090fa86cf5e3377e05b4ab641d7c32b4659c6003d6c0a573688, 0xc95c811c8c0f976412eb4c4244b86589c7e6bfe58591cfb3cbeae063a8d983918d7c44c234cadf4af40,
  0x1fa4e37e6992e7b932b3a9abd5ce6e9e6dd30dfb40731c8d4cb576c670f1ff727a312d7dbd38a6b05b38, 0x430c4b742cb2090e0a655417dda4f6411304aebbcbf0ab20e59f96e1abe257abe89d7d9356f3b09f7700, 0x77f82d55291c17e1d318b84c64a43bb48a3bb15db348e0e2070eecf680313f4a33d4f881698c113e7cb6,
  0xb5938eb97a2852390fbcc25a0e3c8e788cf19910b07f12efc602b0ef462fa07dc4979dd4e6884fa66bd0, 0xe8bb1a3c9eaf4f36000ab38c788b5966e4a2f40a09332b23bd17de25eb05a3413a9dfc907775706053fa, 0xfcc925ca44fca584d71dbf7b6f9331124d5b8562fad95d0009b72627863f5715da28f1dd4e06ecdb8ba0,
  0xe8bb1a3c9eaf4f36000ab38c788b5966e4a2f40a09332b23bd17de25eb05a3413a9dfc907775706053fa, 0xb5938eb97a2852390fbcc25a0e3c8e788cf19910b07f12efc602b0ef462fa07dc4979dd4e6884fa66bd0, 0x77f82d55291c17e1d318b84c64a43bb48a3bb15db348e0e2070eecf680313f4a33d4f881698c113e7cb6,
  0x430c4b742cb2090e0a655417dda4f6411304aebbcbf0ab20e59f96e1abe257abe89d7d9356f3b09f7700, 0x1fa4e37e6992e7b932b3a9abd5ce6e9e6dd30dfb40731c8d4cb576c670f1ff727a312d7dbd38a6b05b38, 0xc95c811c8c0f976412eb4c4244b86589c7e6bfe58591cfb3cbeae063a8d983918d7c44c234cadf4af40,
  0x434d34a6df1520694cb09accc1394015090fa86cf5e3377e05b4ab641d7c32b4659c6003d6c0a573688, 0x12d7a1aa3f00ddd60511632fa5f94b069865f06ee7fa99ca920c5c7d3ebfaaa4eec54ef361c1a292380, 0x466c6bdc03a5f540d5ad8483d3f8925485adb346e98fae2f91e74c8de74422de53461693a68faadba8,
  0xda989d4a9cdde5d1a0a81c48f5c070a94e53df2835e1839fee2e058672b87271555302aba594cf640, 0x230775cfc707464858e7b64d2980b5bee9c119174171a15acc520f6456d92547aaaf903b5d36ad118, 0x49b795328c1bf175c07de3bdbdfb99ff588a3e5429473c4d850002229a146b8fe17dc034575c7500,
  0x7e65ebced8146185bd78dce7083a6dde263b168057dd93ae087ede9006c971c59dc0752f826ae6c, 0xaf13aa6e790fe58196501c59d8ff9677fa4933b12045c06c233cd51d65d25c53c21f98c5d2cea0, 0xc1f5170e34f4ec3acc8645a5941f9c8143f2dd07130260ea540c28c2b544eeb29073f9c8500f4,
  0xa9dfb3d31ac64ef44d8048e64f266459f1fb7dda072749f9ab2b398fab437b099fdbeef3be40, 0x74082324d3d4c7b4fec73f34189f42714e5f0d783e1fdfd35eb58407e077d413f607da9e654, 0x3cd3a634e48c493477d4378a24caee532f7e7617c96e4742bb80191d59c7d2faf0669e13a0,
  0x1802fdd24313ad8468db6a7d700dd51edf4ae5b3623040e1b477819a89e63b389dffde20c, 0x6fa317e4400268821be61a816c0ab0377110c2428dd85878849c26c34009d412127cf00, 0x173b73141219282dfea1fc4fd1ee2982f36c0cee79938bd2499e51aaa2ed5d434f9ee8,
  0x3592ae95b0d5b1f93419f0ca8101e7458f6b06d9741730703c604a8d979f038aedc0, 0x521392196f06ea86b5294ad145ce66816477b365321bc29bb07cfafd546ac8fc58, 0x4f4a60b79eacdf511d4d653d6115b773f5769601e8b3e1df7dd4e9baefa16080,
  0x2d2c8a272e8442b01644ad97136cb7b414f6aae03063179af38b68516fddf8, 0xde7d9839c48b9ab9c07d1c59233f9b1daf5af6120ef4b6948f3e75010c0, 0x20e7fcf3fbb2b02a8fd0147767d40efd4ed127d67642b2b0e2ccdc448,
  0x1fd3050d72dca6e6e0aa1ea703fcafabe3b9087fe811eb43a04500, 0x9fd3a4dbdd13e530a13bb3022809e207eddbe80b81c9916351, 0xb9173f10b6ce365fb78cc9f72b23209722d05491cc0e38,
  0x1cfa578c95477c537e9d36c207639a01c4945026b7, 0x3fffff97de56ea52dc652649d2f5240ff7f0, 0x1723ecaf7aab05f77dd11edb8b187,
  0x7fffffffffffffffb8, 0x1]

private theorem eulerianCoefficients_eq : descentCoeffs 71 = eulerianCoefficients := by
  decide +kernel

private theorem upper : upperOK (descentCoeffs 71) first gaps = true := by
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

private theorem lower (i : Fin (lastRepresentative 72 - 2)) :
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

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 72) :
    StrictNegativeInterlacing (originalQuotient 72 k) (eulerian 71) 69 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N072
