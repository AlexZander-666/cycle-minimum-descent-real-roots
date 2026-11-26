import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentPackedData.C127L072.N068

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N068

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L072.N068 LongCycleBounds.DescentNecklace.Packed.C127L072.N068.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L072.N068 LongCycleBounds.DescentNecklace.Packed.C127L072.N068.rows

private theorem actual : RepresentativeChecks 68 previousNodes rows :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L072.N068 LongCycleBounds.DescentNecklace.Packed.C127L072.N068.dataChecks

private def first : LongCycleFinite.Dyadic := ⟨-147573952589676412928, 0⟩

private def gaps : List Window := [
  ⟨⟨-147569167515072331776, 0⟩, ⟨-630135455744, 0⟩⟩,
  ⟨⟨-625838391296, 0⟩, ⟨-247918592, 0⟩⟩,
  ⟨⟨-222312960, 0⟩, ⟨-2941680, 0⟩⟩,
  ⟨⟨-2931376, 0⟩, ⟨-179338, 0⟩⟩,
  ⟨⟨-358407, 1⟩, ⟨-407525, 4⟩⟩,
  ⟨⟨-50925, 1⟩, ⟨-96135, 4⟩⟩,
  ⟨⟨-384475, 6⟩, ⟨-31479, 4⟩⟩,
  ⟨⟨-503609, 8⟩, ⟨-206375, 8⟩⟩,
  ⟨⟨-412717, 9⟩, ⟨-396945, 10⟩⟩,
  ⟨⟨-396921, 10⟩, ⟨-107395, 9⟩⟩,
  ⟨⟨-429559, 11⟩, ⟨-127113, 10⟩⟩,
  ⟨⟨-31777, 8⟩, ⟨-322571, 12⟩⟩,
  ⟨⟨-315, 2⟩, ⟨-432421, 13⟩⟩,
  ⟨⟨-54051, 10⟩, ⟨-75725, 11⟩⟩,
  ⟨⟨-75723, 11⟩, ⟨-27493, 10⟩⟩,
  ⟨⟨-439877, 14⟩, ⟨-82247, 12⟩⟩,
  ⟨⟨-328981, 14⟩, ⟨-504335, 15⟩⟩,
  ⟨⟨-504325, 15⟩, ⟨-394603, 15⟩⟩,
  ⟨⟨-98649, 13⟩, ⟨-314147, 15⟩⟩,
  ⟨⟨-157071, 14⟩, ⟨-253793, 15⟩⟩,
  ⟨⟨-253789, 15⟩, ⟨-25951, 12⟩⟩,
  ⟨⟨-207605, 15⟩, ⟨-343287, 16⟩⟩,
  ⟨⟨-171641, 15⟩, ⟨-286397, 16⟩⟩,
  ⟨⟨-286393, 16⟩, ⟨-481565, 17⟩⟩,
  ⟨⟨-481559, 17⟩, ⟨-407513, 17⟩⟩,
  ⟨⟨-101877, 15⟩, ⟨-43343, 14⟩⟩,
  ⟨⟨-86685, 15⟩, ⟨-74097, 15⟩⟩,
  ⟨⟨-4631, 11⟩, ⟨-15893, 13⟩⟩,
  ⟨⟨-254285, 17⟩, ⟨-218815, 17⟩⟩,
  ⟨⟨-437625, 18⟩, ⟨-188713, 17⟩⟩,
  ⟨⟨-377421, 18⟩, ⟨-326019, 18⟩⟩,
  ⟨⟨-326015, 18⟩, ⟨-35235, 15⟩⟩,
  ⟨⟨-281877, 18⟩, ⟨-487585, 19⟩⟩,
  ⟨⟨-487579, 19⟩, ⟨-105393, 17⟩⟩,
  ⟨⟨-421567, 19⟩, ⟨-364151, 19⟩⟩,
  ⟨⟨-364147, 19⟩, ⟨-157029, 18⟩⟩,
  ⟨⟨-157027, 18⟩, ⟨-33781, 16⟩⟩,
  ⟨⟨-67561, 17⟩, ⟨-463719, 20⟩⟩,
  ⟨⟨-463713, 20⟩, ⟨-198187, 19⟩⟩,
  ⟨⟨-198185, 19⟩, ⟨-168633, 19⟩⟩,
  ⟨⟨-168631, 19⟩, ⟨-285405, 20⟩⟩,
  ⟨⟨-285401, 20⟩, ⟨-119973, 19⟩⟩,
  ⟨⟨-239943, 20⟩, ⟨-400369, 21⟩⟩,
  ⟨⟨-400363, 21⟩, ⟨-165505, 20⟩⟩,
  ⟨⟨-331005, 21⟩, ⟨-270773, 21⟩⟩,
  ⟨⟨-270769, 21⟩, ⟨-218753, 21⟩⟩,
  ⟨⟨-437499, 22⟩, ⟨-174151, 21⟩⟩,
  ⟨⟨-348297, 22⟩, ⟨-272519, 22⟩⟩,
  ⟨⟨-136257, 21⟩, ⟨-417769, 23⟩⟩,
  ⟨⟨-417761, 23⟩, ⟨-156227, 22⟩⟩,
  ⟨⟨-312447, 23⟩, ⟨-453753, 24⟩⟩,
  ⟨⟨-453743, 24⟩, ⟨-317849, 24⟩⟩,
  ⟨⟨-317841, 24⟩, ⟨-213039, 24⟩⟩,
  ⟨⟨-426067, 25⟩, ⟨-270311, 25⟩⟩,
  ⟨⟨-270303, 25⟩, ⟨-319957, 26⟩⟩,
  ⟨⟨-159973, 25⟩, ⟨-86565, 25⟩⟩,
  ⟨⟨-346247, 27⟩, ⟨-332995, 28⟩⟩,
  ⟨⟨-332981, 28⟩, ⟨-68223, 27⟩⟩,
  ⟨⟨-136439, 28⟩, ⟨-357439, 31⟩⟩,
  ⟨⟨-357419, 31⟩, ⟨-337297, 33⟩⟩,
  ⟨⟨-337275, 33⟩, ⟨-383441, 36⟩⟩,
  ⟨⟨-191707, 35⟩, ⟨-374433, 40⟩⟩,
  ⟨⟨-93601, 38⟩, ⟨-151767, 45⟩⟩,
  ⟨⟨-303509, 46⟩, ⟨-14343, 53⟩⟩,
  ⟨⟨-458933, 58⟩, ⟨-262149, 85⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private def eulerianCoefficients : List ℤ := [
  0x1, 0x7ffffffffffffffbc, 0x492286e8201c84a2bd0d05df801,
  0x3ffffec92d42a52e36cc4c5c88a70bb910, 0xbde83e8e465b9228b3ad56b15cdce4f9abb3af0, 0x248e1c56ccb19e9b33e75b6f85826dac30455ac6e1e0,
  0x11065b5f628d5bac9c1ca1347926f24c1a95e238a0c048f0, 0x1fb7900b2702348f2d777386ec934a3aac6fa087366ae597430, 0x145d4d51988ca7cb046f6ec0cd879df21b61681204f357bae31a78,
  0x5979a60013b4c84ec5d7c3da01ac03adc768b042116c2e81b9403d60, 0xc39538f488eddc923717e4ec1931c4f327d45eaa132b0ec2a29a023278, 0xed5163c443900dc69d9e791d7f110a99533c32481e33359b953be115ebd0,
  0xad72e4c6a13d137d35523ac3d97150ad1ebf7027e5232025fcdcef897404d0, 0x51469efe1b2a9e13e1940b2731f657650759c8ecc22d9b2d783bc0f3bce34ca0, 0x19a30af5275d4b238d5e5f595ec24e91ad215a4dce5508f2661d9f81403f1d72d0,
  0x5a89a86043cc81fb4d48d2b8ace899ce399976d2912191652522ad0f7ca99f301f0, 0xe6d8cdea8213a8267e4c24bcce34e8a23a9a11fb0ddb342268f42b72bafe45994b1c, 0x1b3fbae46ebbbd925c3ee754aa0889cb7bf1065a41f9233f967282ba1165902bd97510,
  0x26ef93a3c4db09b4c0862d60a5f01500988d0aae637375d2ec558f48d23462d571e3b1c, 0x2ad813e0e1383dfc66842dd64ea5319674e9f5cb9be8c4248bbadbcfcb6f1bec928d38d0, 0x24d9ade55365a03edd3291bbb669b2419f9facd5544d4b358b7057172a6c97e22e90c1df0,
  0x1916b04e7a3586813109867b1e480429ee75b277eb1803aa452fba84fb9d652c299abf4ee0, 0xdaa9540be40de0cbd34d780caa927982551319139aff8fcb737d25662b653ecd1512be33f0, 0x602c4cd59e4e420fc8fe575c34862ef2c4c293511cb269f3eebfbabfb7b88b7e96f5dc6ae70,
  0x226bc29f058aab108e9ecf232c59de4b7041ddab1b119bb2a02b041776e2239a9aba387b1d48, 0xa1773ac48efedeb92893fa22c50b2361f043820d7ac10315c5ba165529c2de9ef122128447a0, 0x26ff31cfb3214c9bb48d50fe11a979448da144d8dac870b629775f5dd9037032317e9a8141548,
  0x7cbaa81f3f4afd0d1337ca7dcc89726e2c97d4d75ca0fb3e55026c078ece982c040a260f6f590, 0x14b8100ac5b925912e5c7fa7e3b4a9cb8b5b899571368a04effc2e1e867f3d70d2c3d6c7087e50, 0x2de80b1382dfa929bc6aafa420f839c453c5e153f5bb6d612a4f72f80766421f32671f485182a0,
  0x5502ec8cd89adbe88adaf036fb8373a45283cdbf629d46a0d87108e009b28cc054aed9708fb450, 0x83d59a340d1432f3fd9853e939e348513ff42164587930283fa3bf6ef2f38e62575d0bde470830, 0xab71d1027d5e6f0bd8b12490edbc28598de3bbe185774cb869982b6d380fef2a1e9dc526068246,
  0xbb1e4cd0b6e808d0197ce981467eae184d07c2763798de8b36ba2c2d8d519226c7ec941b4e0c68, 0xab71d1027d5e6f0bd8b12490edbc28598de3bbe185774cb869982b6d380fef2a1e9dc526068246, 0x83d59a340d1432f3fd9853e939e348513ff42164587930283fa3bf6ef2f38e62575d0bde470830,
  0x5502ec8cd89adbe88adaf036fb8373a45283cdbf629d46a0d87108e009b28cc054aed9708fb450, 0x2de80b1382dfa929bc6aafa420f839c453c5e153f5bb6d612a4f72f80766421f32671f485182a0, 0x14b8100ac5b925912e5c7fa7e3b4a9cb8b5b899571368a04effc2e1e867f3d70d2c3d6c7087e50,
  0x7cbaa81f3f4afd0d1337ca7dcc89726e2c97d4d75ca0fb3e55026c078ece982c040a260f6f590, 0x26ff31cfb3214c9bb48d50fe11a979448da144d8dac870b629775f5dd9037032317e9a8141548, 0xa1773ac48efedeb92893fa22c50b2361f043820d7ac10315c5ba165529c2de9ef122128447a0,
  0x226bc29f058aab108e9ecf232c59de4b7041ddab1b119bb2a02b041776e2239a9aba387b1d48, 0x602c4cd59e4e420fc8fe575c34862ef2c4c293511cb269f3eebfbabfb7b88b7e96f5dc6ae70, 0xdaa9540be40de0cbd34d780caa927982551319139aff8fcb737d25662b653ecd1512be33f0,
  0x1916b04e7a3586813109867b1e480429ee75b277eb1803aa452fba84fb9d652c299abf4ee0, 0x24d9ade55365a03edd3291bbb669b2419f9facd5544d4b358b7057172a6c97e22e90c1df0, 0x2ad813e0e1383dfc66842dd64ea5319674e9f5cb9be8c4248bbadbcfcb6f1bec928d38d0,
  0x26ef93a3c4db09b4c0862d60a5f01500988d0aae637375d2ec558f48d23462d571e3b1c, 0x1b3fbae46ebbbd925c3ee754aa0889cb7bf1065a41f9233f967282ba1165902bd97510, 0xe6d8cdea8213a8267e4c24bcce34e8a23a9a11fb0ddb342268f42b72bafe45994b1c,
  0x5a89a86043cc81fb4d48d2b8ace899ce399976d2912191652522ad0f7ca99f301f0, 0x19a30af5275d4b238d5e5f595ec24e91ad215a4dce5508f2661d9f81403f1d72d0, 0x51469efe1b2a9e13e1940b2731f657650759c8ecc22d9b2d783bc0f3bce34ca0,
  0xad72e4c6a13d137d35523ac3d97150ad1ebf7027e5232025fcdcef897404d0, 0xed5163c443900dc69d9e791d7f110a99533c32481e33359b953be115ebd0, 0xc39538f488eddc923717e4ec1931c4f327d45eaa132b0ec2a29a023278,
  0x5979a60013b4c84ec5d7c3da01ac03adc768b042116c2e81b9403d60, 0x145d4d51988ca7cb046f6ec0cd879df21b61681204f357bae31a78, 0x1fb7900b2702348f2d777386ec934a3aac6fa087366ae597430,
  0x11065b5f628d5bac9c1ca1347926f24c1a95e238a0c048f0, 0x248e1c56ccb19e9b33e75b6f85826dac30455ac6e1e0, 0xbde83e8e465b9228b3ad56b15cdce4f9abb3af0,
  0x3ffffec92d42a52e36cc4c5c88a70bb910, 0x492286e8201c84a2bd0d05df801, 0x7ffffffffffffffbc,
  0x1]

private theorem eulerianCoefficients_eq : descentCoeffs 67 = eulerianCoefficients := by
  decide +kernel

private theorem upper : upperOK (descentCoeffs 67) first gaps = true := by
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

private theorem lower (i : Fin (lastRepresentative 68 - 2)) :
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

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 68) :
    StrictNegativeInterlacing (originalQuotient 68 k) (eulerian 67) 65 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N068
