import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentPackedData.C127L080.N074

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N074

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L080.N074 LongCycleBounds.DescentNecklace.Packed.C127L080.N074.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L080.N074 LongCycleBounds.DescentNecklace.Packed.C127L080.N074.rows

private theorem actual : RepresentativeChecks 74 previousNodes rows :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L080.N074 LongCycleBounds.DescentNecklace.Packed.C127L080.N074.dataChecks

private def first : LongCycleFinite.Dyadic := ⟨-9444732965739290427392, 0⟩

private def gaps : List Window := [
  ⟨⟨-9444426720964629233664, 0⟩, ⟨-7237841977344, 0⟩⟩,
  ⟨⟨-6962964070400, 0⟩, ⟨-1341595648, 0⟩⟩,
  ⟨⟨-1050888192, 0⟩, ⟨-11397216, 0⟩⟩,
  ⟨⟨-11333600, 0⟩, ⟨-545618, 0⟩⟩,
  ⟨⟨-545092, 0⟩, ⟨-131619, 1⟩⟩,
  ⟨⟨-65785, 0⟩, ⟨-440987, 5⟩⟩,
  ⟨⟨-110225, 3⟩, ⟨-131987, 5⟩⟩,
  ⟨⟨-65985, 4⟩, ⟨-100847, 6⟩⟩,
  ⟨⟨-50419, 5⟩, ⟨-366909, 9⟩⟩,
  ⟨⟨-91721, 7⟩, ⟨-379539, 10⟩⟩,
  ⟨⟨-189759, 9⟩, ⟨-216435, 10⟩⟩,
  ⟨⟨-432851, 11⟩, ⟨-266297, 11⟩⟩,
  ⟨⟨-266287, 11⟩, ⟨-347911, 12⟩⟩,
  ⟨⟨-86975, 10⟩, ⟨-119251, 11⟩⟩,
  ⟨⟨-476991, 13⟩, ⟨-170057, 12⟩⟩,
  ⟨⟨-170053, 12⟩, ⟨-15657, 9⟩⟩,
  ⟨⟨-125253, 12⟩, ⟨-379141, 14⟩⟩,
  ⟨⟨-379133, 14⟩, ⟨-293499, 14⟩⟩,
  ⟨⟨-293493, 14⟩, ⟨-115807, 13⟩⟩,
  ⟨⟨-115805, 13⟩, ⟨-46449, 12⟩⟩,
  ⟨⟨-371585, 15⟩, ⟨-302291, 15⟩⟩,
  ⟨⟨-151143, 14⟩, ⟨-497785, 16⟩⟩,
  ⟨⟨-248889, 15⟩, ⟨-103531, 14⟩⟩,
  ⟨⟨-207059, 15⟩, ⟨-347625, 16⟩⟩,
  ⟨⟨-347621, 16⟩, ⟨-294063, 16⟩⟩,
  ⟨⟨-294059, 16⟩, ⟨-250419, 16⟩⟩,
  ⟨⟨-15651, 12⟩, ⟨-428947, 17⟩⟩,
  ⟨⟨-214471, 16⟩, ⟨-92295, 15⟩⟩,
  ⟨⟨-46147, 14⟩, ⟨-319059, 17⟩⟩,
  ⟨⟨-319055, 17⟩, ⟨-276699, 17⟩⟩,
  ⟨⟨-34587, 14⟩, ⟨-240649, 17⟩⟩,
  ⟨⟨-481293, 18⟩, ⟨-52443, 15⟩⟩,
  ⟨⟨-419539, 18⟩, ⟨-183175, 17⟩⟩,
  ⟨⟨-183173, 17⟩, ⟨-320291, 18⟩⟩,
  ⟨⟨-10009, 13⟩, ⟨-140113, 17⟩⟩,
  ⟨⟨-280223, 18⟩, ⟨-490463, 19⟩⟩,
  ⟨⟨-245229, 18⟩, ⟨-429111, 19⟩⟩,
  ⟨⟨-429107, 19⟩, ⟨-187581, 18⟩⟩,
  ⟨⟨-187579, 18⟩, ⟨-327595, 19⟩⟩,
  ⟨⟨-327591, 19⟩, ⟨-142781, 18⟩⟩,
  ⟨⟨-285559, 19⟩, ⟨-62089, 17⟩⟩,
  ⟨⟨-248353, 19⟩, ⟨-430771, 20⟩⟩,
  ⟨⟨-215383, 19⟩, ⟨-372287, 20⟩⟩,
  ⟨⟨-372283, 20⟩, ⟨-160207, 19⟩⟩,
  ⟨⟨-160205, 19⟩, ⟨-274423, 20⟩⟩,
  ⟨⟨-274419, 20⟩, ⟨-467383, 21⟩⟩,
  ⟨⟨-467377, 21⟩, ⟨-197685, 20⟩⟩,
  ⟨⟨-395365, 21⟩, ⟨-331883, 21⟩⟩,
  ⟨⟨-165939, 20⟩, ⟨-276107, 21⟩⟩,
  ⟨⟨-276103, 21⟩, ⟨-227333, 21⟩⟩,
  ⟨⟨-454659, 22⟩, ⟨-184935, 21⟩⟩,
  ⟨⟨-46233, 19⟩, ⟨-296701, 22⟩⟩,
  ⟨⟨-37087, 19⟩, ⟨-468287, 23⟩⟩,
  ⟨⟨-468279, 23⟩, ⟨-362507, 23⟩⟩,
  ⟨⟨-90625, 21⟩, ⟨-17145, 19⟩⟩,
  ⟨⟨-274315, 23⟩, ⟨-404103, 24⟩⟩,
  ⟨⟨-404095, 24⟩, ⟨-288135, 24⟩⟩,
  ⟨⟨-2251, 17⟩, ⟨-98763, 23⟩⟩,
  ⟨⟨-197521, 24⟩, ⟨-516131, 26⟩⟩,
  ⟨⟨-516117, 26⟩, ⟨-39689, 23⟩⟩,
  ⟨⟨-158751, 25⟩, ⟨-181069, 26⟩⟩,
  ⟨⟨-181063, 26⟩, ⟨-93653, 26⟩⟩,
  ⟨⟨-187299, 27⟩, ⟨-340713, 29⟩⟩,
  ⟨⟨-170349, 28⟩, ⟨-520689, 31⟩⟩,
  ⟨⟨-520663, 31⟩, ⟨-77925, 30⟩⟩,
  ⟨⟨-155841, 31⟩, ⟨-261153, 34⟩⟩,
  ⟨⟨-16321, 30⟩, ⟨-504067, 38⟩⟩,
  ⟨⟨-504031, 38⟩, ⟨-387849, 42⟩⟩,
  ⟨⟨-387819, 42⟩, ⟨-26897, 45⟩⟩,
  ⟨⟨-107579, 47⟩, ⟨-322295, 61⟩⟩,
  ⟨⟨-40283, 58⟩, ⟨-262149, 91⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private def eulerianCoefficients : List ℤ := [
  0x1, 0x1ffffffffffffffffb6, 0xd043522b5b0335b36c5a15b7dee70,
  0x3fffffc3cc8a3f7656327a22adf5b8d9b232a, 0x2d47326ba931b78da4de9c0b03c57dc2c7f521df90e, 0x1a0798dbf7fa784b4f49cf4ae774350386b8d785c170954a,
  0x1e99f33e864b01066c01fbd2aa7edb0a6616b472515056fade70, 0x7f72665848a18dc6fdfe75970e10e129bfa631532817dacefe62996, 0xa71eba4e8fc02d1da9d8c784b2eff44942052eb6b49bdb3fb55bba9e99,
  0x5784342b3b37b7171e993dfd5aeefd92e57cb929c2a89d99c084770f13630, 0x15a1716a1309a3519fda5c1a0d90a13fb93116165451e082b9f94d149a65e280, 0x2d942b37bbc862d9fd0b5b2ec0ec290458111aa6029ee4eb40fde2e9b5e8e5d2d0,
  0x3805cb5a6ae040fa51fec72e58c393462a5d4e89230f5937299cf12b041982d1e3d0, 0x2b0b8f7717084905195d0976c7508729b558e4018734f39e6345c2a5102a1e6c9a1f10, 0x15d287f561377ac08ac73ffbdf709d4bd49d8b8a9fd6cde0337b2688541dcd4fa8510a80,
  0x79ea94ccfdd295de8978ddf4a8502156fa98ee092e148178a990fda017759edde41a751f0, 0x1e5aa9a84bc6e37fdcb6a105cceac064bb32053af85a981c12bdff6e5ac10cd2d828cf725f4, 0x58b3c250cc9002e3127cfa145aa81cbbb5acc0f2c291cc973483d069783f76dfee0137a95d88,
  0xc2ab60b638beb52b67dc742bc90d89720ab0cc22816a75e293dc7bae00d0cd6970469186c6840, 0x1473a08b0edb2a6845ffe1800a5412fc5a9eb9999eec34b5714eefa2c10dd1effe68e3633db9ef8, 0x1ac5869fb81e3752ff60acc8bbf624bd3fcf4f15b08e2e9104d815dab202cb62c385b7282f563e08,
  0x1bada536a908cbfbb3cef24813ed7d4372a58bc54e2d5d7ec78ed0e03d0bdd1d7b580f005975e68b8, 0x16e0027f6f300fb475f4f306cddac77abb73012b32257b21147e9d7a80ec4acad04e5e339bba2ee840, 0xf451ec86b009b1678913a9317b2d689bf9d50d014c84e4967f5b2e82179ef14cf5c3d7918b1e25dbc8,
  0x84e9ae94b6278f4e168cc53dc5dbda8c28112f97a270528fb7b886b66f38a3bcfc709b2a5dd5cb04684, 0x3b61ad7e13a087da041a2f1896a75679aec2c1fb78aa89e0ef4d1e569cb44f1683cfeedbc56443ed7a10, 0x15eeec3bdc7076ffd1f92b62047a6967ccfbacb5b3a3f2848b39459c005aa77ce3ef3d49ebadfef03e980,
  0x6bc7aef00265c12e82bf0b1dbdf5b6c9cb4b97f69fb7f706a3f23908699b75f79a1f73f5df03a5dfeecf0, 0x1ba91b589a88ab919ecc803ee176e369659ccf60a5caa0d591c1ae50d821d5481892ca410fbed78e8d54b0, 0x5f4ffca4078eb20bdcf88e5d1a98964ad1c1d171dcc8f47793694263f07b11147359a7131cf7090d812c30,
  0x114980dc62f064f1d13fbcf110b12057f69ac6e631b35c55b0773337c606575d26759a65fa45b61b95db180, 0x2a606ef58081be5480e71ac7799d6204497d2ebd74ca01dc192552d77e04811f3fd56e16be92b9734a702d0, 0x57f76da6ac2a4924713cbadb3add72a265ab6f0c9329f42878d8ad631d225a1f8ca6d13e7ff7743ce56f4ee,
  0x9aefa4ca1d9df2ab987eb2c1969c9f78b2015368392b143708a3ddb36bc32b8d34d503617d96051cc039864, 0xe7e4bbea75ff720fe20af748f627adbabbba6fe9ee3603e049622cf9a7970b453d7175b890780638fd35aa0, 0x1273f833308c5d6765e23a98ab8a9fbfb090188c47952340364a5c8f2c0961edbc50dd4efb798b1ee7d434dc,
  0x13ffae4fdd3714179deb0004f0e25618d4ee573a2158cb332ca1832afcd8a56e4b0b27cc28119e1cb2e720d4, 0x1273f833308c5d6765e23a98ab8a9fbfb090188c47952340364a5c8f2c0961edbc50dd4efb798b1ee7d434dc, 0xe7e4bbea75ff720fe20af748f627adbabbba6fe9ee3603e049622cf9a7970b453d7175b890780638fd35aa0,
  0x9aefa4ca1d9df2ab987eb2c1969c9f78b2015368392b143708a3ddb36bc32b8d34d503617d96051cc039864, 0x57f76da6ac2a4924713cbadb3add72a265ab6f0c9329f42878d8ad631d225a1f8ca6d13e7ff7743ce56f4ee, 0x2a606ef58081be5480e71ac7799d6204497d2ebd74ca01dc192552d77e04811f3fd56e16be92b9734a702d0,
  0x114980dc62f064f1d13fbcf110b12057f69ac6e631b35c55b0773337c606575d26759a65fa45b61b95db180, 0x5f4ffca4078eb20bdcf88e5d1a98964ad1c1d171dcc8f47793694263f07b11147359a7131cf7090d812c30, 0x1ba91b589a88ab919ecc803ee176e369659ccf60a5caa0d591c1ae50d821d5481892ca410fbed78e8d54b0,
  0x6bc7aef00265c12e82bf0b1dbdf5b6c9cb4b97f69fb7f706a3f23908699b75f79a1f73f5df03a5dfeecf0, 0x15eeec3bdc7076ffd1f92b62047a6967ccfbacb5b3a3f2848b39459c005aa77ce3ef3d49ebadfef03e980, 0x3b61ad7e13a087da041a2f1896a75679aec2c1fb78aa89e0ef4d1e569cb44f1683cfeedbc56443ed7a10,
  0x84e9ae94b6278f4e168cc53dc5dbda8c28112f97a270528fb7b886b66f38a3bcfc709b2a5dd5cb04684, 0xf451ec86b009b1678913a9317b2d689bf9d50d014c84e4967f5b2e82179ef14cf5c3d7918b1e25dbc8, 0x16e0027f6f300fb475f4f306cddac77abb73012b32257b21147e9d7a80ec4acad04e5e339bba2ee840,
  0x1bada536a908cbfbb3cef24813ed7d4372a58bc54e2d5d7ec78ed0e03d0bdd1d7b580f005975e68b8, 0x1ac5869fb81e3752ff60acc8bbf624bd3fcf4f15b08e2e9104d815dab202cb62c385b7282f563e08, 0x1473a08b0edb2a6845ffe1800a5412fc5a9eb9999eec34b5714eefa2c10dd1effe68e3633db9ef8,
  0xc2ab60b638beb52b67dc742bc90d89720ab0cc22816a75e293dc7bae00d0cd6970469186c6840, 0x58b3c250cc9002e3127cfa145aa81cbbb5acc0f2c291cc973483d069783f76dfee0137a95d88, 0x1e5aa9a84bc6e37fdcb6a105cceac064bb32053af85a981c12bdff6e5ac10cd2d828cf725f4,
  0x79ea94ccfdd295de8978ddf4a8502156fa98ee092e148178a990fda017759edde41a751f0, 0x15d287f561377ac08ac73ffbdf709d4bd49d8b8a9fd6cde0337b2688541dcd4fa8510a80, 0x2b0b8f7717084905195d0976c7508729b558e4018734f39e6345c2a5102a1e6c9a1f10,
  0x3805cb5a6ae040fa51fec72e58c393462a5d4e89230f5937299cf12b041982d1e3d0, 0x2d942b37bbc862d9fd0b5b2ec0ec290458111aa6029ee4eb40fde2e9b5e8e5d2d0, 0x15a1716a1309a3519fda5c1a0d90a13fb93116165451e082b9f94d149a65e280,
  0x5784342b3b37b7171e993dfd5aeefd92e57cb929c2a89d99c084770f13630, 0xa71eba4e8fc02d1da9d8c784b2eff44942052eb6b49bdb3fb55bba9e99, 0x7f72665848a18dc6fdfe75970e10e129bfa631532817dacefe62996,
  0x1e99f33e864b01066c01fbd2aa7edb0a6616b472515056fade70, 0x1a0798dbf7fa784b4f49cf4ae774350386b8d785c170954a, 0x2d47326ba931b78da4de9c0b03c57dc2c7f521df90e,
  0x3fffffc3cc8a3f7656327a22adf5b8d9b232a, 0xd043522b5b0335b36c5a15b7dee70, 0x1ffffffffffffffffb6,
  0x1]

private theorem eulerianCoefficients_eq : descentCoeffs 73 = eulerianCoefficients := by
  decide +kernel

private theorem upper : upperOK (descentCoeffs 73) first gaps = true := by
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

private theorem lower (i : Fin (lastRepresentative 74 - 2)) :
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

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 74) :
    StrictNegativeInterlacing (originalQuotient 74 k) (eulerian 73) 71 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N074
