import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentPackedData.C127L080.N076

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N076

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L080.N076 LongCycleBounds.DescentNecklace.Packed.C127L080.N076.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L080.N076 LongCycleBounds.DescentNecklace.Packed.C127L080.N076.rows

private theorem actual : RepresentativeChecks 76 previousNodes rows :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L080.N076 LongCycleBounds.DescentNecklace.Packed.C127L080.N076.dataChecks

private def first : LongCycleFinite.Dyadic := ⟨-37778931862957161709568, 0⟩

private def gaps : List Window := [
  ⟨⟨-37777706883858516934656, 0⟩, ⟨-16171256512512, 0⟩⟩,
  ⟨⟨-15071711330304, 0⟩, ⟨-2497560576, 0⟩⟩,
  ⟨⟨-1846194176, 0⟩, ⟨-17800128, 0⟩⟩,
  ⟨⟨-17688256, 0⟩, ⟨-790112, 0⟩⟩,
  ⟨⟨-789282, 0⟩, ⟨-360811, 2⟩⟩,
  ⟨⟨-360669, 2⟩, ⟨-72619, 2⟩⟩,
  ⟨⟨-18151, 0⟩, ⟨-10545, 1⟩⟩,
  ⟨⟨-337395, 6⟩, ⟨-503703, 8⟩⟩,
  ⟨⟨-62957, 5⟩, ⟨-112401, 7⟩⟩,
  ⟨⟨-449573, 9⟩, ⟨-114511, 8⟩⟩,
  ⟨⟨-458019, 10⟩, ⟨-515901, 11⟩⟩,
  ⟨⟨-257939, 10⟩, ⟨-314069, 11⟩⟩,
  ⟨⟨-314057, 11⟩, ⟨-406743, 12⟩⟩,
  ⟨⟨-203365, 11⟩, ⟨-276765, 12⟩⟩,
  ⟨⟨-276757, 12⟩, ⟨-392213, 13⟩⟩,
  ⟨⟨-392203, 13⟩, ⟨-287341, 13⟩⟩,
  ⟨⟨-143667, 12⟩, ⟨-108227, 12⟩⟩,
  ⟨⟨-432899, 14⟩, ⟨-20865, 10⟩⟩,
  ⟨⟨-166917, 13⟩, ⟨-65649, 12⟩⟩,
  ⟨⟨-262591, 14⟩, ⟨-420165, 15⟩⟩,
  ⟨⟨-210079, 14⟩, ⟨-341049, 15⟩⟩,
  ⟨⟨-341043, 15⟩, ⟨-70077, 13⟩⟩,
  ⟨⟨-280303, 15⟩, ⟨-58221, 13⟩⟩,
  ⟨⟨-232881, 15⟩, ⟨-6103, 10⟩⟩,
  ⟨⟨-390587, 16⟩, ⟨-165103, 15⟩⟩,
  ⟨⟨-330201, 16⟩, ⟨-281121, 16⟩⟩,
  ⟨⟨-281117, 16⟩, ⟨-15049, 12⟩⟩,
  ⟨⟨-240781, 16⟩, ⟨-12957, 12⟩⟩,
  ⟨⟨-414619, 17⟩, ⟨-179295, 16⟩⟩,
  ⟨⟨-358585, 17⟩, ⟨-77827, 15⟩⟩,
  ⟨⟨-38913, 14⟩, ⟨-271121, 17⟩⟩,
  ⟨⟨-135559, 16⟩, ⟨-473485, 18⟩⟩,
  ⟨⟨-59185, 15⟩, ⟨-414313, 18⟩⟩,
  ⟨⟨-414309, 18⟩, ⟨-363115, 18⟩⟩,
  ⟨⟨-363111, 18⟩, ⟨-318603, 18⟩⟩,
  ⟨⟨-318599, 18⟩, ⟨-139867, 17⟩⟩,
  ⟨⟨-279731, 18⟩, ⟨-122831, 17⟩⟩,
  ⟨⟨-491319, 19⟩, ⟨-53923, 16⟩⟩,
  ⟨⟨-107845, 17⟩, ⟨-47313, 16⟩⟩,
  ⟨⟨-94625, 17⟩, ⟨-331733, 19⟩⟩,
  ⟨⟨-331729, 19⟩, ⟨-290275, 19⟩⟩,
  ⟨⟨-290271, 19⟩, ⟨-253467, 19⟩⟩,
  ⟨⟨-506929, 20⟩, ⟨-441495, 20⟩⟩,
  ⟨⟨-220745, 19⟩, ⟨-23955, 16⟩⟩,
  ⟨⟨-95819, 18⟩, ⟨-41435, 17⟩⟩,
  ⟨⟨-82869, 18⟩, ⟨-71351, 18⟩⟩,
  ⟨⟨-35675, 17⟩, ⟨-488907, 21⟩⟩,
  ⟨⟨-488901, 21⟩, ⟨-208113, 20⟩⟩,
  ⟨⟨-416221, 21⟩, ⟨-43985, 18⟩⟩,
  ⟨⟨-87969, 19⟩, ⟨-73771, 19⟩⟩,
  ⟨⟨-36885, 18⟩, ⟨-490321, 22⟩⟩,
  ⟨⟨-245157, 21⟩, ⟨-402993, 22⟩⟩,
  ⟨⟨-402987, 22⟩, ⟨-40889, 19⟩⟩,
  ⟨⟨-327107, 22⟩, ⟨-261697, 22⟩⟩,
  ⟨⟨-261693, 22⟩, ⟨-205849, 22⟩⟩,
  ⟨⟨-411691, 23⟩, ⟨-79371, 21⟩⟩,
  ⟨⟨-158739, 22⟩, ⟨-239159, 23⟩⟩,
  ⟨⟨-478309, 24⟩, ⟨-175215, 23⟩⟩,
  ⟨⟨-175211, 23⟩, ⟨-496601, 25⟩⟩,
  ⟨⟨-248295, 24⟩, ⟨-168959, 24⟩⟩,
  ⟨⟨-168955, 24⟩, ⟨-437617, 26⟩⟩,
  ⟨⟨-109401, 24⟩, ⟨-133209, 25⟩⟩,
  ⟨⟨-266409, 26⟩, ⟨-37509, 24⟩⟩,
  ⟨⟨-300061, 27⟩, ⟨-305701, 28⟩⟩,
  ⟨⟨-305689, 28⟩, ⟨-68221, 27⟩⟩,
  ⟨⟨-34109, 26⟩, ⟨-203671, 30⟩⟩,
  ⟨⟨-407321, 31⟩, ⟨-236603, 32⟩⟩,
  ⟨⟨-473179, 33⟩, ⟨-47629, 32⟩⟩,
  ⟨⟨-381007, 35⟩, ⟨-174067, 37⟩⟩,
  ⟨⟨-348109, 38⟩, ⟨-494725, 43⟩⟩,
  ⟨⟨-494687, 43⟩, ⟨-483651, 50⟩⟩,
  ⟨⟨-241805, 49⟩, ⟨-71619, 60⟩⟩,
  ⟨⟨-17903, 58⟩, ⟨-262149, 93⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private def eulerianCoefficients : List ℤ := [
  0x1, 0x7ffffffffffffffffb4, 0x7525de386605ce34ecf2ac376d0e1d,
  0x3fffffdd38c207415ad6c849a7f4df8ba20ae0, 0x46bf48b038555da611ff009b695354371f8651e693d2, 0x3a919f0f6d35db9551e7d097978034b3123ae4f2ab2b55418,
  0x5dbd20d95c228da44bc0cc4813fb0d78b6ad8e636634156d86c12, 0x1fe4293ccdeea1ccb21799e7bda3dbb1586b1e6bf5efdbcc9d2ca40e0, 0x3503e3faf1212b38f8f863101c32eec2f6770c594ed86887bf8229063875,
  0x22626e6e8f13625698a69fc76ddb91b92a1bcfc847e682dc1bb43d3e56f7694, 0xa56477503eacc0eed3b498090fe6084db65fcd5dad0a175a3178fa8b738e42379, 0x1a1f0c8e5ec085c9c2f12b38cf178ed90e88b06c11fc06615bb531f386e2a1b95700,
  0x26133caa61fb60b8d347a82061ce297aea75e767288150af97adeda20fc1342c744ff0, 0x2262cbcea4e03dba2ae826f1064b448501b7fdfb40e8a165ab0fba96768c243489f27c40, 0x145824ffd92acd1d175f587f745440307149d875437b7a59503634af9e49309e4583fb5870,
  0x83e371ab4d820e29e56e5c481e0cc1ee29b93e3bbbe1cb31f6f36f090a673e90be146666300, 0x25ee07c87a768b277a2485f633500371bed29dfe0a93234d1fb09ccc9ca0c8cd86e23d0695a54, 0x7f90abad637aac1b0815499ea654502e6e91c65e74c91f7e7e04eb523dffead9b4a42d13795f90,
  0x14147a10aa14fa0209c850ebdfbe3cdced7125ba4e870bb05a5f789f6f7af9fc5720e402ea3d4844, 0x26a62527916abc989623eb8d89d84cce255178c155dc01e8a4196f1f59448da6603f30bfd56436280, 0x39d59a0a18b99ea6c5799d42cd034bb437a1f66888ae3626f6ea3e1df86374325ba1c8a713af15f838,
  0x4445abc4372cd1a7c69721ba93ae1d9d0bcddce38f87d5f20281004f1abe812bc42ab4b39022af20ca0, 0x4060a8f1288746a1fb038c6fc6755969c2e685deaed2a4968c6b85a540477e98e765fe85f051c14ec3b8, 0x3103b8ddcc8bef248092f63fd3c4618c4acc9cd9482d1450006075932c82c26ead88a996e902eadcc1680,
  0x1e6971e4bf6d5649dd6608930552c4b2b43407b9a1a73eb2277c99abad38bb47dea2718985d5174acfd554, 0xf806dd7ee261e5f2885106e805b501b6c25ea3e2bbaa4cbe55114f91cf43f3e99c2f82ded9e1d3a2c3dcd0, 0x68961be0128d4522b322f89cd4a407c76c836af7324e5dd48885f409ca1deb49d50438e56d36963e174ae24,
  0x24b443ba8b78d6a333d1a1b2d002f9be5885cecaea9e81883393589f62f2e7aa937ca46d2d2aedf5e9ea9d00, 0xac6dc5ab23ca77ea71321bd53d3fedf017f3684a2dedaa89e2fc6ee8194b3dcff47e09d35ccd34a1bfedbc10, 0x2a8c417051bffa1c8b8cd1690b2bd1851ce0b3fcebe6db310b49a8ef58c01efdcf088ef89175efa3efb01adc0,
  0x8db917167cd088fb0cdc6fc076bf9bcd534367536a73f1bcfc5b669fae6f93274ef3d20aa4e9a96e8a018aa90, 0x18f9541765c8e63e5d2ac18ac0eaf7547fe89efcc7076bb420dfddbf028380ea0a97dd0de7dadca33cbbb93900, 0x3bc43da4e8571f9b64cc61973dd135ac26782c44129096597b8eb5a4969cf877b26cdbe06cf182a9a2a783460e,
  0x79ae58b724cd67194e28410dd6158805e16423ca0a9021380a09a1ed36355651391d0161ba9e7a7398c7574d58, 0xd3240babe4662dd9b1a8d0b3a8535608a30ac4e0777271f6aa4fa0566ab60700aa0342731963d8bd65c29829d6, 0x138b00a865a9f6a7bdad8c84135c5a0b3a86561f7c50a5081dc74ec78cd01e33dd84c8188870c148e340fc0ab40,
  0x18b9b9d92b9516efe45b31cbdbf0217dc0a1229187413ca63f6d7f73fe04d1035ba7f36ce8fbfe9683eec08352c, 0x1abd8c6b6bd987e69e0017940952a03e342c39b110dd5cdb282b500fb5a2591e974bec9c98d14ae37e474c0ea90, 0x18b9b9d92b9516efe45b31cbdbf0217dc0a1229187413ca63f6d7f73fe04d1035ba7f36ce8fbfe9683eec08352c,
  0x138b00a865a9f6a7bdad8c84135c5a0b3a86561f7c50a5081dc74ec78cd01e33dd84c8188870c148e340fc0ab40, 0xd3240babe4662dd9b1a8d0b3a8535608a30ac4e0777271f6aa4fa0566ab60700aa0342731963d8bd65c29829d6, 0x79ae58b724cd67194e28410dd6158805e16423ca0a9021380a09a1ed36355651391d0161ba9e7a7398c7574d58,
  0x3bc43da4e8571f9b64cc61973dd135ac26782c44129096597b8eb5a4969cf877b26cdbe06cf182a9a2a783460e, 0x18f9541765c8e63e5d2ac18ac0eaf7547fe89efcc7076bb420dfddbf028380ea0a97dd0de7dadca33cbbb93900, 0x8db917167cd088fb0cdc6fc076bf9bcd534367536a73f1bcfc5b669fae6f93274ef3d20aa4e9a96e8a018aa90,
  0x2a8c417051bffa1c8b8cd1690b2bd1851ce0b3fcebe6db310b49a8ef58c01efdcf088ef89175efa3efb01adc0, 0xac6dc5ab23ca77ea71321bd53d3fedf017f3684a2dedaa89e2fc6ee8194b3dcff47e09d35ccd34a1bfedbc10, 0x24b443ba8b78d6a333d1a1b2d002f9be5885cecaea9e81883393589f62f2e7aa937ca46d2d2aedf5e9ea9d00,
  0x68961be0128d4522b322f89cd4a407c76c836af7324e5dd48885f409ca1deb49d50438e56d36963e174ae24, 0xf806dd7ee261e5f2885106e805b501b6c25ea3e2bbaa4cbe55114f91cf43f3e99c2f82ded9e1d3a2c3dcd0, 0x1e6971e4bf6d5649dd6608930552c4b2b43407b9a1a73eb2277c99abad38bb47dea2718985d5174acfd554,
  0x3103b8ddcc8bef248092f63fd3c4618c4acc9cd9482d1450006075932c82c26ead88a996e902eadcc1680, 0x4060a8f1288746a1fb038c6fc6755969c2e685deaed2a4968c6b85a540477e98e765fe85f051c14ec3b8, 0x4445abc4372cd1a7c69721ba93ae1d9d0bcddce38f87d5f20281004f1abe812bc42ab4b39022af20ca0,
  0x39d59a0a18b99ea6c5799d42cd034bb437a1f66888ae3626f6ea3e1df86374325ba1c8a713af15f838, 0x26a62527916abc989623eb8d89d84cce255178c155dc01e8a4196f1f59448da6603f30bfd56436280, 0x14147a10aa14fa0209c850ebdfbe3cdced7125ba4e870bb05a5f789f6f7af9fc5720e402ea3d4844,
  0x7f90abad637aac1b0815499ea654502e6e91c65e74c91f7e7e04eb523dffead9b4a42d13795f90, 0x25ee07c87a768b277a2485f633500371bed29dfe0a93234d1fb09ccc9ca0c8cd86e23d0695a54, 0x83e371ab4d820e29e56e5c481e0cc1ee29b93e3bbbe1cb31f6f36f090a673e90be146666300,
  0x145824ffd92acd1d175f587f745440307149d875437b7a59503634af9e49309e4583fb5870, 0x2262cbcea4e03dba2ae826f1064b448501b7fdfb40e8a165ab0fba96768c243489f27c40, 0x26133caa61fb60b8d347a82061ce297aea75e767288150af97adeda20fc1342c744ff0,
  0x1a1f0c8e5ec085c9c2f12b38cf178ed90e88b06c11fc06615bb531f386e2a1b95700, 0xa56477503eacc0eed3b498090fe6084db65fcd5dad0a175a3178fa8b738e42379, 0x22626e6e8f13625698a69fc76ddb91b92a1bcfc847e682dc1bb43d3e56f7694,
  0x3503e3faf1212b38f8f863101c32eec2f6770c594ed86887bf8229063875, 0x1fe4293ccdeea1ccb21799e7bda3dbb1586b1e6bf5efdbcc9d2ca40e0, 0x5dbd20d95c228da44bc0cc4813fb0d78b6ad8e636634156d86c12,
  0x3a919f0f6d35db9551e7d097978034b3123ae4f2ab2b55418, 0x46bf48b038555da611ff009b695354371f8651e693d2, 0x3fffffdd38c207415ad6c849a7f4df8ba20ae0,
  0x7525de386605ce34ecf2ac376d0e1d, 0x7ffffffffffffffffb4, 0x1]

private theorem eulerianCoefficients_eq : descentCoeffs 75 = eulerianCoefficients := by
  decide +kernel

private theorem upper : upperOK (descentCoeffs 75) first gaps = true := by
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

private theorem lower (i : Fin (lastRepresentative 76 - 2)) :
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

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 76) :
    StrictNegativeInterlacing (originalQuotient 76 k) (eulerian 75) 73 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N076
