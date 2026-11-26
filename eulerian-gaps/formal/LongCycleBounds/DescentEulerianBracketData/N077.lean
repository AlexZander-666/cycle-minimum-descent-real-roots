import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentPackedData.C127L080.N077

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N077

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L080.N077 LongCycleBounds.DescentNecklace.Packed.C127L080.N077.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L080.N077 LongCycleBounds.DescentNecklace.Packed.C127L080.N077.rows

private theorem actual : RepresentativeChecks 77 previousNodes rows :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L080.N077 LongCycleBounds.DescentNecklace.Packed.C127L080.N077.dataChecks

private def first : LongCycleFinite.Dyadic := ⟨-75557863725914323419136, 0⟩

private def gaps : List Window := [
  ⟨⟨-75555413767717033869312, 0⟩, ⟨-24417493057536, 0⟩⟩,
  ⟨⟨-22218402693120, 0⟩, ⟨-3125207040, 0⟩⟩,
  ⟨⟨-2171871232, 0⟩, ⟨-22345920, 0⟩⟩,
  ⟨⟨-22214400, 0⟩, ⟨-950094, 0⟩⟩,
  ⟨⟨-949058, 0⟩, ⟨-105598, 0⟩⟩,
  ⟨⟨-105555, 0⟩, ⟨-83339, 2⟩⟩,
  ⟨⟨-333285, 4⟩, ⟨-95361, 4⟩⟩,
  ⟨⟨-381393, 6⟩, ⟨-140675, 6⟩⟩,
  ⟨⟨-281323, 7⟩, ⟨-124389, 7⟩⟩,
  ⟨⟨-497521, 9⟩, ⟨-503051, 10⟩⟩,
  ⟨⟨-503023, 10⟩, ⟨-281515, 10⟩⟩,
  ⟨⟨-140751, 9⟩, ⟨-340967, 11⟩⟩,
  ⟨⟨-170477, 10⟩, ⟨-439613, 12⟩⟩,
  ⟨⟨-439599, 12⟩, ⟨-149011, 11⟩⟩,
  ⟨⟨-298013, 12⟩, ⟨-105247, 11⟩⟩,
  ⟨⟨-420977, 13⟩, ⟨-153795, 12⟩⟩,
  ⟨⟨-153791, 12⟩, ⟨-231171, 13⟩⟩,
  ⟨⟨-115583, 12⟩, ⟨-355835, 14⟩⟩,
  ⟨⟨-88957, 12⟩, ⟨-279435, 14⟩⟩,
  ⟨⟨-139715, 13⟩, ⟨-223241, 14⟩⟩,
  ⟨⟨-446475, 15⟩, ⟨-361989, 15⟩⟩,
  ⟨⟨-361983, 15⟩, ⟨-297241, 15⟩⟩,
  ⟨⟨-74309, 13⟩, ⟨-246765, 15⟩⟩,
  ⟨⟨-493523, 16⟩, ⟨-206821, 15⟩⟩,
  ⟨⟨-103409, 14⟩, ⟨-349561, 16⟩⟩,
  ⟨⟨-87389, 14⟩, ⟨-297531, 16⟩⟩,
  ⟨⟨-297527, 16⟩, ⟨-254823, 16⟩⟩,
  ⟨⟨-63705, 14⟩, ⟨-6857, 11⟩⟩,
  ⟨⟨-219421, 16⟩, ⟨-23727, 13⟩⟩,
  ⟨⟨-379627, 17⟩, ⟨-329709, 17⟩⟩,
  ⟨⟨-164853, 16⟩, ⟨-287309, 17⟩⟩,
  ⟨⟨-287305, 17⟩, ⟨-15691, 13⟩⟩,
  ⟨⟨-502107, 18⟩, ⟨-439751, 18⟩⟩,
  ⟨⟨-219873, 17⟩, ⟨-385815, 18⟩⟩,
  ⟨⟨-385811, 18⟩, ⟨-338939, 18⟩⟩,
  ⟨⟨-42367, 15⟩, ⟨-298017, 18⟩⟩,
  ⟨⟨-298013, 18⟩, ⟨-131073, 17⟩⟩,
  ⟨⟨-262143, 18⟩, ⟨-3603, 12⟩⟩,
  ⟨⟨-461179, 19⟩, ⟨-405501, 19⟩⟩,
  ⟨⟨-405497, 19⟩, ⟨-356233, 19⟩⟩,
  ⟨⟨-356229, 19⟩, ⟨-312543, 19⟩⟩,
  ⟨⟨-78135, 17⟩, ⟨-136863, 18⟩⟩,
  ⟨⟨-136861, 18⟩, ⟨-239187, 19⟩⟩,
  ⟨⟨-478369, 20⟩, ⟨-416855, 20⟩⟩,
  ⟨⟨-416851, 20⟩, ⟨-90509, 18⟩⟩,
  ⟨⟨-22627, 16⟩, ⟨-313185, 20⟩⟩,
  ⟨⟨-313181, 20⟩, ⟨-269679, 20⟩⟩,
  ⟨⟨-269675, 20⟩, ⟨-230969, 20⟩⟩,
  ⟨⟨-115483, 19⟩, ⟨-393183, 21⟩⟩,
  ⟨⟨-196589, 20⟩, ⟨-83067, 19⟩⟩,
  ⟨⟨-41533, 18⟩, ⟨-278485, 21⟩⟩,
  ⟨⟨-278481, 21⟩, ⟨-231197, 21⟩⟩,
  ⟨⟨-115597, 20⟩, ⟨-379681, 22⟩⟩,
  ⟨⟨-379675, 22⟩, ⟨-153917, 21⟩⟩,
  ⟨⟨-307829, 22⟩, ⟨-122965, 21⟩⟩,
  ⟨⟨-122963, 21⟩, ⟨-193125, 22⟩⟩,
  ⟨⟨-386243, 23⟩, ⟨-148637, 22⟩⟩,
  ⟨⟨-74317, 21⟩, ⟨-223421, 23⟩⟩,
  ⟨⟨-446833, 24⟩, ⟨-163239, 23⟩⟩,
  ⟨⟨-163235, 23⟩, ⟨-461187, 25⟩⟩,
  ⟨⟨-57647, 22⟩, ⟨-312645, 25⟩⟩,
  ⟨⟨-78159, 23⟩, ⟨-201549, 25⟩⟩,
  ⟨⟨-201543, 25⟩, ⟨-488233, 27⟩⟩,
  ⟨⟨-244109, 26⟩, ⟨-273227, 27⟩⟩,
  ⟨⟨-273217, 27⟩, ⟨-276233, 28⟩⟩,
  ⟨⟨-276221, 28⟩, ⟨-244273, 29⟩⟩,
  ⟨⟨-488525, 30⟩, ⟨-360371, 31⟩⟩,
  ⟨⟨-11261, 26⟩, ⟨-103091, 31⟩⟩,
  ⟨⟨-103085, 31⟩, ⟨-325483, 35⟩⟩,
  ⟨⟨-325461, 35⟩, ⟨-144681, 37⟩⟩,
  ⟨⟨-289341, 38⟩, ⟨-395137, 43⟩⟩,
  ⟨⟨-197553, 42⟩, ⟨-90641, 48⟩⟩,
  ⟨⟨-362533, 50⟩, ⟨-381961, 63⟩⟩,
  ⟨⟨-190963, 62⟩, ⟨-262165, 94⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private def eulerianCoefficients : List ℤ := [
  0x1, 0xfffffffffffffffffb3, 0x15f719aa934616a9ec6d804a647145f,
  0xffffff964ad47b1a8302ee3e310699fca131c5, 0x161bc7d7119a10c34ec05649576f55c507c7edf13f21a, 0x15f6af44d61d11f7abaffd3691fb2df943315f9940e732f7ce,
  0x2903be9c30329bc381d19fb5b9550cb5b67b5e0d265c763d7ff30e, 0xff3a8de04a0ae3b5be053a34fc8c403564e2302710496a6eafea727da, 0x1ddaa8d81bc95bb3066b05fdf16b05d405be736651070e82be12f6ef1379d,
  0x158b6509c41939246f514cde91e09c683757e305684fb46cecd7c557b2fb6867, 0x7242e80eb324f499d6c1d7d951934f6e892f8fe9811f86e9cdf573bc80988a185b, 0x13c147ed12704e344ed8a145359eb48ae6a1d2a43245f458f2ae752e42925069d15b9,
  0x1f581d7ca91740ad52b5fd4732b3dfef42b9eec5813101a830ac25db7ae884eb03dcf30, 0x1eac5e13af2603cfbd4b0c38e502f7b7b57c2e7afefb0a66a913001b55d8a86b67be27790, 0x1397e1859c57053a774fa68e63075fd6ed9be3e61cdf48252529ae57ab6ffca0acc24744610,
  0x88bc727c44414109d400145e7cc4d539b4b7d6cfacf637593f105996e31eaf2674a4d94a42b0, 0x2a3b7d2f44809b8f0ee32c2fa4f5b38017dc3e874b3ce43bed09b779c851d884fe192d56fe3394, 0x98409cee442353b0823e5db238f24aff735e8993cfd22c9114133cdfadd8f67c494ed6c66d0897c,
  0x19a6bd621e8185924d9b2d42f8ccd9e902472d3c53a7b6f395da31125e82c88efca5e1e6dcc0c03ac, 0x34c83d9f2ba417692fda8075711fbb8edf84085826cf13fd113f0cc2af6812b927b54fb470e4e8c924, 0x545cb24de842f97c440779eea33ba429a12e65d37e2cc77e07f901d63189877e7d522a054083b8ae898,
  0x6a4cb045f72d815c857cef29e51b1dfba82edba95ab833cf227db3c535234f92ff6a7a92cb6a4e8569c8, 0x6af1a5160de5e9c23cb8fafe086f6ac728a8cd081b9573b97661c62e3c0af53b08039ffe69dcd6d223f48, 0x56d99846a035e85649d42d72e1bcddd5558ca4fd06753a8b2ba2f307f912f0dbac351c1418454d5070a118,
  0x3979838278a74366d40d476aaf553727b8c2dbee2f3e7a169dc647fe23b3341ec71d93d988718c19bc06734, 0x1f3fb42f7520b98b58f38e68daa3df5c29a3fa2f02439d48d28194b2028f34150b372fe907ca63226f4becdc, 0xe0eea64ce7858393ecead6e1f7f22776391440836d8b8153d2ff6d5aff8dc2b037f86792aeda38de918f7e6c,
  0x544031dc57a081d93ef88c8ef0b89a8a46af515c6b3662a408637eccccd8cf73a3dfeea2f8f293303bcfe80e4, 0x1a6a3c175d3497d42889fb78aef0ccc7e34fa9967331a49b2862392e2d6b11708a59a5f169fb4b946e99ebbdd0, 0x6f6f21fd04da20f990703bc11b30e588aa8b019fd8bf7d4b45d6751d630d0a7512132fdfdec6cdfd13a6d7e370,
  0x18ce9d8de7cdbf8787a1ff292e631383c84589da8c4785a8b2964dc8581208635dc3101ff41b7c93d7c7d49dff0, 0x4adc313dbf827490db9842ba56b59d0c1774172337c538e67a1bcc8816b09eb1fe109607aeb2cc0ee7b9b7d1b50, 0xbff26664771c2a5c001b1d858205a6db6f179083899e9e47e93df870bd8d62fa7d2225651e4bfc3ec67dbc1d3ce,
  0x1a331e2305e9ea00764fad083dd10014b2657c3044856daa79164004267f7332e48e231dad159d35d89c9ca50a0a, 0x30d488268c43ab2eea1caf34d522ed142544e6c9d6104b07eaee777cbb7ba31e6a9d344fc516a6b8dbfa4f2068b2, 0x4dc987596c52c851483a8595f1852360a5cafb4ecad6c792c44731eed3eb6b13cda547dba20eb09a549e6176c846,
  0x6a08ff6b32f1adae1a44c2719d022e8edfc4773f3f9078d4bd1f7baf1b736ed96dc057292fe09ff2493a934a715c, 0x7bc6e2807a600aac73de81607e3d8e364171cd4741bcc05dba01c4d00a8d5120d6bdb34d62d74e6b2d7f49e2eb14, 0x7bc6e2807a600aac73de81607e3d8e364171cd4741bcc05dba01c4d00a8d5120d6bdb34d62d74e6b2d7f49e2eb14,
  0x6a08ff6b32f1adae1a44c2719d022e8edfc4773f3f9078d4bd1f7baf1b736ed96dc057292fe09ff2493a934a715c, 0x4dc987596c52c851483a8595f1852360a5cafb4ecad6c792c44731eed3eb6b13cda547dba20eb09a549e6176c846, 0x30d488268c43ab2eea1caf34d522ed142544e6c9d6104b07eaee777cbb7ba31e6a9d344fc516a6b8dbfa4f2068b2,
  0x1a331e2305e9ea00764fad083dd10014b2657c3044856daa79164004267f7332e48e231dad159d35d89c9ca50a0a, 0xbff26664771c2a5c001b1d858205a6db6f179083899e9e47e93df870bd8d62fa7d2225651e4bfc3ec67dbc1d3ce, 0x4adc313dbf827490db9842ba56b59d0c1774172337c538e67a1bcc8816b09eb1fe109607aeb2cc0ee7b9b7d1b50,
  0x18ce9d8de7cdbf8787a1ff292e631383c84589da8c4785a8b2964dc8581208635dc3101ff41b7c93d7c7d49dff0, 0x6f6f21fd04da20f990703bc11b30e588aa8b019fd8bf7d4b45d6751d630d0a7512132fdfdec6cdfd13a6d7e370, 0x1a6a3c175d3497d42889fb78aef0ccc7e34fa9967331a49b2862392e2d6b11708a59a5f169fb4b946e99ebbdd0,
  0x544031dc57a081d93ef88c8ef0b89a8a46af515c6b3662a408637eccccd8cf73a3dfeea2f8f293303bcfe80e4, 0xe0eea64ce7858393ecead6e1f7f22776391440836d8b8153d2ff6d5aff8dc2b037f86792aeda38de918f7e6c, 0x1f3fb42f7520b98b58f38e68daa3df5c29a3fa2f02439d48d28194b2028f34150b372fe907ca63226f4becdc,
  0x3979838278a74366d40d476aaf553727b8c2dbee2f3e7a169dc647fe23b3341ec71d93d988718c19bc06734, 0x56d99846a035e85649d42d72e1bcddd5558ca4fd06753a8b2ba2f307f912f0dbac351c1418454d5070a118, 0x6af1a5160de5e9c23cb8fafe086f6ac728a8cd081b9573b97661c62e3c0af53b08039ffe69dcd6d223f48,
  0x6a4cb045f72d815c857cef29e51b1dfba82edba95ab833cf227db3c535234f92ff6a7a92cb6a4e8569c8, 0x545cb24de842f97c440779eea33ba429a12e65d37e2cc77e07f901d63189877e7d522a054083b8ae898, 0x34c83d9f2ba417692fda8075711fbb8edf84085826cf13fd113f0cc2af6812b927b54fb470e4e8c924,
  0x19a6bd621e8185924d9b2d42f8ccd9e902472d3c53a7b6f395da31125e82c88efca5e1e6dcc0c03ac, 0x98409cee442353b0823e5db238f24aff735e8993cfd22c9114133cdfadd8f67c494ed6c66d0897c, 0x2a3b7d2f44809b8f0ee32c2fa4f5b38017dc3e874b3ce43bed09b779c851d884fe192d56fe3394,
  0x88bc727c44414109d400145e7cc4d539b4b7d6cfacf637593f105996e31eaf2674a4d94a42b0, 0x1397e1859c57053a774fa68e63075fd6ed9be3e61cdf48252529ae57ab6ffca0acc24744610, 0x1eac5e13af2603cfbd4b0c38e502f7b7b57c2e7afefb0a66a913001b55d8a86b67be27790,
  0x1f581d7ca91740ad52b5fd4732b3dfef42b9eec5813101a830ac25db7ae884eb03dcf30, 0x13c147ed12704e344ed8a145359eb48ae6a1d2a43245f458f2ae752e42925069d15b9, 0x7242e80eb324f499d6c1d7d951934f6e892f8fe9811f86e9cdf573bc80988a185b,
  0x158b6509c41939246f514cde91e09c683757e305684fb46cecd7c557b2fb6867, 0x1ddaa8d81bc95bb3066b05fdf16b05d405be736651070e82be12f6ef1379d, 0xff3a8de04a0ae3b5be053a34fc8c403564e2302710496a6eafea727da,
  0x2903be9c30329bc381d19fb5b9550cb5b67b5e0d265c763d7ff30e, 0x15f6af44d61d11f7abaffd3691fb2df943315f9940e732f7ce, 0x161bc7d7119a10c34ec05649576f55c507c7edf13f21a,
  0xffffff964ad47b1a8302ee3e310699fca131c5, 0x15f719aa934616a9ec6d804a647145f, 0xfffffffffffffffffb3,
  0x1]

private theorem eulerianCoefficients_eq : descentCoeffs 76 = eulerianCoefficients := by
  decide +kernel

private theorem upper : upperOK (descentCoeffs 76) first gaps = true := by
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

private theorem lower (i : Fin (lastRepresentative 77 - 2)) :
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

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 77) :
    StrictNegativeInterlacing (originalQuotient 77 k) (eulerian 76) 74 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N077
