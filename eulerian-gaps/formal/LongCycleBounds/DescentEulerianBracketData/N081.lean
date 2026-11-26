import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentPackedData.C127L088.N081

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N081

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L088.N081 LongCycleBounds.DescentNecklace.Packed.C127L088.N081.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L088.N081 LongCycleBounds.DescentNecklace.Packed.C127L088.N081.rows

private theorem actual : RepresentativeChecks 81 previousNodes rows :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L088.N081 LongCycleBounds.DescentNecklace.Packed.C127L088.N081.dataChecks

private def first : LongCycleFinite.Dyadic := ⟨-1208925819614629174706176, 0⟩

private def gaps : List Window := [
  ⟨⟨-1208886620283472541908992, 0⟩, ⟨-153058675785728, 0⟩⟩,
  ⟨⟨-117874303696896, 0⟩, ⟨-12594774016, 0⟩⟩,
  ⟨⟨-7548157952, 0⟩, ⟨-55038336, 0⟩⟩,
  ⟨⟨-54580096, 0⟩, ⟨-1989616, 0⟩⟩,
  ⟨⟨-1987052, 0⟩, ⟨-396293, 1⟩⟩,
  ⟨⟨-396111, 1⟩, ⟨-288751, 3⟩⟩,
  ⟨⟨-288683, 3⟩, ⟨-310973, 5⟩⟩,
  ⟨⟨-310927, 5⟩, ⟨-218795, 6⟩⟩,
  ⟨⟨-218773, 6⟩, ⟨-186293, 7⟩⟩,
  ⟨⟨-186279, 7⟩, ⟨-91321, 7⟩⟩,
  ⟨⟨-182631, 8⟩, ⟨-398585, 10⟩⟩,
  ⟨⟨-199283, 9⟩, ⟨-236311, 10⟩⟩,
  ⟨⟨-472603, 11⟩, ⟨-149635, 10⟩⟩,
  ⟨⟨-74815, 9⟩, ⟨-399651, 12⟩⟩,
  ⟨⟨-399639, 12⟩, ⟨-139321, 11⟩⟩,
  ⟨⟨-139317, 11⟩, ⟨-201339, 12⟩⟩,
  ⟨⟨-402669, 13⟩, ⟨-299775, 13⟩⟩,
  ⟨⟨-299769, 13⟩, ⟨-114425, 12⟩⟩,
  ⟨⟨-457691, 14⟩, ⟨-178469, 13⟩⟩,
  ⟨⟨-356931, 14⟩, ⟨-70871, 12⟩⟩,
  ⟨⟨-283479, 14⟩, ⟨-228703, 14⟩⟩,
  ⟨⟨-457399, 15⟩, ⟨-374045, 15⟩⟩,
  ⟨⟨-374039, 15⟩, ⟨-309491, 15⟩⟩,
  ⟨⟨-309487, 15⟩, ⟨-258713, 15⟩⟩,
  ⟨⟨-517419, 16⟩, ⟨-218201, 15⟩⟩,
  ⟨⟨-436397, 16⟩, ⟨-92737, 14⟩⟩,
  ⟨⟨-370943, 16⟩, ⟨-158733, 15⟩⟩,
  ⟨⟨-158731, 15⟩, ⟨-273317, 16⟩⟩,
  ⟨⟨-136657, 15⟩, ⟨-59133, 14⟩⟩,
  ⟨⟨-473059, 17⟩, ⟨-411247, 17⟩⟩,
  ⟨⟨-411243, 17⟩, ⟨-358907, 17⟩⟩,
  ⟨⟨-358903, 17⟩, ⟨-314277, 17⟩⟩,
  ⟨⟨-314273, 17⟩, ⟨-137989, 16⟩⟩,
  ⟨⟨-275975, 17⟩, ⟨-485845, 18⟩⟩,
  ⟨⟨-30365, 14⟩, ⟨-214239, 17⟩⟩,
  ⟨⟨-428473, 18⟩, ⟨-189227, 17⟩⟩,
  ⟨⟨-189225, 17⟩, ⟨-334649, 18⟩⟩,
  ⟨⟨-167323, 17⟩, ⟨-74033, 16⟩⟩,
  ⟨⟨-296129, 18⟩, ⟨-131073, 17⟩⟩,
  ⟨⟨-262143, 18⟩, ⟨-464117, 19⟩⟩,
  ⟨⟨-464113, 19⟩, ⟨-410701, 19⟩⟩,
  ⟨⟨-410697, 19⟩, ⟨-181581, 18⟩⟩,
  ⟨⟨-181579, 18⟩, ⟨-160383, 18⟩⟩,
  ⟨⟨-320763, 19⟩, ⟨-141445, 18⟩⟩,
  ⟨⟨-282887, 19⟩, ⟨-498011, 20⟩⟩,
  ⟨⟨-249003, 19⟩, ⟨-437321, 20⟩⟩,
  ⟨⟨-437317, 20⟩, ⟨-382943, 20⟩⟩,
  ⟨⟨-382939, 20⟩, ⟨-167101, 19⟩⟩,
  ⟨⟨-167099, 19⟩, ⟨-72633, 18⟩⟩,
  ⟨⟨-290529, 20⟩, ⟨-251431, 20⟩⟩,
  ⟨⟨-62857, 18⟩, ⟨-13529, 16⟩⟩,
  ⟨⟨-432923, 21⟩, ⟨-185255, 20⟩⟩,
  ⟨⟨-185253, 20⟩, ⟨-314939, 21⟩⟩,
  ⟨⟨-314935, 21⟩, ⟨-132813, 20⟩⟩,
  ⟨⟨-132811, 20⟩, ⟨-444083, 22⟩⟩,
  ⟨⟨-444077, 22⟩, ⟨-367445, 22⟩⟩,
  ⟨⟨-367439, 22⟩, ⟨-300479, 22⟩⟩,
  ⟨⟨-150237, 21⟩, ⟨-242415, 22⟩⟩,
  ⟨⟨-242411, 22⟩, ⟨-192527, 22⟩⟩,
  ⟨⟨-48131, 20⟩, ⟨-300291, 23⟩⟩,
  ⟨⟨-300285, 23⟩, ⟨-458479, 24⟩⟩,
  ⟨⟨-229235, 23⟩, ⟨-341321, 24⟩⟩,
  ⟨⟨-170657, 23⟩, ⟨-493261, 25⟩⟩,
  ⟨⟨-246625, 24⟩, ⟨-42989, 22⟩⟩,
  ⟨⟨-10747, 20⟩, ⟨-459261, 26⟩⟩,
  ⟨⟨-459249, 26⟩, ⟨-72703, 24⟩⟩,
  ⟨⟨-290803, 26⟩, ⟨-344835, 27⟩⟩,
  ⟨⟨-344823, 27⟩, ⟨-23517, 24⟩⟩,
  ⟨⟨-188129, 27⟩, ⟨-184445, 28⟩⟩,
  ⟨⟨-368875, 29⟩, ⟨-157055, 29⟩⟩,
  ⟨⟨-314095, 30⟩, ⟨-442017, 32⟩⟩,
  ⟨⟨-220997, 31⟩, ⟨-476105, 34⟩⟩,
  ⟨⟨-476077, 34⟩, ⟨-346943, 36⟩⟩,
  ⟨⟨-346919, 36⟩, ⟨-276387, 39⟩⟩,
  ⟨⟨-138183, 38⟩, ⟨-80443, 42⟩⟩,
  ⟨⟨-321747, 44⟩, ⟨-229039, 51⟩⟩,
  ⟨⟨-57255, 49⟩, ⟨-150889, 64⟩⟩,
  ⟨⟨-150875, 64⟩, ⟨-262165, 98⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private def eulerianCoefficients : List ℤ := [
  0x1, 0xffffffffffffffffffaf, 0x6f32f1ef8ac7a2bc3cea59789c79e0e9,
  0xffffffdcd0e1733509dc8270b9d9b0d67d728a27, 0x35f9d993e1f715f4c36cd889da98e070ec6c21e8d648865, 0x6f31e0aea0a2faca8a4b0bbed9fd159f8ce62fab6c3b0c37614b,
  0x180c6e5f1b816b10bc847f28c5a8392e619e5e3841b277ffea6d1975d, 0xff863b6ebbbe3ee7ea87b3c93f9a68ef25adc2d33a9b485a711a84206833, 0x2ffc4af822aadaed084aed48c02f7aec161726e9facf08b5d42dcea5e84dcdcb,
  0x350622195c24fe929ed8346b5b6cb9c7499e3b12ee71f9cc20487736708531e5245, 0x19ef6a00cc501121ebb2e33865e2a4a0a6bdf569fc5ac87d8238a3f0b41d0d5cd4f4a3, 0x66d2f038614007d513ee74ee760e49b76653463ad949116a01f0527abaa484b63bdcb68d,
  0xe473c1ba4332b5ac68376dadd27b9c5c2428b1fde7624df7300eb2fc74a3a833432a069e9f, 0x13346cfd24cf9b9cc5fb84bb1bb5ea45b585482f6ef27f06090607826c3b272da53be6ee304f1, 0x109c121804028cf15c7009d763d5462f8bb4aca8e72775353e55315f75f9aae04fee7774db6cf67,
  0x9b0b62942fd96fad897bb3e3934415a71ac25da29cd2a1c48fb7088609f484bd7212425a6ea895c9, 0x3f6c89a950f48b0326727f59a2c73817aeee7eb065e1f1578a27e55587a416ac69ef4740a6efee3b24, 0x12c6d2e49b235b00c27dea62caeef1d37654d00b5aa09a726cf638f9a878caf64b5179ceb431d2e53d9c,
  0x4213fa70ec3798723bbe8f731b6aea1a3ddbff65181d7b8d4bfd3ee59c041877b64db83c1fb380b295cc4, 0xb098bd8a5ab7c65427614515baf592e5a96dedf4ff25223a13269612fdb226a8ce9034f6a697d50e79657c, 0x16d215bd6850af3bac1680f1f05808b75ea27860cda0082f497a7da23a505c09a050344c395f901ff3eba674,
  0x2515a37ecf691081d1cee574db5aa0ba3ab0c8a0defdb7a54154b25194aec025421163216e449b55af20fd64c, 0x3002c47211509077cdb67c9ff690c53fec97bd36ecfd5134d63f27205a6d8aeda2647168914e0ad8110044cc54, 0x3219ad1219030f3c907352c2c3634e1ec23d65ded79a89690ac5c52a84fd1f91d19df94f483152ead87029a6bec,
  0x2a91ab89186c3135dbda7979ea59cb2fe1fe98cd5f789fae3304f01278317bdff9d1512f5a71e854c0b19568ce7c, 0x1db625ef18f1c3865657eb4210c3b1dd6d40eb6cd3855b5803c5f86a5597aea3926aed7710eb9e504125b13c5dcc4, 0x112a8574f8e6c5b9d0d5a28943f190e29bd42c1edaa9f81a1a1fff02d91b40965f98d43b59ff4dcea1df97682f935c,
  0x843e25d2b5321a3b112bf5d960b06a84062744552e78c3686a0114efa8f64beb26f6b0bd720f253bd3a24cede48264, 0x35600522feb228c0bc1e2f3d1bbb553d6ebcd07c721cb90f78568fa846e3803c66b706c85fa2e452f3ec9d8c769a14c, 0x1226e7f7616403422d777596c7c8c1c114e022088b832f5e57a13e5c51fd7ce19a2b03ea9748c52ae2fca983b9a863f4,
  0x5399284c4006f3f19e39887d83e6e8e9e3ce82dd707edc850bb11eb3a3772063d33e8c3ddb3135dbacf12c348d5354ec, 0x14724116ea0ac79701df844d325614666cbbf6edc48d7540a1cbaddb7adeff320853d7c5fe555749e3d62c90ccc84d4d4, 0x44373d85b51a4d16feebacecf207a98063b0d4512cd9157ccb9afb28fe3e02fcc4af4b9c2538ee9702917edcc9f6e893e,
  0xc29a3f0010e7905bf5e4e003e72b4baa7581355dcd615d6f8e90addaf3a11ef38b90402ec7811e86b81cf034667f5ff62, 0x1dbdb6e0e00f8f3b8dd65fed5fb84f5493530969d705b743c304638085539cea9a37cbf8439ceeed183f2f68d5fb43306e, 0x3e774e5018ef88f87c9e462d03debb84495a20c79a3e4a3c75af5ba313dc9c8f3178e410825ee999f2ae57c64e08cd2972,
  0x70e17f11dba9bd5c10880fa42290c8e1ba586cae71b26e0ab7e0759de316a9846e8ff4fa492fae59322301c010d4413f36, 0xafbc400d1647f91782c128b75d7bc1580bf21cbb21ccf511b1d1d05c438b6254e9911e5410a9c819c07323562c9386696a, 0xebee590ce9a66abb4fb0bc0c79445fba75796edf7fa7b69cb92ae71a1a2af771034acaf3849828d78b2dbe4ff8b9dc0c46,
  0x111530be48cbdda921253fe5f58c89ababde745ce1d84ede4ddb512a7a58c49e54f4f430f02da9ea32a3da9b7042b88609a, 0x111530be48cbdda921253fe5f58c89ababde745ce1d84ede4ddb512a7a58c49e54f4f430f02da9ea32a3da9b7042b88609a, 0xebee590ce9a66abb4fb0bc0c79445fba75796edf7fa7b69cb92ae71a1a2af771034acaf3849828d78b2dbe4ff8b9dc0c46,
  0xafbc400d1647f91782c128b75d7bc1580bf21cbb21ccf511b1d1d05c438b6254e9911e5410a9c819c07323562c9386696a, 0x70e17f11dba9bd5c10880fa42290c8e1ba586cae71b26e0ab7e0759de316a9846e8ff4fa492fae59322301c010d4413f36, 0x3e774e5018ef88f87c9e462d03debb84495a20c79a3e4a3c75af5ba313dc9c8f3178e410825ee999f2ae57c64e08cd2972,
  0x1dbdb6e0e00f8f3b8dd65fed5fb84f5493530969d705b743c304638085539cea9a37cbf8439ceeed183f2f68d5fb43306e, 0xc29a3f0010e7905bf5e4e003e72b4baa7581355dcd615d6f8e90addaf3a11ef38b90402ec7811e86b81cf034667f5ff62, 0x44373d85b51a4d16feebacecf207a98063b0d4512cd9157ccb9afb28fe3e02fcc4af4b9c2538ee9702917edcc9f6e893e,
  0x14724116ea0ac79701df844d325614666cbbf6edc48d7540a1cbaddb7adeff320853d7c5fe555749e3d62c90ccc84d4d4, 0x5399284c4006f3f19e39887d83e6e8e9e3ce82dd707edc850bb11eb3a3772063d33e8c3ddb3135dbacf12c348d5354ec, 0x1226e7f7616403422d777596c7c8c1c114e022088b832f5e57a13e5c51fd7ce19a2b03ea9748c52ae2fca983b9a863f4,
  0x35600522feb228c0bc1e2f3d1bbb553d6ebcd07c721cb90f78568fa846e3803c66b706c85fa2e452f3ec9d8c769a14c, 0x843e25d2b5321a3b112bf5d960b06a84062744552e78c3686a0114efa8f64beb26f6b0bd720f253bd3a24cede48264, 0x112a8574f8e6c5b9d0d5a28943f190e29bd42c1edaa9f81a1a1fff02d91b40965f98d43b59ff4dcea1df97682f935c,
  0x1db625ef18f1c3865657eb4210c3b1dd6d40eb6cd3855b5803c5f86a5597aea3926aed7710eb9e504125b13c5dcc4, 0x2a91ab89186c3135dbda7979ea59cb2fe1fe98cd5f789fae3304f01278317bdff9d1512f5a71e854c0b19568ce7c, 0x3219ad1219030f3c907352c2c3634e1ec23d65ded79a89690ac5c52a84fd1f91d19df94f483152ead87029a6bec,
  0x3002c47211509077cdb67c9ff690c53fec97bd36ecfd5134d63f27205a6d8aeda2647168914e0ad8110044cc54, 0x2515a37ecf691081d1cee574db5aa0ba3ab0c8a0defdb7a54154b25194aec025421163216e449b55af20fd64c, 0x16d215bd6850af3bac1680f1f05808b75ea27860cda0082f497a7da23a505c09a050344c395f901ff3eba674,
  0xb098bd8a5ab7c65427614515baf592e5a96dedf4ff25223a13269612fdb226a8ce9034f6a697d50e79657c, 0x4213fa70ec3798723bbe8f731b6aea1a3ddbff65181d7b8d4bfd3ee59c041877b64db83c1fb380b295cc4, 0x12c6d2e49b235b00c27dea62caeef1d37654d00b5aa09a726cf638f9a878caf64b5179ceb431d2e53d9c,
  0x3f6c89a950f48b0326727f59a2c73817aeee7eb065e1f1578a27e55587a416ac69ef4740a6efee3b24, 0x9b0b62942fd96fad897bb3e3934415a71ac25da29cd2a1c48fb7088609f484bd7212425a6ea895c9, 0x109c121804028cf15c7009d763d5462f8bb4aca8e72775353e55315f75f9aae04fee7774db6cf67,
  0x13346cfd24cf9b9cc5fb84bb1bb5ea45b585482f6ef27f06090607826c3b272da53be6ee304f1, 0xe473c1ba4332b5ac68376dadd27b9c5c2428b1fde7624df7300eb2fc74a3a833432a069e9f, 0x66d2f038614007d513ee74ee760e49b76653463ad949116a01f0527abaa484b63bdcb68d,
  0x19ef6a00cc501121ebb2e33865e2a4a0a6bdf569fc5ac87d8238a3f0b41d0d5cd4f4a3, 0x350622195c24fe929ed8346b5b6cb9c7499e3b12ee71f9cc20487736708531e5245, 0x2ffc4af822aadaed084aed48c02f7aec161726e9facf08b5d42dcea5e84dcdcb,
  0xff863b6ebbbe3ee7ea87b3c93f9a68ef25adc2d33a9b485a711a84206833, 0x180c6e5f1b816b10bc847f28c5a8392e619e5e3841b277ffea6d1975d, 0x6f31e0aea0a2faca8a4b0bbed9fd159f8ce62fab6c3b0c37614b,
  0x35f9d993e1f715f4c36cd889da98e070ec6c21e8d648865, 0xffffffdcd0e1733509dc8270b9d9b0d67d728a27, 0x6f32f1ef8ac7a2bc3cea59789c79e0e9,
  0xffffffffffffffffffaf, 0x1]

private theorem eulerianCoefficients_eq : descentCoeffs 80 = eulerianCoefficients := by
  decide +kernel

private theorem upper : upperOK (descentCoeffs 80) first gaps = true := by
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

private theorem lower (i : Fin (lastRepresentative 81 - 2)) :
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

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 81) :
    StrictNegativeInterlacing (originalQuotient 81 k) (eulerian 80) 78 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N081
