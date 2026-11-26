import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentPackedData.C127L080.N080

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N080

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L080.N080 LongCycleBounds.DescentNecklace.Packed.C127L080.N080.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L080.N080 LongCycleBounds.DescentNecklace.Packed.C127L080.N080.rows

private theorem actual : RepresentativeChecks 80 previousNodes rows :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L080.N080 LongCycleBounds.DescentNecklace.Packed.C127L080.N080.dataChecks

private def first : LongCycleFinite.Dyadic := ⟨-604462909807314587353088, 0⟩

private def gaps : List Window := [
  ⟨⟨-604443310141736270954496, 0⟩, ⟨-91486829936640, 0⟩⟩,
  ⟨⟨-73894643892224, 0⟩, ⟨-9266233344, 0⟩⟩,
  ⟨⟨-5830115328, 0⟩, ⟨-43764096, 0⟩⟩,
  ⟨⟨-43410176, 0⟩, ⟨-1655360, 0⟩⟩,
  ⟨⟨-1653308, 0⟩, ⟨-338537, 1⟩⟩,
  ⟨⟨-169193, 0⟩, ⟨-251713, 3⟩⟩,
  ⟨⟨-503311, 4⟩, ⟨-275229, 5⟩⟩,
  ⟨⟨-275189, 5⟩, ⟨-97979, 5⟩⟩,
  ⟨⟨-391877, 7⟩, ⟨-84223, 6⟩⟩,
  ⟨⟨-336867, 8⟩, ⟨-332831, 9⟩⟩,
  ⟨⟨-332811, 9⟩, ⟨-22843, 6⟩⟩,
  ⟨⟨-365471, 10⟩, ⟨-54463, 8⟩⟩,
  ⟨⟨-435687, 11⟩, ⟨-138571, 10⟩⟩,
  ⟨⟨-69283, 9⟩, ⟨-46439, 9⟩⟩,
  ⟨⟨-92875, 10⟩, ⟨-259873, 12⟩⟩,
  ⟨⟨-519733, 13⟩, ⟨-376615, 13⟩⟩,
  ⟨⟨-376605, 13⟩, ⟨-281049, 13⟩⟩,
  ⟨⟨-281043, 13⟩, ⟨-429991, 14⟩⟩,
  ⟨⟨-214991, 13⟩, ⟨-335929, 14⟩⟩,
  ⟨⟨-167961, 13⟩, ⟨-267203, 14⟩⟩,
  ⟨⟨-133599, 13⟩, ⟨-215843, 14⟩⟩,
  ⟨⟨-431679, 15⟩, ⟨-353395, 15⟩⟩,
  ⟨⟨-353389, 15⟩, ⟨-292665, 15⟩⟩,
  ⟨⟨-73165, 13⟩, ⟨-489641, 16⟩⟩,
  ⟨⟨-244817, 15⟩, ⟨-413197, 16⟩⟩,
  ⟨⟨-51649, 13⟩, ⟨-351363, 16⟩⟩,
  ⟨⟨-175679, 15⟩, ⟨-300781, 16⟩⟩,
  ⟨⟨-150389, 15⟩, ⟨-517967, 17⟩⟩,
  ⟨⟨-517961, 17⟩, ⟨-224125, 16⟩⟩,
  ⟨⟨-448245, 17⟩, ⟨-24351, 13⟩⟩,
  ⟨⟨-389611, 17⟩, ⟨-84983, 15⟩⟩,
  ⟨⟨-42491, 14⟩, ⟨-4649, 11⟩⟩,
  ⟨⟨-297533, 17⟩, ⟨-522273, 18⟩⟩,
  ⟨⟨-130567, 16⟩, ⟨-229699, 17⟩⟩,
  ⟨⟨-229697, 17⟩, ⟨-25301, 14⟩⟩,
  ⟨⟨-101203, 16⟩, ⟨-357209, 18⟩⟩,
  ⟨⟨-178603, 17⟩, ⟨-157751, 17⟩⟩,
  ⟨⟨-315499, 18⟩, ⟨-69707, 16⟩⟩,
  ⟨⟨-278825, 18⟩, ⟨-492923, 19⟩⟩,
  ⟨⟨-246459, 18⟩, ⟨-435623, 19⟩⟩,
  ⟨⟨-435619, 19⟩, ⟨-384763, 19⟩⟩,
  ⟨⟨-384759, 19⟩, ⟨-169757, 18⟩⟩,
  ⟨⟨-169755, 18⟩, ⟨-299175, 19⟩⟩,
  ⟨⟨-74793, 17⟩, ⟨-32895, 16⟩⟩,
  ⟨⟨-263157, 19⟩, ⟨-461925, 20⟩⟩,
  ⟨⟨-14435, 15⟩, ⟨-202159, 19⟩⟩,
  ⟨⟨-202157, 19⟩, ⟨-352759, 20⟩⟩,
  ⟨⟨-352755, 20⟩, ⟨-153309, 19⟩⟩,
  ⟨⟨-153307, 19⟩, ⟨-265345, 20⟩⟩,
  ⟨⟨-132671, 19⟩, ⟨-28559, 17⟩⟩,
  ⟨⟨-456939, 21⟩, ⟨-391163, 21⟩⟩,
  ⟨⟨-195579, 20⟩, ⟨-166313, 20⟩⟩,
  ⟨⟨-166311, 20⟩, ⟨-140349, 20⟩⟩,
  ⟨⟨-140347, 20⟩, ⟨-469621, 22⟩⟩,
  ⟨⟨-469615, 22⟩, ⟨-97229, 20⟩⟩,
  ⟨⟨-194455, 21⟩, ⟨-318383, 22⟩⟩,
  ⟨⟨-159189, 21⟩, ⟨-514373, 23⟩⟩,
  ⟨⟨-514365, 23⟩, ⟨-25571, 19⟩⟩,
  ⟨⟨-409129, 23⟩, ⟨-319637, 23⟩⟩,
  ⟨⟨-319631, 23⟩, ⟨-489035, 24⟩⟩,
  ⟨⟨-244513, 23⟩, ⟨-364947, 24⟩⟩,
  ⟨⟨-91235, 22⟩, ⟨-264443, 24⟩⟩,
  ⟨⟨-264437, 24⟩, ⟨-184977, 24⟩⟩,
  ⟨⟨-369945, 25⟩, ⟨-495925, 26⟩⟩,
  ⟨⟨-61989, 23⟩, ⟨-315455, 26⟩⟩,
  ⟨⟨-157723, 25⟩, ⟨-47007, 24⟩⟩,
  ⟨⟨-94011, 25⟩, ⟨-206479, 27⟩⟩,
  ⟨⟨-412943, 28⟩, ⟨-408003, 29⟩⟩,
  ⟨⟨-203993, 28⟩, ⟨-350719, 30⟩⟩,
  ⟨⟨-175351, 29⟩, ⟨-249695, 31⟩⟩,
  ⟨⟨-124841, 30⟩, ⟨-68263, 31⟩⟩,
  ⟨⟨-273035, 33⟩, ⟨-406013, 36⟩⟩,
  ⟨⟨-202993, 35⟩, ⟨-166223, 38⟩⟩,
  ⟨⟨-332421, 39⟩, ⟨-402801, 44⟩⟩,
  ⟨⟨-402769, 44⟩, ⟨-305513, 51⟩⟩,
  ⟨⟨-305487, 51⟩, ⟨-226337, 64⟩⟩,
  ⟨⟨-56579, 62⟩, ⟨-262149, 97⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private def eulerianCoefficients : List ℤ := [
  0x1, 0x7fffffffffffffffffb0, 0x2510fb4fd8e0363ebef8c87d897dfdc3,
  0x3ffffff46ab1770c339b0c64524158c508a34da0, 0xacb91ad9397dc31fe7e461dbed2cd953e014b998fb7f61, 0x128847ae10f63928730573227d8d9bdb3c346f80e44f346c2d50,
  0x36f713cafff7af1fe4f0f4ff02a62eda265c5ae88db312715b5d369b, 0x1feed1df42db6828df4ded626c5c54f1792f1a4fa9c95c0945d8eed17ac0, 0x553ec6c1f8aac22a3331fedff9c8e5405933ada107d40e5c58204a04dee9633,
  0x54b0c919fa280b8ad50668e2abb0b819213bfc62d7a7aff9d4467069751231ddd0, 0x2597a554161f832cbf9e050b3a0b31e645a144616aa8754abfddf55a21dbb204a6429, 0x8841185488d62a9483f024a0f22ff740470953aff19179403f7131b63298ac5e0a6a4a0,
  0x116634b2ae74b44443c5701516a6a3bb2dc485b82bf896704c3b28c32af233a435310efddb, 0x159f81251c18159d9b91f918df513764ab18b8488d6746edcc50ed768c885c862afcc1b62f30, 0x1158668c0ba93d6f2497cc7b96a67f1cda1429450caad8bc70717b3febb108f1c2a79ec1ea9389,
  0x96a3f08aa0e37714513128f83203cf60c7633f28149b40bcb72a383acf1c91780fa5b30b3219200, 0x397a549d515b489d04dfbec92f0e44911a2e10a93268f5045228b15eb1527c9cbdd378e6189daece4, 0xfe78f4db89f1f9ef917c13c10afb33dc2a8a5ec3941e10c2710a4383c1b3026c9055d742580cc762c0,
  0x3466a68373cafefab8c5bb7ec99483f39b8cc2b41cd72e5b3ec2b52869a653347aa05a9ca0855026b52c, 0x8349d31739b3860ebaae85ed372425f6e44ab60cdd04b02510f4f3ed16d137110aaccc4c4379a72a99c80, 0xfec00af194f78654cd732a766b1b7bdb7759ea32294bbe39d51731800efd7fc4973f0fe8ec4f9d933effa4,
  0x184d4556263ce88d6f5837d77939f101184c20c6be8f9785abb0ac3694b3fb2d2c7707b376cf6ce92ea93940, 0x1d9192996cf993534fa4858bed497daae7b69a49ab008bbd99fb37ba6d08e167ee226ae58044e712f262bbb4c, 0x1d02d79e9fd4fe4a027a760467b3f617cdc3d3ada05a46dd37a88e81572418ebc9103501746bfcfa6afac93d00,
  0x172ec03c69e4dd2c9699662eb06d12c964782a8ef8927afe98dc33c68348b230e503b1a857aa6c27a9c96c689dc, 0xf381063c3cfc00114ea70300573da5b2cb8102c601264420a6b7bdf30da80380a98151b03bec595fd55cba88c40, 0x845271c66df60b9d46608d0149e4c57559163f9c62988dc8bcf01b53240b0521ae1a10e04455ee424ffb33a72f54,
  0x3be9c2705bacaa2fb7c5b2a934cb75818f433c17e3766375a1a67f968a924b58ac867424023c33f25778bd4704680, 0x16bbe2024d4852dc2943534821a8d49e68a0a376f2b5568accf794d29794d8ca2555e97c2bafd06d174241b61702bc, 0x743fcc4c2216399c4ee6ccc7c4effad9cd122ea95f3c3cd2b176ca5875b1ca2d7db258c304f549c59415039d6f8fc0,
  0x1f6dc76e21bd381956190251ce294f71369524002f6dfc338efbd438f5ec98352163fb4e54c2bc9e7efa5b9ccd2e114, 0x7371ef56acac7ed14325d6dc4f01618e0a4b584ddbcb3fd61b6bd1e49e65b07ee77da56000e0897c6c42083e4c13e00, 0x16944de39d716f2e6dbc671909512a489c014f66190933290ae43fe7d1b7bb19af2a89fd293d7e743576d7e943bbb97e,
  0x3c5d75bddb7d576b18419eaa858d9655418649795c28a17bc3179f1f0cfb0465b16af60ae11c762648f864b08ed68ea0, 0x8a329ee0fd3ac952ba5c0a5d228a0252547ba9c5ba3d8cc9502cf0b66dabf24b8d71ef9bdc9f9760a9373cd4ec5cf57a, 0x10f74ad6774c88b3f9b72744bb058b28ce71f3870ae4358cebd1897a3a098151bd28d3f9d3d145546cdc48094753c2ac0,
  0x1ca337e6164f409de51bd810eb5a9c9fc9c83dd45b90cd4f3714db7b92ce106271757bb1d7a6227610c3fe1e82060447e, 0x2996919c188ebab58b60faf6b14019704261ab2f55c6a748c26fe61b03cac60532cc5f1d8584c177c4cbf60f3c44c7f60, 0x34014614fd346947b1fa52926c4d2cb2c7e2e4b92033cb47460f3f9ed8b3f9499621c5720fa2541916651093aefb9d30a,
  0x3806501f818fd1ea8a8104500e1abce03f13f17b1799aecc1745997370e60ad6b2a37d3de4510fa78d2446183b1c4f080, 0x34014614fd346947b1fa52926c4d2cb2c7e2e4b92033cb47460f3f9ed8b3f9499621c5720fa2541916651093aefb9d30a, 0x2996919c188ebab58b60faf6b14019704261ab2f55c6a748c26fe61b03cac60532cc5f1d8584c177c4cbf60f3c44c7f60,
  0x1ca337e6164f409de51bd810eb5a9c9fc9c83dd45b90cd4f3714db7b92ce106271757bb1d7a6227610c3fe1e82060447e, 0x10f74ad6774c88b3f9b72744bb058b28ce71f3870ae4358cebd1897a3a098151bd28d3f9d3d145546cdc48094753c2ac0, 0x8a329ee0fd3ac952ba5c0a5d228a0252547ba9c5ba3d8cc9502cf0b66dabf24b8d71ef9bdc9f9760a9373cd4ec5cf57a,
  0x3c5d75bddb7d576b18419eaa858d9655418649795c28a17bc3179f1f0cfb0465b16af60ae11c762648f864b08ed68ea0, 0x16944de39d716f2e6dbc671909512a489c014f66190933290ae43fe7d1b7bb19af2a89fd293d7e743576d7e943bbb97e, 0x7371ef56acac7ed14325d6dc4f01618e0a4b584ddbcb3fd61b6bd1e49e65b07ee77da56000e0897c6c42083e4c13e00,
  0x1f6dc76e21bd381956190251ce294f71369524002f6dfc338efbd438f5ec98352163fb4e54c2bc9e7efa5b9ccd2e114, 0x743fcc4c2216399c4ee6ccc7c4effad9cd122ea95f3c3cd2b176ca5875b1ca2d7db258c304f549c59415039d6f8fc0, 0x16bbe2024d4852dc2943534821a8d49e68a0a376f2b5568accf794d29794d8ca2555e97c2bafd06d174241b61702bc,
  0x3be9c2705bacaa2fb7c5b2a934cb75818f433c17e3766375a1a67f968a924b58ac867424023c33f25778bd4704680, 0x845271c66df60b9d46608d0149e4c57559163f9c62988dc8bcf01b53240b0521ae1a10e04455ee424ffb33a72f54, 0xf381063c3cfc00114ea70300573da5b2cb8102c601264420a6b7bdf30da80380a98151b03bec595fd55cba88c40,
  0x172ec03c69e4dd2c9699662eb06d12c964782a8ef8927afe98dc33c68348b230e503b1a857aa6c27a9c96c689dc, 0x1d02d79e9fd4fe4a027a760467b3f617cdc3d3ada05a46dd37a88e81572418ebc9103501746bfcfa6afac93d00, 0x1d9192996cf993534fa4858bed497daae7b69a49ab008bbd99fb37ba6d08e167ee226ae58044e712f262bbb4c,
  0x184d4556263ce88d6f5837d77939f101184c20c6be8f9785abb0ac3694b3fb2d2c7707b376cf6ce92ea93940, 0xfec00af194f78654cd732a766b1b7bdb7759ea32294bbe39d51731800efd7fc4973f0fe8ec4f9d933effa4, 0x8349d31739b3860ebaae85ed372425f6e44ab60cdd04b02510f4f3ed16d137110aaccc4c4379a72a99c80,
  0x3466a68373cafefab8c5bb7ec99483f39b8cc2b41cd72e5b3ec2b52869a653347aa05a9ca0855026b52c, 0xfe78f4db89f1f9ef917c13c10afb33dc2a8a5ec3941e10c2710a4383c1b3026c9055d742580cc762c0, 0x397a549d515b489d04dfbec92f0e44911a2e10a93268f5045228b15eb1527c9cbdd378e6189daece4,
  0x96a3f08aa0e37714513128f83203cf60c7633f28149b40bcb72a383acf1c91780fa5b30b3219200, 0x1158668c0ba93d6f2497cc7b96a67f1cda1429450caad8bc70717b3febb108f1c2a79ec1ea9389, 0x159f81251c18159d9b91f918df513764ab18b8488d6746edcc50ed768c885c862afcc1b62f30,
  0x116634b2ae74b44443c5701516a6a3bb2dc485b82bf896704c3b28c32af233a435310efddb, 0x8841185488d62a9483f024a0f22ff740470953aff19179403f7131b63298ac5e0a6a4a0, 0x2597a554161f832cbf9e050b3a0b31e645a144616aa8754abfddf55a21dbb204a6429,
  0x54b0c919fa280b8ad50668e2abb0b819213bfc62d7a7aff9d4467069751231ddd0, 0x553ec6c1f8aac22a3331fedff9c8e5405933ada107d40e5c58204a04dee9633, 0x1feed1df42db6828df4ded626c5c54f1792f1a4fa9c95c0945d8eed17ac0,
  0x36f713cafff7af1fe4f0f4ff02a62eda265c5ae88db312715b5d369b, 0x128847ae10f63928730573227d8d9bdb3c346f80e44f346c2d50, 0xacb91ad9397dc31fe7e461dbed2cd953e014b998fb7f61,
  0x3ffffff46ab1770c339b0c64524158c508a34da0, 0x2510fb4fd8e0363ebef8c87d897dfdc3, 0x7fffffffffffffffffb0,
  0x1]

private theorem eulerianCoefficients_eq : descentCoeffs 79 = eulerianCoefficients := by
  decide +kernel

private theorem upper : upperOK (descentCoeffs 79) first gaps = true := by
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

private theorem lower (i : Fin (lastRepresentative 80 - 2)) :
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

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 80) :
    StrictNegativeInterlacing (originalQuotient 80 k) (eulerian 79) 77 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N080
