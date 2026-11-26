import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentPackedData.C127L088.N083

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N083

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L088.N083 LongCycleBounds.DescentNecklace.Packed.C127L088.N083.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L088.N083 LongCycleBounds.DescentNecklace.Packed.C127L088.N083.rows

private theorem actual : RepresentativeChecks 83 previousNodes rows :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L088.N083 LongCycleBounds.DescentNecklace.Packed.C127L088.N083.dataChecks

private def first : LongCycleFinite.Dyadic := ⟨-4835703278458516698824704, 0⟩

private def gaps : List Window := [
  ⟨⟨-4835546481133890167635968, 0⟩, ⟨-311386202701824, 0⟩⟩,
  ⟨⟨-170649788088320, 0⟩, ⟨-17494900736, 0⟩⟩,
  ⟨⟨-17484677120, 0⟩, ⟨-86078464, 0⟩⟩,
  ⟨⟨-85282048, 0⟩, ⟨-2877600, 0⟩⟩,
  ⟨⟨-2873552, 0⟩, ⟨-271250, 0⟩⟩,
  ⟨⟨-271117, 0⟩, ⟨-379801, 3⟩⟩,
  ⟨⟨-379707, 3⟩, ⟨-396809, 5⟩⟩,
  ⟨⟨-396749, 5⟩, ⟨-17041, 2⟩⟩,
  ⟨⟨-272627, 6⟩, ⟨-113897, 6⟩⟩,
  ⟨⟨-455553, 8⟩, ⟨-109951, 7⟩⟩,
  ⟨⟨-439777, 9⟩, ⟨-118445, 8⟩⟩,
  ⟨⟨-473757, 10⟩, ⟨-138945, 9⟩⟩,
  ⟨⟨-138939, 9⟩, ⟨-348769, 11⟩⟩,
  ⟨⟨-87189, 9⟩, ⟨-462163, 12⟩⟩,
  ⟨⟨-462149, 12⟩, ⟨-320111, 12⟩⟩,
  ⟨⟨-160051, 11⟩, ⟨-229995, 12⟩⟩,
  ⟨⟨-459979, 13⟩, ⟨-170387, 12⟩⟩,
  ⟨⟨-340767, 13⟩, ⟨-518115, 14⟩⟩,
  ⟨⟨-64763, 11⟩, ⟨-100649, 12⟩⟩,
  ⟨⟨-402589, 14⟩, ⟨-159377, 13⟩⟩,
  ⟨⟨-79687, 12⟩, ⟨-256475, 14⟩⟩,
  ⟨⟨-256471, 14⟩, ⟨-209267, 14⟩⟩,
  ⟨⟨-13079, 10⟩, ⟨-345657, 15⟩⟩,
  ⟨⟨-86413, 13⟩, ⟨-36063, 12⟩⟩,
  ⟨⟨-72125, 13⟩, ⟨-243033, 15⟩⟩,
  ⟨⟨-486059, 16⟩, ⟨-206393, 15⟩⟩,
  ⟨⟨-412781, 16⟩, ⟨-353047, 16⟩⟩,
  ⟨⟨-176521, 15⟩, ⟨-9495, 11⟩⟩,
  ⟨⟨-303837, 16⟩, ⟨-262919, 16⟩⟩,
  ⟨⟨-262915, 16⟩, ⟨-457191, 17⟩⟩,
  ⟨⟨-228593, 16⟩, ⟨-399159, 17⟩⟩,
  ⟨⟨-399155, 17⟩, ⟨-174875, 16⟩⟩,
  ⟨⟨-174873, 16⟩, ⟨-153703, 16⟩⟩,
  ⟨⟨-307403, 17⟩, ⟨-135449, 16⟩⟩,
  ⟨⟨-135447, 16⟩, ⟨-119625, 16⟩⟩,
  ⟨⟨-478495, 18⟩, ⟨-105839, 16⟩⟩,
  ⟨⟨-423351, 18⟩, ⟨-187547, 17⟩⟩,
  ⟨⟨-187545, 17⟩, ⟨-332679, 18⟩⟩,
  ⟨⟨-332675, 18⟩, ⟨-9227, 13⟩⟩,
  ⟨⟨-295261, 18⟩, ⟨-262145, 18⟩⟩,
  ⟨⟨-262143, 18⟩, ⟨-116371, 17⟩⟩,
  ⟨⟨-58185, 16⟩, ⟨-413133, 19⟩⟩,
  ⟨⟨-413129, 19⟩, ⟨-366417, 19⟩⟩,
  ⟨⟨-366413, 19⟩, ⟨-162323, 18⟩⟩,
  ⟨⟨-162321, 18⟩, ⟨-561, 10⟩⟩,
  ⟨⟨-71807, 17⟩, ⟨-63419, 17⟩⟩,
  ⟨⟨-507347, 20⟩, ⟨-223549, 19⟩⟩,
  ⟨⟨-447093, 20⟩, ⟨-392965, 20⟩⟩,
  ⟨⟨-392961, 20⟩, ⟨-86081, 18⟩⟩,
  ⟨⟨-1345, 12⟩, ⟨-300619, 20⟩⟩,
  ⟨⟨-37577, 17⟩, ⟨-261375, 20⟩⟩,
  ⟨⟨-65343, 18⟩, ⟨-226173, 20⟩⟩,
  ⟨⟨-452341, 21⟩, ⟨-389299, 21⟩⟩,
  ⟨⟨-194647, 20⟩, ⟨-166479, 20⟩⟩,
  ⟨⟨-166477, 20⟩, ⟨-141381, 20⟩⟩,
  ⟨⟨-282759, 21⟩, ⟨-476393, 22⟩⟩,
  ⟨⟨-476387, 22⟩, ⟨-397621, 22⟩⟩,
  ⟨⟨-397615, 22⟩, ⟨-82097, 20⟩⟩,
  ⟨⟨-328383, 22⟩, ⟨-267943, 22⟩⟩,
  ⟨⟨-133969, 21⟩, ⟨-431181, 23⟩⟩,
  ⟨⟨-215587, 22⟩, ⟨-170693, 22⟩⟩,
  ⟨⟨-341381, 23⟩, ⟨-265275, 23⟩⟩,
  ⟨⟨-132635, 22⟩, ⟨-403319, 24⟩⟩,
  ⟨⟨-403311, 24⟩, ⟨-74699, 22⟩⟩,
  ⟨⟨-298789, 24⟩, ⟨-26835, 21⟩⟩,
  ⟨⟨-429351, 25⟩, ⟨-18587, 21⟩⟩,
  ⟨⟨-297385, 25⟩, ⟨-394081, 26⟩⟩,
  ⟨⟨-197035, 25⟩, ⟨-494599, 27⟩⟩,
  ⟨⟨-494585, 27⟩, ⟨-36263, 24⟩⟩,
  ⟨⟨-145047, 26⟩, ⟨-19533, 24⟩⟩,
  ⟨⟨-78129, 26⟩, ⟨-301697, 29⟩⟩,
  ⟨⟨-301685, 29⟩, ⟨-63017, 28⟩⟩,
  ⟨⟨-504113, 31⟩, ⟨-346387, 32⟩⟩,
  ⟨⟨-346369, 32⟩, ⟨-90487, 32⟩⟩,
  ⟨⟨-180963, 33⟩, ⟨-506821, 37⟩⟩,
  ⟨⟨-506787, 37⟩, ⟨-191087, 39⟩⟩,
  ⟨⟨-191073, 39⟩, ⟨-205405, 44⟩⟩,
  ⟨⟨-205389, 44⟩, ⟨-257493, 52⟩⟩,
  ⟨⟨-514943, 53⟩, ⟨-33533, 63⟩⟩,
  ⟨⟨-134119, 65⟩, ⟨-262165, 100⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private def eulerianCoefficients : List ℤ := [
  0x1, 0x3ffffffffffffffffffad, 0x3e8ca816be291b89e243d253d80488394,
  0xffffffebb86580a05544924ba402ced0f68803f6c, 0x545666b01111bcd5ddea7e9d6f6585322491c35e1c309770, 0xfa30eadab6a8159c3b5c0bc5514c6607c6a4e91cf864b98cf6398,
  0x49a7bc1db256d9455605575498ea05cf4412fbf99b42f10f59ea9b3404, 0x3fe81dc9137e31d204bf6e6095dff640652b5fd39f4c09ff92de2e5574467c, 0xf33b286918ddfe6b64e9774211ae5774d1a8c66cddd8966f8fcae18057e043f62,
  0x14c6885f4d9d4dc2a18fc5c4e628ec8c6b9421dedf8eafbe09e3c5625329f68f12182, 0xc559b35746b0d259653a2e84b0491cb84a0a00a72faebfe8d1abc13945d76c060f74e5c, 0x3a7b215bca19115b9e8de81cdc888dc816327c5e5ee80138494e87864b5876770b34a9bc24,
  0x998c088e6ddf9c107d7e17cb2b161f5118572014106cd878fc832c4c6da7a7ce6397c70bd998, 0xf1bbb77832c71422752f91f8fc908631fe15ac3557133c0ef1c07436dd278b16aa7f06bb5e7730, 0xf2cfd92f463eaccf6cb960a8bea82f53c32747336b473feceefe8bce6c4cf0e671298bc812b227cc,
  0xa37bf693978c9fffb6cf8e4deb7f64967743f6a5461e3411c0318a197d60f29c9040d64c31bc2b2f34, 0x4cc7fc7d87563f1ca9fb5d242c20f39d682472a22b51b331c517bc0e435f7d711fd40ceca3db53aa3df9, 0x19fccda9e80b24de190c5e1c61f969ebd3eb7c9b1b3e3ea9d67db1b4a3f5e8d8201fac5c26255489c96c1d,
  0x68323e84a0a3912478f000c3734db3662e36ad33c250afbe56cf3a23cb77307cdb8f31bee411e32c27c60d0, 0x13c6247a5279338ecdb7b2eda060c0482d5275120249b2407c73dbc62ff7684f930ee2aa027a171df928ed730, 0x2e58fad598a408caaf5f229839cc3e6dacc7eaa1827d2472b6d529d29e7468c33fdd2aa10630ecadae537f0f00,
  0x553b1ecb86b0690ee0f53a5fe373e6a04ac101ce9a0ba792de7eff4746e2a2df8c7ff481f8fa2bf1c664db36fa0, 0x7cb356ac3e40c3c19fa99c52c661a8bf610404daf4c0415778f4752b85acdc17adadf3524d8a4b08ac7cef9ae190, 0x92eae41cadd80fdf22016a0865452c7ab04bc9bae581a032c45c96bec938e8086ecfd8bc52088e1bb9ffb3791e470,
  0x8cd950be61df55797b23e4ab5da9bb59ea35e6df5dff66b832d707e4caab6c69a4cbac5cf47be9d40d2b98f22aac78, 0x6ee1e9bffe4b71800d98cbe91e7c497986c3be3f33b13d4ecedb25101850a7d6d1ee7b21de6f26835f5557ab0ca6538, 0x4840e79c254d6d9cdc5490c4579b34b42551cd7dc41fb9cc8c8baf19d813f22e807fdf209532258b78f515e01b7547b0,
  0x273e6759b952b2593a48ff6e92b08d1ecd4a2eba8233058bf08c5495054f4a90a41cdc1dec0d73e866a4c8953e5cd1e50, 0x11e01796a25eaadcb4ae3895798c276b60b0eb01f7273a1c9d0d613613e26dde4b62ed44f8837876036cb3f8032e825fa0, 0x6dd73f50fd1d6326b433f75a58db8d8ed3161fe5ed2bf54c9332f819f60d8535d4a785aeeb63f71d4c040bb0bb713a7180,
  0x23bc5afc8946dd2a037009c5184b6ace19366e0764261c42b30826b3929698d7aa45e66fbcd261f0f9a4296d035c09bdd70, 0x9e3c3aa4666c9700d22e4b20529580e502fc4055383ad868f2d8893f4daf783caa43530e6ad0aa7f455b4fcc78b77a91290, 0x25624fb7f448a9673a9c4f5b8a2dffe0f05c40c8edaa680f143b1a5299917851de902383b0c6e65f73e5185ebe7c68359d82,
  0x790452cc224d78e2f643be914d0ac1538cda19281ce0d7c53c146883b723a0b21fe867b23e7a9018ee0d6efb6ceb06811aba, 0x15060ea3c838f82ef7bc58ec5468f966d3d2e3efb3b04eb9a42f64d80c90a532003aff1e83d76f6bda2a4d825c5caff4c05d8, 0x324ae93312083299f7b1b4543d1b6f5b9e104fd2c250b5e62cf423db4b0c013b33979f7490e4f25f91de475f9fcc489b1f828,
  0x67bd3b30e4f2ab9691d68c8e8bf3c208d4acf6a3d13407e4dbbef77322e143885eebe4d98ab7e66a8d6bf28e62d0015c5fce0, 0xb8ccaf5212f4450d342c716a6e57c326471a6380855cdabf9c4c8744c7a3cb0bee8fe536b493cfa2cb0b8d9724e1287886790, 0x11ca6621f7f9e4f5cbb306ed362bda2442b97983813277162ab1f72b531a731780cc377e375e41b7e40fb5c23bf9335f33fbf8,
  0x17b7623ab1497bb1c605f2a6d7df4e39d427a688b49c9a6a885f27b70377abf5d572d44e864feff5504317d78ff2a2d4b81308, 0x1b60ebfdd855f1f2439e1817b7d63a1b12c1adbcd18d03bbb58283e9d9b6d5186d0eb67533a3de41d6d0f9abf59e0214432b6c, 0x1b60ebfdd855f1f2439e1817b7d63a1b12c1adbcd18d03bbb58283e9d9b6d5186d0eb67533a3de41d6d0f9abf59e0214432b6c,
  0x17b7623ab1497bb1c605f2a6d7df4e39d427a688b49c9a6a885f27b70377abf5d572d44e864feff5504317d78ff2a2d4b81308, 0x11ca6621f7f9e4f5cbb306ed362bda2442b97983813277162ab1f72b531a731780cc377e375e41b7e40fb5c23bf9335f33fbf8, 0xb8ccaf5212f4450d342c716a6e57c326471a6380855cdabf9c4c8744c7a3cb0bee8fe536b493cfa2cb0b8d9724e1287886790,
  0x67bd3b30e4f2ab9691d68c8e8bf3c208d4acf6a3d13407e4dbbef77322e143885eebe4d98ab7e66a8d6bf28e62d0015c5fce0, 0x324ae93312083299f7b1b4543d1b6f5b9e104fd2c250b5e62cf423db4b0c013b33979f7490e4f25f91de475f9fcc489b1f828, 0x15060ea3c838f82ef7bc58ec5468f966d3d2e3efb3b04eb9a42f64d80c90a532003aff1e83d76f6bda2a4d825c5caff4c05d8,
  0x790452cc224d78e2f643be914d0ac1538cda19281ce0d7c53c146883b723a0b21fe867b23e7a9018ee0d6efb6ceb06811aba, 0x25624fb7f448a9673a9c4f5b8a2dffe0f05c40c8edaa680f143b1a5299917851de902383b0c6e65f73e5185ebe7c68359d82, 0x9e3c3aa4666c9700d22e4b20529580e502fc4055383ad868f2d8893f4daf783caa43530e6ad0aa7f455b4fcc78b77a91290,
  0x23bc5afc8946dd2a037009c5184b6ace19366e0764261c42b30826b3929698d7aa45e66fbcd261f0f9a4296d035c09bdd70, 0x6dd73f50fd1d6326b433f75a58db8d8ed3161fe5ed2bf54c9332f819f60d8535d4a785aeeb63f71d4c040bb0bb713a7180, 0x11e01796a25eaadcb4ae3895798c276b60b0eb01f7273a1c9d0d613613e26dde4b62ed44f8837876036cb3f8032e825fa0,
  0x273e6759b952b2593a48ff6e92b08d1ecd4a2eba8233058bf08c5495054f4a90a41cdc1dec0d73e866a4c8953e5cd1e50, 0x4840e79c254d6d9cdc5490c4579b34b42551cd7dc41fb9cc8c8baf19d813f22e807fdf209532258b78f515e01b7547b0, 0x6ee1e9bffe4b71800d98cbe91e7c497986c3be3f33b13d4ecedb25101850a7d6d1ee7b21de6f26835f5557ab0ca6538,
  0x8cd950be61df55797b23e4ab5da9bb59ea35e6df5dff66b832d707e4caab6c69a4cbac5cf47be9d40d2b98f22aac78, 0x92eae41cadd80fdf22016a0865452c7ab04bc9bae581a032c45c96bec938e8086ecfd8bc52088e1bb9ffb3791e470, 0x7cb356ac3e40c3c19fa99c52c661a8bf610404daf4c0415778f4752b85acdc17adadf3524d8a4b08ac7cef9ae190,
  0x553b1ecb86b0690ee0f53a5fe373e6a04ac101ce9a0ba792de7eff4746e2a2df8c7ff481f8fa2bf1c664db36fa0, 0x2e58fad598a408caaf5f229839cc3e6dacc7eaa1827d2472b6d529d29e7468c33fdd2aa10630ecadae537f0f00, 0x13c6247a5279338ecdb7b2eda060c0482d5275120249b2407c73dbc62ff7684f930ee2aa027a171df928ed730,
  0x68323e84a0a3912478f000c3734db3662e36ad33c250afbe56cf3a23cb77307cdb8f31bee411e32c27c60d0, 0x19fccda9e80b24de190c5e1c61f969ebd3eb7c9b1b3e3ea9d67db1b4a3f5e8d8201fac5c26255489c96c1d, 0x4cc7fc7d87563f1ca9fb5d242c20f39d682472a22b51b331c517bc0e435f7d711fd40ceca3db53aa3df9,
  0xa37bf693978c9fffb6cf8e4deb7f64967743f6a5461e3411c0318a197d60f29c9040d64c31bc2b2f34, 0xf2cfd92f463eaccf6cb960a8bea82f53c32747336b473feceefe8bce6c4cf0e671298bc812b227cc, 0xf1bbb77832c71422752f91f8fc908631fe15ac3557133c0ef1c07436dd278b16aa7f06bb5e7730,
  0x998c088e6ddf9c107d7e17cb2b161f5118572014106cd878fc832c4c6da7a7ce6397c70bd998, 0x3a7b215bca19115b9e8de81cdc888dc816327c5e5ee80138494e87864b5876770b34a9bc24, 0xc559b35746b0d259653a2e84b0491cb84a0a00a72faebfe8d1abc13945d76c060f74e5c,
  0x14c6885f4d9d4dc2a18fc5c4e628ec8c6b9421dedf8eafbe09e3c5625329f68f12182, 0xf33b286918ddfe6b64e9774211ae5774d1a8c66cddd8966f8fcae18057e043f62, 0x3fe81dc9137e31d204bf6e6095dff640652b5fd39f4c09ff92de2e5574467c,
  0x49a7bc1db256d9455605575498ea05cf4412fbf99b42f10f59ea9b3404, 0xfa30eadab6a8159c3b5c0bc5514c6607c6a4e91cf864b98cf6398, 0x545666b01111bcd5ddea7e9d6f6585322491c35e1c309770,
  0xffffffebb86580a05544924ba402ced0f68803f6c, 0x3e8ca816be291b89e243d253d80488394, 0x3ffffffffffffffffffad,
  0x1]

private theorem eulerianCoefficients_eq : descentCoeffs 82 = eulerianCoefficients := by
  decide +kernel

private theorem upper : upperOK (descentCoeffs 82) first gaps = true := by
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

private theorem lower_039 : lowerOK (rows.getD 39 []) gaps = true := by
  decide +kernel

private theorem lower (i : Fin (lastRepresentative 83 - 2)) :
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
  · exact lower_039

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 83) :
    StrictNegativeInterlacing (originalQuotient 83 k) (eulerian 82) 80 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N083
