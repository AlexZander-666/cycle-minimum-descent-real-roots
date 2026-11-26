import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentPackedData.C127L080.N079

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N079

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L080.N079 LongCycleBounds.DescentNecklace.Packed.C127L080.N079.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L080.N079 LongCycleBounds.DescentNecklace.Packed.C127L080.N079.rows

private theorem actual : RepresentativeChecks 79 previousNodes rows :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L080.N079 LongCycleBounds.DescentNecklace.Packed.C127L080.N079.dataChecks

private def first : LongCycleFinite.Dyadic := ⟨-302231454903657293676544, 0⟩

private def gaps : List Window := [
  ⟨⟨-302221655070868135477248, 0⟩, ⟨-60700907012096, 0⟩⟩,
  ⟨⟨-51904813989888, 0⟩, ⟨-6877134848, 0⟩⟩,
  ⟨⟨-4783112192, 0⟩, ⟨-35066368, 0⟩⟩,
  ⟨⟨-34776064, 0⟩, ⟨-1375668, 0⟩⟩,
  ⟨⟨-1374036, 0⟩, ⟨-289343, 1⟩⟩,
  ⟨⟨-144609, 0⟩, ⟨-438799, 4⟩⟩,
  ⟨⟨-109675, 2⟩, ⟨-487191, 6⟩⟩,
  ⟨⟨-487123, 6⟩, ⟨-350955, 7⟩⟩,
  ⟨⟨-43865, 4⟩, ⟨-304551, 8⟩⟩,
  ⟨⟨-304529, 8⟩, ⟨-303211, 9⟩⟩,
  ⟨⟨-303193, 9⟩, ⟨-335091, 10⟩⟩,
  ⟨⟨-335075, 10⟩, ⟨-401599, 11⟩⟩,
  ⟨⟨-401583, 11⟩, ⟨-64149, 9⟩⟩,
  ⟨⟨-513175, 12⟩, ⟨-345281, 12⟩⟩,
  ⟨⟨-172635, 11⟩, ⟨-484621, 13⟩⟩,
  ⟨⟨-1893, 5⟩, ⟨-352133, 13⟩⟩,
  ⟨⟨-352125, 13⟩, ⟨-263409, 13⟩⟩,
  ⟨⟨-263403, 13⟩, ⟨-100959, 12⟩⟩,
  ⟨⟨-100957, 12⟩, ⟨-316047, 14⟩⟩,
  ⟨⟨-316041, 14⟩, ⟨-503521, 15⟩⟩,
  ⟨⟨-503513, 15⟩, ⟨-101813, 13⟩⟩,
  ⟨⟨-407245, 15⟩, ⟨-83435, 13⟩⟩,
  ⟨⟨-333735, 15⟩, ⟨-17289, 11⟩⟩,
  ⟨⟨-276619, 15⟩, ⟨-231559, 15⟩⟩,
  ⟨⟨-463111, 16⟩, ⟨-391015, 16⟩⟩,
  ⟨⟨-195505, 15⟩, ⟨-332621, 16⟩⟩,
  ⟨⟨-41577, 13⟩, ⟨-2225, 9⟩⟩,
  ⟨⟨-71199, 14⟩, ⟨-122619, 15⟩⟩,
  ⟨⟨-490471, 17⟩, ⟨-212213, 16⟩⟩,
  ⟨⟨-424421, 17⟩, ⟨-368835, 17⟩⟩,
  ⟨⟨-368831, 17⟩, ⟨-160845, 16⟩⟩,
  ⟨⟨-160843, 16⟩, ⟨-281435, 17⟩⟩,
  ⟨⟨-281431, 17⟩, ⟨-493697, 18⟩⟩,
  ⟨⟨-123423, 16⟩, ⟨-433931, 18⟩⟩,
  ⟨⟨-433927, 18⟩, ⟨-191011, 17⟩⟩,
  ⟨⟨-191009, 17⟩, ⟨-336733, 18⟩⟩,
  ⟨⟨-168365, 17⟩, ⟨-148525, 17⟩⟩,
  ⟨⟨-148523, 17⟩, ⟨-131073, 17⟩⟩,
  ⟨⟨-262143, 18⟩, ⟨-231343, 18⟩⟩,
  ⟨⟨-462681, 19⟩, ⟨-204079, 18⟩⟩,
  ⟨⟨-204077, 18⟩, ⟨-179885, 18⟩⟩,
  ⟨⟨-179883, 18⟩, ⟨-158367, 18⟩⟩,
  ⟨⟨-158365, 18⟩, ⟨-278389, 19⟩⟩,
  ⟨⟨-139193, 18⟩, ⟨-122089, 18⟩⟩,
  ⟨⟨-488351, 20⟩, ⟨-427247, 20⟩⟩,
  ⟨⟨-213621, 19⟩, ⟨-372633, 20⟩⟩,
  ⟨⟨-372629, 20⟩, ⟨-323827, 20⟩⟩,
  ⟨⟨-323823, 20⟩, ⟨-280219, 20⟩⟩,
  ⟨⟨-280215, 20⟩, ⟨-482587, 21⟩⟩,
  ⟨⟨-241291, 20⟩, ⟨-206603, 20⟩⟩,
  ⟨⟨-413201, 21⟩, ⟨-43937, 18⟩⟩,
  ⟨⟨-351491, 21⟩, ⟨-296773, 21⟩⟩,
  ⟨⟨-296769, 21⟩, ⟨-496849, 22⟩⟩,
  ⟨⟨-496843, 22⟩, ⟨-411821, 22⟩⟩,
  ⟨⟨-411815, 22⟩, ⟨-337487, 22⟩⟩,
  ⟨⟨-168741, 21⟩, ⟨-272959, 22⟩⟩,
  ⟨⟨-136477, 21⟩, ⟨-6795, 17⟩⟩,
  ⟨⟨-434873, 23⟩, ⟨-340341, 23⟩⟩,
  ⟨⟨-340335, 23⟩, ⟨-521777, 24⟩⟩,
  ⟨⟨-65221, 21⟩, ⟨-195155, 23⟩⟩,
  ⟨⟨-390303, 24⟩, ⟨-35451, 21⟩⟩,
  ⟨⟨-141801, 23⟩, ⟨-199029, 24⟩⟩,
  ⟨⟨-12439, 20⟩, ⟨-267819, 25⟩⟩,
  ⟨⟨-66953, 23⟩, ⟨-342249, 26⟩⟩,
  ⟨⟨-342239, 26⟩, ⟨-410169, 27⟩⟩,
  ⟨⟨-102539, 25⟩, ⟨-453299, 28⟩⟩,
  ⟨⟨-453283, 28⟩, ⟨-112829, 27⟩⟩,
  ⟨⟨-225649, 28⟩, ⟨-391635, 30⟩⟩,
  ⟨⟨-391617, 30⟩, ⟨-70537, 29⟩⟩,
  ⟨⟨-282133, 31⟩, ⟨-313251, 33⟩⟩,
  ⟨⟨-313233, 33⟩, ⟨-237579, 35⟩⟩,
  ⟨⟨-475127, 36⟩, ⟨-199943, 38⟩⟩,
  ⟨⟨-399857, 39⟩, ⟨-252111, 43⟩⟩,
  ⟨⟨-504183, 44⟩, ⟨-407519, 51⟩⟩,
  ⟨⟨-407485, 51⟩, ⟨-339511, 64⟩⟩,
  ⟨⟨-339479, 64⟩, ⟨-262165, 96⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private def eulerianCoefficients : List ℤ := [
  0x1, 0x3fffffffffffffffffb1, 0xc5afe6ff2eefcbf94fd9829d87f5c82,
  0xffffffc2feb7b74052a00e105be0b1630b4f5c2, 0x228b6ad50b7fc69dfbbeadab52fbc8edd6f771dd97e64f, 0x316b4f2f60370a395ef4c0f8fe458fa68aff28f8f90dbc099bf,
  0x7da0730333da5bc1c53e2d29e07bc641c6c12640e1be04e195956bc, 0x3fd9391a7a99fda484cbeb95423fc588fa0e37d4fb4ac8645fc39b622bc, 0x976c90e920931f08a10212583ee9d101006094c64dcb4f5324114c087da957,
  0x873f0243c3db6bb3c1109d4f727f39dcc4bc9cc3757d77036c10ec4aaacc88e67, 0x367901f50e56de9851b2e2470547c256cd462af8f73cc96b28a5929ad3f9afd6e8f2, 0xb47772baf476f72dfb713b29b0775db31d81374c69f39e8af55b42b42b6fb443a165b2,
  0x152ff7ebe1e0e3da8d36ee16e5d57bae587ad4cd2b0ae6fd4c239fd97d48691d931101b19, 0x185268507ef2ab5d62563e4c4a2150e2d6c44667b5cfaff363f58c039f4d38f2eed944115e9, 0x12170848d1c19d6dd6a27575dea390d155ea50f66e3bfcce8c728ea12ff976a4b2ec0cec266a0,
  0x921e2e786c730fb8db888b9aba5aeb2c71e8aaea790c4189140d9492831e33cee2eaafd0287ea0, 0x33fb493324e22177a2d23203493cb35d46c17534e8a231a7c9cced1469d123792c6f0c10c876cf44, 0xd701dd72cd582fd96ab65fae711b1cd16694e7727522798a7e5ec8f99c8218bd86bb8213cdc71d804,
  0x296e42dda017ae1e90bbb2b0d804766326123f29deb6678342519e23886d2b2021bb8683f6c0a9489e8, 0x61432f89068b2dcc73ced33c9d35ae92ec4b8c3270a7f31b7121757d68ac80c4689d7a3777b6cc6476e8, 0xb1043c2e7a411a7eff0e18366fe7b448d78986c4faeb74b8c495b35e98476c42887c039d0f067736ed67c,
  0xfd9e17172bb71db30b7037425bd4c6b51a20a5bc918bba1db917e378a08b48f13d778d6156f3e2979daa3c, 0x121d425e074147a2708dc13c914f8ae37c33258d60da763c37b78764372a6502d55e38578963923fccb2d190, 0x10b2f6115ed479befbe7a27f6ff1b52407106cf9ccc6fe0007a59b424761e1e21c4265c989942352f977c7990,
  0xc8a6ef4ea92b29246b4e2bbb7eb9cb77516ced031a639df19195bc9c65ddddd009a83b481fd2e712cebf618cc, 0x7bcd6c2865b92ab3762a2af07c9f0cc99dbd8f3f9996ecce94eda29009f3355cc984d1f58d0d7414d73b4c480c, 0x3f396e730088b791d96e1db2aab8cbbd6596854e59f45498dee089e0c84948f0475643346730adc38de12410c08,
  0x1ae5c492db2e39a80d7d54ee3ca3625ae85bce4b69d2b82854c9a69e37efa97235bbf5fe7e7152a85aa89366a308, 0x9962104fd950760ed8f17ec81f988d756414bc9e3a7ec0ec474a3a850cb1730c4c30420427b2a75d250ec5437774, 0x2e05ad648dad126d8d152335b28ac3da10d01209d97fb9248eb027f484ea341c506f6cbac70ae093f07344d8abdb4,
  0xbacbe938dbd778559dad1d90bdd4a4ca1bc8cab827a158e39a32785c25065481bde45eec0579053b49f1ead12ba60, 0x2835d9ce01ba0c209acab0a895b4c154128ad925aa2e7f95b7412da9abba405349f169c9dfecec40a732561b89f260, 0x75e4358a08bc54fbad2081467ad14bf1d61d9f473c71bfe547bc612437c61986ed4f42752007bacc53888c6e39761e,
  0x127036a533ba1e2ff08a3fbc2b0d2aad153346fd709c534b8f276c14052832bbf9c6ed39555808bedb4685641e5bebe, 0x27783ce2e81cf3648653c16bd86ffd645bd20847bd0a0126c45e338a1ce0680c48a959ca5636dadf078b61ad69970dc, 0x486802a6df5230da4b939c9dd410528b12f0b9a182d8d0bab95ee7f54086a6a804c5204e955436d5fce5de3524d3e5c,
  0x71fe41682f0a02d810b43c9b0bff1a02f651b177347f32287c28eed91b71cb5b7a2c169ca9f901bba8098fe16d943c2, 0x9a2e2e5799dee6afce67d0fafb2a155cc9e6d80bfa5cdeaff2fa7f75311ba61c3afa31e3d51a4b5774101e01b11e0e2, 0xb34766cb38329fbb54d00dccf9ef2933fd0c9e56b1ebc8f37dab84a49c79bc48a20b2a5fa769cbb1c3a746b3f05a968,
  0xb34766cb38329fbb54d00dccf9ef2933fd0c9e56b1ebc8f37dab84a49c79bc48a20b2a5fa769cbb1c3a746b3f05a968, 0x9a2e2e5799dee6afce67d0fafb2a155cc9e6d80bfa5cdeaff2fa7f75311ba61c3afa31e3d51a4b5774101e01b11e0e2, 0x71fe41682f0a02d810b43c9b0bff1a02f651b177347f32287c28eed91b71cb5b7a2c169ca9f901bba8098fe16d943c2,
  0x486802a6df5230da4b939c9dd410528b12f0b9a182d8d0bab95ee7f54086a6a804c5204e955436d5fce5de3524d3e5c, 0x27783ce2e81cf3648653c16bd86ffd645bd20847bd0a0126c45e338a1ce0680c48a959ca5636dadf078b61ad69970dc, 0x127036a533ba1e2ff08a3fbc2b0d2aad153346fd709c534b8f276c14052832bbf9c6ed39555808bedb4685641e5bebe,
  0x75e4358a08bc54fbad2081467ad14bf1d61d9f473c71bfe547bc612437c61986ed4f42752007bacc53888c6e39761e, 0x2835d9ce01ba0c209acab0a895b4c154128ad925aa2e7f95b7412da9abba405349f169c9dfecec40a732561b89f260, 0xbacbe938dbd778559dad1d90bdd4a4ca1bc8cab827a158e39a32785c25065481bde45eec0579053b49f1ead12ba60,
  0x2e05ad648dad126d8d152335b28ac3da10d01209d97fb9248eb027f484ea341c506f6cbac70ae093f07344d8abdb4, 0x9962104fd950760ed8f17ec81f988d756414bc9e3a7ec0ec474a3a850cb1730c4c30420427b2a75d250ec5437774, 0x1ae5c492db2e39a80d7d54ee3ca3625ae85bce4b69d2b82854c9a69e37efa97235bbf5fe7e7152a85aa89366a308,
  0x3f396e730088b791d96e1db2aab8cbbd6596854e59f45498dee089e0c84948f0475643346730adc38de12410c08, 0x7bcd6c2865b92ab3762a2af07c9f0cc99dbd8f3f9996ecce94eda29009f3355cc984d1f58d0d7414d73b4c480c, 0xc8a6ef4ea92b29246b4e2bbb7eb9cb77516ced031a639df19195bc9c65ddddd009a83b481fd2e712cebf618cc,
  0x10b2f6115ed479befbe7a27f6ff1b52407106cf9ccc6fe0007a59b424761e1e21c4265c989942352f977c7990, 0x121d425e074147a2708dc13c914f8ae37c33258d60da763c37b78764372a6502d55e38578963923fccb2d190, 0xfd9e17172bb71db30b7037425bd4c6b51a20a5bc918bba1db917e378a08b48f13d778d6156f3e2979daa3c,
  0xb1043c2e7a411a7eff0e18366fe7b448d78986c4faeb74b8c495b35e98476c42887c039d0f067736ed67c, 0x61432f89068b2dcc73ced33c9d35ae92ec4b8c3270a7f31b7121757d68ac80c4689d7a3777b6cc6476e8, 0x296e42dda017ae1e90bbb2b0d804766326123f29deb6678342519e23886d2b2021bb8683f6c0a9489e8,
  0xd701dd72cd582fd96ab65fae711b1cd16694e7727522798a7e5ec8f99c8218bd86bb8213cdc71d804, 0x33fb493324e22177a2d23203493cb35d46c17534e8a231a7c9cced1469d123792c6f0c10c876cf44, 0x921e2e786c730fb8db888b9aba5aeb2c71e8aaea790c4189140d9492831e33cee2eaafd0287ea0,
  0x12170848d1c19d6dd6a27575dea390d155ea50f66e3bfcce8c728ea12ff976a4b2ec0cec266a0, 0x185268507ef2ab5d62563e4c4a2150e2d6c44667b5cfaff363f58c039f4d38f2eed944115e9, 0x152ff7ebe1e0e3da8d36ee16e5d57bae587ad4cd2b0ae6fd4c239fd97d48691d931101b19,
  0xb47772baf476f72dfb713b29b0775db31d81374c69f39e8af55b42b42b6fb443a165b2, 0x367901f50e56de9851b2e2470547c256cd462af8f73cc96b28a5929ad3f9afd6e8f2, 0x873f0243c3db6bb3c1109d4f727f39dcc4bc9cc3757d77036c10ec4aaacc88e67,
  0x976c90e920931f08a10212583ee9d101006094c64dcb4f5324114c087da957, 0x3fd9391a7a99fda484cbeb95423fc588fa0e37d4fb4ac8645fc39b622bc, 0x7da0730333da5bc1c53e2d29e07bc641c6c12640e1be04e195956bc,
  0x316b4f2f60370a395ef4c0f8fe458fa68aff28f8f90dbc099bf, 0x228b6ad50b7fc69dfbbeadab52fbc8edd6f771dd97e64f, 0xffffffc2feb7b74052a00e105be0b1630b4f5c2,
  0xc5afe6ff2eefcbf94fd9829d87f5c82, 0x3fffffffffffffffffb1, 0x1]

private theorem eulerianCoefficients_eq : descentCoeffs 78 = eulerianCoefficients := by
  decide +kernel

private theorem upper : upperOK (descentCoeffs 78) first gaps = true := by
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

private theorem lower (i : Fin (lastRepresentative 79 - 2)) :
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

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 79) :
    StrictNegativeInterlacing (originalQuotient 79 k) (eulerian 78) 76 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N079
