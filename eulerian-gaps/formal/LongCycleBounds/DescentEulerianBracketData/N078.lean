import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentPackedData.C127L080.N078

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N078

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L080.N078 LongCycleBounds.DescentNecklace.Packed.C127L080.N078.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L080.N078 LongCycleBounds.DescentNecklace.Packed.C127L080.N078.rows

private theorem actual : RepresentativeChecks 78 previousNodes rows :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L080.N078 LongCycleBounds.DescentNecklace.Packed.C127L080.N078.dataChecks

private def first : LongCycleFinite.Dyadic := ⟨-151115727451828646838272, 0⟩

private def gaps : List Window := [
  ⟨⟨-151110827535434067738624, 0⟩, ⟨-36511919636480, 0⟩⟩,
  ⟨⟨-32113873125376, 0⟩, ⟨-5494652928, 0⟩⟩,
  ⟨⟨-4071587840, 0⟩, ⟨-27890496, 0⟩⟩,
  ⟨⟨-27730112, 0⟩, ⟨-1143564, 0⟩⟩,
  ⟨⟨-1142256, 0⟩, ⟨-494425, 2⟩⟩,
  ⟨⟨-247109, 1⟩, ⟨-382479, 4⟩⟩,
  ⟨⟨-382395, 4⟩, ⟨-107773, 4⟩⟩,
  ⟨⟨-431033, 6⟩, ⟨-78563, 5⟩⟩,
  ⟨⟨-314221, 7⟩, ⟨-137643, 7⟩⟩,
  ⟨⟨-137633, 7⟩, ⟨-138095, 8⟩⟩,
  ⟨⟨-138087, 8⟩, ⟨-76793, 8⟩⟩,
  ⟨⟨-307157, 10⟩, ⟨-185037, 10⟩⟩,
  ⟨⟨-370059, 11⟩, ⟨-118757, 10⟩⟩,
  ⟨⟨-118753, 10⟩, ⟨-40103, 9⟩⟩,
  ⟨⟨-160407, 11⟩, ⟨-451743, 13⟩⟩,
  ⟨⟨-112933, 11⟩, ⟨-41145, 10⟩⟩,
  ⟨⟨-5143, 7⟩, ⟨-246803, 13⟩⟩,
  ⟨⟨-123399, 12⟩, ⟨-379143, 14⟩⟩,
  ⟨⟨-379135, 14⟩, ⟨-18577, 10⟩⟩,
  ⟨⟨-148613, 13⟩, ⟨-474239, 15⟩⟩,
  ⟨⟨-59279, 12⟩, ⟨-192019, 14⟩⟩,
  ⟨⟨-12001, 10⟩, ⟨-157517, 14⟩⟩,
  ⟨⟨-315029, 15⟩, ⟨-522671, 16⟩⟩,
  ⟨⟨-65333, 13⟩, ⟨-54725, 13⟩⟩,
  ⟨⟨-218897, 15⟩, ⟨-369819, 16⟩⟩,
  ⟨⟨-184907, 15⟩, ⟨-314687, 16⟩⟩,
  ⟨⟨-314683, 16⟩, ⟨-269487, 16⟩⟩,
  ⟨⟨-269483, 16⟩, ⟨-116029, 15⟩⟩,
  ⟨⟨-232055, 16⟩, ⟨-12549, 12⟩⟩,
  ⟨⟨-100391, 15⟩, ⟨-174437, 16⟩⟩,
  ⟨⟨-174435, 16⟩, ⟨-304155, 17⟩⟩,
  ⟨⟨-304151, 17⟩, ⟨-132973, 16⟩⟩,
  ⟨⟨-265943, 17⟩, ⟨-233101, 17⟩⟩,
  ⟨⟨-466197, 18⟩, ⟨-204707, 17⟩⟩,
  ⟨⟨-204705, 17⟩, ⟨-360073, 18⟩⟩,
  ⟨⟨-360069, 18⟩, ⟨-19813, 14⟩⟩,
  ⟨⟨-317005, 18⟩, ⟨-69817, 16⟩⟩,
  ⟨⟨-279265, 18⟩, ⟨-246071, 18⟩⟩,
  ⟨⟨-246069, 18⟩, ⟨-433555, 19⟩⟩,
  ⟨⟨-216775, 18⟩, ⟨-381701, 19⟩⟩,
  ⟨⟨-381697, 19⟩, ⟨-167851, 18⟩⟩,
  ⟨⟨-167849, 18⟩, ⟨-36851, 16⟩⟩,
  ⟨⟨-294805, 19⟩, ⟨-258399, 19⟩⟩,
  ⟨⟨-64599, 17⟩, ⟨-451875, 20⟩⟩,
  ⟨⟨-225935, 19⟩, ⟨-196977, 19⟩⟩,
  ⟨⟨-196975, 19⟩, ⟨-85565, 18⟩⟩,
  ⟨⟨-21391, 16⟩, ⟨-296133, 20⟩⟩,
  ⟨⟨-148065, 19⟩, ⟨-255003, 20⟩⟩,
  ⟨⟨-31875, 17⟩, ⟨-27297, 17⟩⟩,
  ⟨⟨-436747, 21⟩, ⟨-371647, 21⟩⟩,
  ⟨⟨-185821, 20⟩, ⟨-313933, 21⟩⟩,
  ⟨⟨-313929, 21⟩, ⟨-262959, 21⟩⟩,
  ⟨⟨-262955, 21⟩, ⟨-436271, 22⟩⟩,
  ⟨⟨-436265, 22⟩, ⟨-89471, 20⟩⟩,
  ⟨⟨-357879, 22⟩, ⟨-289813, 22⟩⟩,
  ⟨⟨-289809, 22⟩, ⟨-462405, 23⟩⟩,
  ⟨⟨-231199, 22⟩, ⟨-181255, 22⟩⟩,
  ⟨⟨-362503, 23⟩, ⟨-69611, 21⟩⟩,
  ⟨⟨-139219, 22⟩, ⟨-417555, 24⟩⟩,
  ⟨⟨-417547, 24⟩, ⟨-38031, 21⟩⟩,
  ⟨⟨-304241, 24⟩, ⟨-53551, 22⟩⟩,
  ⟨⟨-214199, 24⟩, ⟨-36167, 22⟩⟩,
  ⟨⟨-18083, 21⟩, ⟨-5803, 20⟩⟩,
  ⟨⟨-371381, 26⟩, ⟨-223727, 26⟩⟩,
  ⟨⟨-447439, 27⟩, ⟨-497659, 28⟩⟩,
  ⟨⟨-248821, 27⟩, ⟨-499297, 29⟩⟩,
  ⟨⟨-499277, 29⟩, ⟨-218691, 29⟩⟩,
  ⟨⟨-218681, 29⟩, ⟨-79711, 29⟩⟩,
  ⟨⟨-79707, 29⟩, ⟨-44923, 30⟩⟩,
  ⟨⟨-179681, 32⟩, ⟨-139031, 34⟩⟩,
  ⟨⟨-278043, 35⟩, ⟨-481049, 39⟩⟩,
  ⟨⟨-240507, 38⟩, ⟨-157803, 42⟩⟩,
  ⟨⟨-315581, 43⟩, ⟨-271791, 50⟩⟩,
  ⟨⟨-33971, 47⟩, ⟨-254637, 63⟩⟩,
  ⟨⟨-254613, 63⟩, ⟨-262149, 95⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private def eulerianCoefficients : List ℤ := [
  0x1, 0x1fffffffffffffffffb2, 0x41e54cffba1d43fdc54880df2d5268e,
  0x3fffffebec228a15330348ade3e8bc00310aa8a, 0x6e8aebc358007185f3335864728ba898d5063655aebaf, 0x83c87f1a07f63b03518ed1a8f02d1d4c951ee09b3428cde624,
  0x11f204dafed79a468886bfbc74b75d5a1bd81350d90083bcda25f84, 0x7fa87df643ba9fb176781c6c29f6cd5c2c20fdcf3fbd327facc635b4a4, 0x10cf4ba6137882e3a99bf6d562d0b464182163f8fd3c6e6625e8018988b247,
  0xd7f0d3af3f7253321208478b2a0822eaee8747a085f56a3eec15860675e4d9ba, 0x4ee83741340e91c90c3768d74c18232af2b872f72f6a7a8445b8871bf7a65bb5ede, 0xeee6b31a19e6a2e4acbd6ed8e3e0f62a778bc3e3fe7c1637e49f12a8886e3a2f74c22,
  0x19c7d9297c7dccca87b42dd9025bfaafda80036834040d8950e5c37e5fcb5e65a1060969, 0x1b5432c72be5a0587aec82a6e52d68407bd79066b5206d2074b350af59093571a6d5d655e0, 0x12d72a1fb0133a95d1d403a59cdca588e21cbe9ebf5d501bc710ce429c5b01edc8de9f8b8760,
  0x8d7b3b1aa01e544dfce55eb4f8c09e6fc243980167f44ad23e1071d01ea3ce555e7be68cd22e0, 0x2ee88376b28cde0ff5499f404780bd25055aff52b7b41d32b01ac146f418db09109774a8d9350c4, 0xb52ea1e320b5e29c1a0367c3aaba2a716761f96dff6eb7a14223eb7c2e87440afe06983f9e3dc168,
  0x20a76f2732d510e257088bb908a5403940adf252f465804598ed2136490c5e36b6534efa21d6f3f558, 0x47ca13ef31767586a16648d3f9c613d161e92aaddb76d86f85823f1184abb8d7d6e038cfdb21ce88bc8, 0x7a7a3fbeb18f70a984f176a35c6e583973514b81363ee148c34ddc407a12ae013e5335e611cfda39dd7c,
  0xa49db9613ead3872666d6b85ceba55232282944f205712e0612b4f9603e6a30dca9c61bafdcefc5d9f870, 0xb091d72ebc1546d217f7c02f2c58fcef5b94b7ed0a24697c1a958e81d4ba569d7065165341e14bacbd6970, 0x98d55d3c973f5bd0678d491de862cd4602e692bb3f815e39e06d0c59b646b903f6006dddcebc8948fc87370,
  0x6bc8ea027bb0826a889dacff7ab1401b3b6695cc8c27e3e2268e8ccdbe58ed4d91c535d40e37c3e9dd1b6e0c, 0x3e7433839ed72733539e79ec0ee79a29d5320b38c5469062ee1ed840e3691b3872abafe2dc5ff18d2f0cb04e8, 0x1df2dc6f90c099d75cb54a08b8b52fa8d450cda53a012ef95930c1280f767ae8c7233177e4fe55bf5586428538,
  0xbf5ef3bc9e90f6ef1278d3f247b05a2712d8c2fb67046be16de401422c651b10c9b665d7d9cf20afe119dcca08, 0x4000d67585b50c0b1e87aab21927c8bec387f1f3614f633a9ecd12e8e5878f511d205972c1bde72943e9c6b2c34, 0x1202f140080b6c550687062741fce14b7e9b39fcf0ffbf8be9c18c721a1f9a7ed20f0eb97ffa6a4f7d0a69803e20,
  0x4485b8806502af24684e79583dddeff36b564063c895baf7abd596348fd2552c03fb750802dbc12fe8aecd94dfa0, 0xdd0a677379746fc75d22430b12c812330eb01a9ac2d81211f5a7b8b02a951581a9b1fa6b3b349e46dbd1f2e9a720, 0x25e6f3dace048ff3529d4288f700a71d697171b2258b1d67c887dffa746c45a793ca5131629d3962b651da8fa1a9e,
  0x58aa49a3b109e888cb6df8c475b518d9b22fb4bd2d42cc3e9d65eebc326321cf332fe90c7102fd6d366a6933bbcbc, 0xb13a4ad272b8ab57de14e049b85e16d3b0f7769b3c6a3adb7755716c0194fa6b4f75e0ce404ba3351758721270004, 0x12f3355ee63ebe412090ef87c0ee73dee56dd93431a4e05ff02522a00c8f63d1c66908aff91fc83007fd56b005570c,
  0x1bc89397d0b6302f2e5d4f7f6f5fa36520e4e77bc2ac476d40c4f3df8ee8632b98cc451b20dfd166bc22d4e5c87582, 0x22f0ed87d22004b8cd4dc59613457a6260ad971a75b0976f27292e8a3ddb035cd906363bec270ea1c4320bfb509b58, 0x25b69903254943408b4dcb6b6676c15487f0ac8bb607829c8eac89f763370eb8016dcca1941d99e4a7dcc88323a018,
  0x22f0ed87d22004b8cd4dc59613457a6260ad971a75b0976f27292e8a3ddb035cd906363bec270ea1c4320bfb509b58, 0x1bc89397d0b6302f2e5d4f7f6f5fa36520e4e77bc2ac476d40c4f3df8ee8632b98cc451b20dfd166bc22d4e5c87582, 0x12f3355ee63ebe412090ef87c0ee73dee56dd93431a4e05ff02522a00c8f63d1c66908aff91fc83007fd56b005570c,
  0xb13a4ad272b8ab57de14e049b85e16d3b0f7769b3c6a3adb7755716c0194fa6b4f75e0ce404ba3351758721270004, 0x58aa49a3b109e888cb6df8c475b518d9b22fb4bd2d42cc3e9d65eebc326321cf332fe90c7102fd6d366a6933bbcbc, 0x25e6f3dace048ff3529d4288f700a71d697171b2258b1d67c887dffa746c45a793ca5131629d3962b651da8fa1a9e,
  0xdd0a677379746fc75d22430b12c812330eb01a9ac2d81211f5a7b8b02a951581a9b1fa6b3b349e46dbd1f2e9a720, 0x4485b8806502af24684e79583dddeff36b564063c895baf7abd596348fd2552c03fb750802dbc12fe8aecd94dfa0, 0x1202f140080b6c550687062741fce14b7e9b39fcf0ffbf8be9c18c721a1f9a7ed20f0eb97ffa6a4f7d0a69803e20,
  0x4000d67585b50c0b1e87aab21927c8bec387f1f3614f633a9ecd12e8e5878f511d205972c1bde72943e9c6b2c34, 0xbf5ef3bc9e90f6ef1278d3f247b05a2712d8c2fb67046be16de401422c651b10c9b665d7d9cf20afe119dcca08, 0x1df2dc6f90c099d75cb54a08b8b52fa8d450cda53a012ef95930c1280f767ae8c7233177e4fe55bf5586428538,
  0x3e7433839ed72733539e79ec0ee79a29d5320b38c5469062ee1ed840e3691b3872abafe2dc5ff18d2f0cb04e8, 0x6bc8ea027bb0826a889dacff7ab1401b3b6695cc8c27e3e2268e8ccdbe58ed4d91c535d40e37c3e9dd1b6e0c, 0x98d55d3c973f5bd0678d491de862cd4602e692bb3f815e39e06d0c59b646b903f6006dddcebc8948fc87370,
  0xb091d72ebc1546d217f7c02f2c58fcef5b94b7ed0a24697c1a958e81d4ba569d7065165341e14bacbd6970, 0xa49db9613ead3872666d6b85ceba55232282944f205712e0612b4f9603e6a30dca9c61bafdcefc5d9f870, 0x7a7a3fbeb18f70a984f176a35c6e583973514b81363ee148c34ddc407a12ae013e5335e611cfda39dd7c,
  0x47ca13ef31767586a16648d3f9c613d161e92aaddb76d86f85823f1184abb8d7d6e038cfdb21ce88bc8, 0x20a76f2732d510e257088bb908a5403940adf252f465804598ed2136490c5e36b6534efa21d6f3f558, 0xb52ea1e320b5e29c1a0367c3aaba2a716761f96dff6eb7a14223eb7c2e87440afe06983f9e3dc168,
  0x2ee88376b28cde0ff5499f404780bd25055aff52b7b41d32b01ac146f418db09109774a8d9350c4, 0x8d7b3b1aa01e544dfce55eb4f8c09e6fc243980167f44ad23e1071d01ea3ce555e7be68cd22e0, 0x12d72a1fb0133a95d1d403a59cdca588e21cbe9ebf5d501bc710ce429c5b01edc8de9f8b8760,
  0x1b5432c72be5a0587aec82a6e52d68407bd79066b5206d2074b350af59093571a6d5d655e0, 0x19c7d9297c7dccca87b42dd9025bfaafda80036834040d8950e5c37e5fcb5e65a1060969, 0xeee6b31a19e6a2e4acbd6ed8e3e0f62a778bc3e3fe7c1637e49f12a8886e3a2f74c22,
  0x4ee83741340e91c90c3768d74c18232af2b872f72f6a7a8445b8871bf7a65bb5ede, 0xd7f0d3af3f7253321208478b2a0822eaee8747a085f56a3eec15860675e4d9ba, 0x10cf4ba6137882e3a99bf6d562d0b464182163f8fd3c6e6625e8018988b247,
  0x7fa87df643ba9fb176781c6c29f6cd5c2c20fdcf3fbd327facc635b4a4, 0x11f204dafed79a468886bfbc74b75d5a1bd81350d90083bcda25f84, 0x83c87f1a07f63b03518ed1a8f02d1d4c951ee09b3428cde624,
  0x6e8aebc358007185f3335864728ba898d5063655aebaf, 0x3fffffebec228a15330348ade3e8bc00310aa8a, 0x41e54cffba1d43fdc54880df2d5268e,
  0x1fffffffffffffffffb2, 0x1]

private theorem eulerianCoefficients_eq : descentCoeffs 77 = eulerianCoefficients := by
  decide +kernel

private theorem upper : upperOK (descentCoeffs 77) first gaps = true := by
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

private theorem lower (i : Fin (lastRepresentative 78 - 2)) :
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

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 78) :
    StrictNegativeInterlacing (originalQuotient 78 k) (eulerian 77) 75 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N078
