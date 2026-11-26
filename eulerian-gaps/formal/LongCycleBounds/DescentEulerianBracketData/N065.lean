import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentPackedData.C127L072.N065

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N065

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L072.N065 LongCycleBounds.DescentNecklace.Packed.C127L072.N065.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L072.N065 LongCycleBounds.DescentNecklace.Packed.C127L072.N065.rows

private theorem actual : RepresentativeChecks 65 previousNodes rows :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L072.N065 LongCycleBounds.DescentNecklace.Packed.C127L072.N065.dataChecks

private def first : LongCycleFinite.Dyadic := ⟨-18446744073709551616, 0⟩

private def gaps : List Window := [
  ⟨⟨-18446145939384041472, 0⟩, ⟨-186417938432, 0⟩⟩,
  ⟨⟨-185880543232, 0⟩, ⟨-103944448, 0⟩⟩,
  ⟨⟨-96371456, 0⟩, ⟨-1494592, 0⟩⟩,
  ⟨⟨-1490168, 0⟩, ⟨-410535, 2⟩⟩,
  ⟨⟨-410265, 2⟩, ⟨-506227, 5⟩⟩,
  ⟨⟨-253043, 4⟩, ⟨-506733, 7⟩⟩,
  ⟨⟨-506653, 7⟩, ⟨-43377, 5⟩⟩,
  ⟨⟨-86745, 6⟩, ⟨-36801, 6⟩⟩,
  ⟨⟨-147193, 8⟩, ⟨-145513, 9⟩⟩,
  ⟨⟨-291009, 10⟩, ⟨-161019, 10⟩⟩,
  ⟨⟨-322023, 11⟩, ⟨-388161, 12⟩⟩,
  ⟨⟨-194073, 11⟩, ⟨-62493, 10⟩⟩,
  ⟨⟨-62491, 10⟩, ⟨-339283, 13⟩⟩,
  ⟨⟨-169637, 12⟩, ⟨-480271, 14⟩⟩,
  ⟨⟨-240129, 13⟩, ⟨-87935, 12⟩⟩,
  ⟨⟨-351731, 14⟩, ⟨-264945, 14⟩⟩,
  ⟨⟨-264939, 14⟩, ⟨-408543, 15⟩⟩,
  ⟨⟨-51067, 12⟩, ⟨-160583, 14⟩⟩,
  ⟨⟨-40145, 12⟩, ⟨-513281, 16⟩⟩,
  ⟨⟨-513273, 16⟩, ⟨-12995, 11⟩⟩,
  ⟨⟨-207917, 15⟩, ⟨-170425, 15⟩⟩,
  ⟨⟨-340845, 16⟩, ⟨-282147, 16⟩⟩,
  ⟨⟨-282143, 16⟩, ⟨-471003, 17⟩⟩,
  ⟨⟨-117749, 15⟩, ⟨-24743, 13⟩⟩,
  ⟨⟨-395883, 17⟩, ⟨-334695, 17⟩⟩,
  ⟨⟨-334691, 17⟩, ⟨-284317, 17⟩⟩,
  ⟨⟨-284313, 17⟩, ⟨-484899, 18⟩⟩,
  ⟨⟨-484893, 18⟩, ⟨-25921, 14⟩⟩,
  ⟨⟨-414731, 18⟩, ⟨-355503, 18⟩⟩,
  ⟨⟨-355499, 18⟩, ⟨-305167, 18⟩⟩,
  ⟨⟨-305163, 18⟩, ⟨-131073, 17⟩⟩,
  ⟨⟨-262143, 18⟩, ⟨-112595, 17⟩⟩,
  ⟨⟨-450375, 19⟩, ⟨-193305, 18⟩⟩,
  ⟨⟨-386605, 19⟩, ⟨-165697, 18⟩⟩,
  ⟨⟨-165695, 18⟩, ⟨-141721, 18⟩⟩,
  ⟨⟨-141719, 18⟩, ⟨-483407, 20⟩⟩,
  ⟨⟨-241701, 19⟩, ⟨-205323, 19⟩⟩,
  ⟨⟨-25665, 16⟩, ⟨-10849, 15⟩⟩,
  ⟨⟨-347163, 20⟩, ⟨-72951, 18⟩⟩,
  ⟨⟨-36475, 17⟩, ⟨-487129, 21⟩⟩,
  ⟨⟨-487123, 21⟩, ⟨-100807, 19⟩⟩,
  ⟨⟨-403223, 21⟩, ⟨-330513, 21⟩⟩,
  ⟨⟨-82627, 19⟩, ⟨-66943, 19⟩⟩,
  ⟨⟨-33471, 18⟩, ⟨-427941, 22⟩⟩,
  ⟨⟨-213967, 21⟩, ⟨-84105, 20⟩⟩,
  ⟨⟨-168207, 21⟩, ⟨-259377, 22⟩⟩,
  ⟨⟨-518745, 23⟩, ⟨-390749, 23⟩⟩,
  ⟨⟨-390741, 23⟩, ⟨-286179, 23⟩⟩,
  ⟨⟨-286173, 23⟩, ⟨-101275, 22⟩⟩,
  ⟨⟨-202545, 23⟩, ⟨-274919, 24⟩⟩,
  ⟨⟨-274911, 24⟩, ⟨-177047, 24⟩⟩,
  ⟨⟨-88521, 23⟩, ⟨-426797, 26⟩⟩,
  ⟨⟨-426783, 26⟩, ⟨-236137, 26⟩⟩,
  ⟨⟨-472257, 27⟩, ⟨-466853, 28⟩⟩,
  ⟨⟨-233417, 27⟩, ⟨-396075, 29⟩⟩,
  ⟨⟨-49507, 26⟩, ⟨-271231, 30⟩⟩,
  ⟨⟨-16951, 26⟩, ⟨-271549, 32⟩⟩,
  ⟨⟨-271531, 32⟩, ⟨-41867, 32⟩⟩,
  ⟨⟨-5233, 29⟩, ⟨-184191, 38⟩⟩,
  ⟨⟨-368353, 39⟩, ⟨-360763, 45⟩⟩,
  ⟨⟨-360733, 45⟩, ⟨-193675, 55⟩⟩,
  ⟨⟨-193657, 55⟩, ⟨-262165, 82⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private def eulerianCoefficients : List ℤ := [
  0x1, 0xffffffffffffffbf, 0x2b56d4af4e7932278c797ec521,
  0xfffff4fef3ff74b23a43f55526d1581f, 0x184ec2e9415a165ab95b0625ba42bfe5341bd1, 0x2b50a8a7b13fd6cda173787e40f5efb8f14cd74cef,
  0xcb121b7c623823a0e0e4590561929fb0ef1c08313feb1, 0xfcc59b6fbcd4f313f918857b53308bebdc3d88f589177f8f, 0x715b0424347ecd15d1f6ce28f34ca0e510d95d297bce8aa90e9,
  0x167a32eb90b90b87da4e055a83e9c82e8c9552da61a81a1b07f6d7, 0x24637ab353512eb2cbf3f71ab32176ee921f61eceaa8186747871789, 0x215802943dcc916993c53a6f410751657e026fb9d3d26fba14aa7cf9b7,
  0x12af0205f7591c68ee1d61cc75eb3fc10ecd2d3f2ccfc2373f6b1c976019, 0x6ca9a9a4fd058cd35adb5acb845f4bbdd08d6481e21fc5d0aaa5706d150a7, 0x1ad53b8efb0488eadde41f18d986a5f5df4b56547e0a1ed83fb867ed8a37e79,
  0x4ab67a9f593a838d1a72de038e7b7f052806ed1cdec4f3addb227f110d3f23c7, 0x9702842e1faa1c5e2f126d8bc0a60b143c446e592c365334d48c42b944616c355, 0xe2ff4f6360b0c4cc07c962836a43d5bf85d5fcaaa3323575255d7ea1aea09e7b6b,
  0x102e794d9a07a9423681af3c1471463c3559f9acdf9318220ca9ef328ab07de7f7f5, 0xe3d50f75b265fd92991eb23443b8615f4832d51761dae4e0cd9516fbbeec439f324b, 0x9cde4336e2fc187c1a62d29b1a33cdeb712107f09a2640a2f2766ad552e4dabbef0a5,
  0x5583678fef1db8f41e5908235436d77cff7853523271b49eb32c76fa9ada83d3de7b1b, 0x254735b115c9924e39a3ede4884c8c2b0f7151e3dcfc65200ea38297ed15a8487de9605, 0xd1b2a2899887b46e19514d335df2180a6f033d0d1e81f9b07aed99085b3247b8183b93b,
  0x3be29560e1d5ca6abe450aec4857af47b02608f67e07b91eef1ec40c509f9e2bd4d2560d, 0xdf9b0f222940b22a42be05d3bf54d686644d145d15dbb4eeb79c5041a01d4d765fb1a4b3, 0x2adb86a5bfbbf8c35869208fec001a2346e870ea23d7ec1afd5c9d68a5c1ccfe3c4d3c82d,
  0x6c63a507ed9a847b34ff25f638a4cb96c41fcdb51996bb38e7ee49daf5fe26b5014564213, 0xe2d28ea50f6fbee0e8148b8c2dcf13da9cdc3e4025d2be120aae538a855d5c7ccb5518d3d, 0x189c76826bb4db6c500759a1181776452106c419642d5fe1746f7b73ccedd5c7eacfc78a83,
  0x23836be6f56fc46916b585e9bbe014278344571e899ed5333f7a1f5b7c0ed7da6dc601961d, 0x2aa598220262258b07a042902a38ecb672ecac6ee3485b17a20ef55e5915c23b6598723923, 0x2aa598220262258b07a042902a38ecb672ecac6ee3485b17a20ef55e5915c23b6598723923,
  0x23836be6f56fc46916b585e9bbe014278344571e899ed5333f7a1f5b7c0ed7da6dc601961d, 0x189c76826bb4db6c500759a1181776452106c419642d5fe1746f7b73ccedd5c7eacfc78a83, 0xe2d28ea50f6fbee0e8148b8c2dcf13da9cdc3e4025d2be120aae538a855d5c7ccb5518d3d,
  0x6c63a507ed9a847b34ff25f638a4cb96c41fcdb51996bb38e7ee49daf5fe26b5014564213, 0x2adb86a5bfbbf8c35869208fec001a2346e870ea23d7ec1afd5c9d68a5c1ccfe3c4d3c82d, 0xdf9b0f222940b22a42be05d3bf54d686644d145d15dbb4eeb79c5041a01d4d765fb1a4b3,
  0x3be29560e1d5ca6abe450aec4857af47b02608f67e07b91eef1ec40c509f9e2bd4d2560d, 0xd1b2a2899887b46e19514d335df2180a6f033d0d1e81f9b07aed99085b3247b8183b93b, 0x254735b115c9924e39a3ede4884c8c2b0f7151e3dcfc65200ea38297ed15a8487de9605,
  0x5583678fef1db8f41e5908235436d77cff7853523271b49eb32c76fa9ada83d3de7b1b, 0x9cde4336e2fc187c1a62d29b1a33cdeb712107f09a2640a2f2766ad552e4dabbef0a5, 0xe3d50f75b265fd92991eb23443b8615f4832d51761dae4e0cd9516fbbeec439f324b,
  0x102e794d9a07a9423681af3c1471463c3559f9acdf9318220ca9ef328ab07de7f7f5, 0xe2ff4f6360b0c4cc07c962836a43d5bf85d5fcaaa3323575255d7ea1aea09e7b6b, 0x9702842e1faa1c5e2f126d8bc0a60b143c446e592c365334d48c42b944616c355,
  0x4ab67a9f593a838d1a72de038e7b7f052806ed1cdec4f3addb227f110d3f23c7, 0x1ad53b8efb0488eadde41f18d986a5f5df4b56547e0a1ed83fb867ed8a37e79, 0x6ca9a9a4fd058cd35adb5acb845f4bbdd08d6481e21fc5d0aaa5706d150a7,
  0x12af0205f7591c68ee1d61cc75eb3fc10ecd2d3f2ccfc2373f6b1c976019, 0x215802943dcc916993c53a6f410751657e026fb9d3d26fba14aa7cf9b7, 0x24637ab353512eb2cbf3f71ab32176ee921f61eceaa8186747871789,
  0x167a32eb90b90b87da4e055a83e9c82e8c9552da61a81a1b07f6d7, 0x715b0424347ecd15d1f6ce28f34ca0e510d95d297bce8aa90e9, 0xfcc59b6fbcd4f313f918857b53308bebdc3d88f589177f8f,
  0xcb121b7c623823a0e0e4590561929fb0ef1c08313feb1, 0x2b50a8a7b13fd6cda173787e40f5efb8f14cd74cef, 0x184ec2e9415a165ab95b0625ba42bfe5341bd1,
  0xfffff4fef3ff74b23a43f55526d1581f, 0x2b56d4af4e7932278c797ec521, 0xffffffffffffffbf,
  0x1]

private theorem eulerianCoefficients_eq : descentCoeffs 64 = eulerianCoefficients := by
  decide +kernel

private theorem upper : upperOK (descentCoeffs 64) first gaps = true := by
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

private theorem lower (i : Fin (lastRepresentative 65 - 2)) :
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

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 65) :
    StrictNegativeInterlacing (originalQuotient 65 k) (eulerian 64) 62 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N065
