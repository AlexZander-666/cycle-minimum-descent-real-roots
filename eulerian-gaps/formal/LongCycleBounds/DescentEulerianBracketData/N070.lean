import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentPackedData.C127L072.N070

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N070

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L072.N070 LongCycleBounds.DescentNecklace.Packed.C127L072.N070.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L072.N070 LongCycleBounds.DescentNecklace.Packed.C127L072.N070.rows

private theorem actual : RepresentativeChecks 70 previousNodes rows :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L072.N070 LongCycleBounds.DescentNecklace.Packed.C127L072.N070.dataChecks

private def first : LongCycleFinite.Dyadic := ⟨-590295810358705651712, 0⟩

private def gaps : List Window := [
  ⟨⟨-590276670060289327104, 0⟩, ⟨-1422544338944, 0⟩⟩,
  ⟨⟨-1405364469760, 0⟩, ⟨-464931840, 0⟩⟩,
  ⟨⟨-407483392, 0⟩, ⟨-4615104, 0⟩⟩,
  ⟨⟨-4597456, 0⟩, ⟨-519717, 1⟩⟩,
  ⟨⟨-519293, 1⟩, ⟨-69933, 1⟩⟩,
  ⟨⟨-34955, 0⟩, ⟨-63425, 3⟩⟩,
  ⟨⟨-253655, 5⟩, ⟨-322521, 7⟩⟩,
  ⟨⟨-322483, 7⟩, ⟨-64559, 6⟩⟩,
  ⟨⟨-258215, 8⟩, ⟨-243787, 9⟩⟩,
  ⟨⟨-487543, 10⟩, ⟨-519843, 11⟩⟩,
  ⟨⟨-519817, 11⟩, ⟨-303903, 11⟩⟩,
  ⟨⟨-151945, 10⟩, ⟨-95427, 10⟩⟩,
  ⟨⟨-190847, 11⟩, ⟨-507369, 13⟩⟩,
  ⟨⟨-507353, 13⟩, ⟨-352899, 13⟩⟩,
  ⟨⟨-176445, 12⟩, ⟨-509461, 14⟩⟩,
  ⟨⟨-509449, 14⟩, ⟨-47393, 11⟩⟩,
  ⟨⟨-1481, 6⟩, ⟨-144707, 13⟩⟩,
  ⟨⟨-2261, 7⟩, ⟨-112839, 13⟩⟩,
  ⟨⟨-112837, 13⟩, ⟨-5599, 9⟩⟩,
  ⟨⟨-179165, 14⟩, ⟨-144433, 14⟩⟩,
  ⟨⟨-288861, 15⟩, ⟨-471823, 16⟩⟩,
  ⟨⟨-58977, 13⟩, ⟨-389635, 16⟩⟩,
  ⟨⟨-389629, 16⟩, ⟨-324837, 16⟩⟩,
  ⟨⟨-324833, 16⟩, ⟨-136515, 15⟩⟩,
  ⟨⟨-136513, 15⟩, ⟨-231087, 16⟩⟩,
  ⟨⟨-57771, 14⟩, ⟨-196743, 16⟩⟩,
  ⟨⟨-393481, 17⟩, ⟨-42085, 14⟩⟩,
  ⟨⟨-84169, 15⟩, ⟨-144635, 16⟩⟩,
  ⟨⟨-289267, 17⟩, ⟨-498771, 18⟩⟩,
  ⟨⟨-249383, 17⟩, ⟨-215581, 17⟩⟩,
  ⟨⟨-431157, 18⟩, ⟨-373483, 18⟩⟩,
  ⟨⟨-373479, 18⟩, ⟨-161995, 17⟩⟩,
  ⟨⟨-323987, 18⟩, ⟨-281297, 18⟩⟩,
  ⟨⟨-140647, 17⟩, ⟨-244299, 18⟩⟩,
  ⟨⟨-488593, 19⟩, ⟨-424213, 19⟩⟩,
  ⟨⟨-26513, 15⟩, ⟨-367997, 19⟩⟩,
  ⟨⟨-367993, 19⟩, ⟨-318769, 19⟩⟩,
  ⟨⟨-318765, 19⟩, ⟨-34445, 16⟩⟩,
  ⟨⟨-275557, 19⟩, ⟨-237563, 19⟩⟩,
  ⟨⟨-29695, 16⟩, ⟨-204113, 19⟩⟩,
  ⟨⟨-408221, 20⟩, ⟨-174645, 19⟩⟩,
  ⟨⟨-349285, 20⟩, ⟨-297381, 20⟩⟩,
  ⟨⟨-297377, 20⟩, ⟨-251693, 20⟩⟩,
  ⟨⟨-125845, 19⟩, ⟨-423105, 21⟩⟩,
  ⟨⟨-105775, 19⟩, ⟨-352745, 21⟩⟩,
  ⟨⟨-88185, 19⟩, ⟨-72825, 19⟩⟩,
  ⟨⟨-9103, 16⟩, ⟨-237897, 21⟩⟩,
  ⟨⟨-475787, 22⟩, ⟨-383551, 22⟩⟩,
  ⟨⟨-383545, 22⟩, ⟨-2379, 15⟩⟩,
  ⟨⟨-152253, 21⟩, ⟨-474893, 23⟩⟩,
  ⟨⟨-474885, 23⟩, ⟨-181253, 22⟩⟩,
  ⟨⟨-362499, 23⟩, ⟨-67445, 21⟩⟩,
  ⟨⟨-134887, 22⟩, ⟨-194731, 23⟩⟩,
  ⟨⟨-389453, 24⟩, ⟨-135447, 23⟩⟩,
  ⟨⟨-270887, 24⟩, ⟨-360075, 25⟩⟩,
  ⟨⟨-360065, 25⟩, ⟨-452263, 26⟩⟩,
  ⟨⟨-452249, 26⟩, ⟨-264397, 26⟩⟩,
  ⟨⟨-264387, 26⟩, ⟨-70473, 25⟩⟩,
  ⟨⟨-140941, 26⟩, ⟨-266123, 28⟩⟩,
  ⟨⟨-266111, 28⟩, ⟨-426159, 30⟩⟩,
  ⟨⟨-213069, 29⟩, ⟨-135443, 30⟩⟩,
  ⟨⟨-135435, 30⟩, ⟨-15357, 29⟩⟩,
  ⟨⟨-3839, 27⟩, ⟨-264503, 36⟩⟩,
  ⟨⟨-66121, 34⟩, ⟨-477185, 41⟩⟩,
  ⟨⟨-119287, 39⟩, ⟨-340945, 47⟩⟩,
  ⟨⟨-85229, 45⟩, ⟨-407967, 59⟩⟩,
  ⟨⟨-50991, 56⟩, ⟨-262149, 87⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private def eulerianCoefficients : List ℤ := [
  0x1, 0x1fffffffffffffffba, 0x29236be29c700a9b8a57534d7162,
  0x3fffff4c050800802bd19782c1f38d4bdba, 0x128bb72be4b7a4f17decb2b068e37ec9f71b21231, 0x5241c58ec71f8f7c0e8e2ccfc1915a523d93d620775e0,
  0x342ab70bbc53aed2a02decd71d156ab8200a50900a46f2b60, 0x7f1b933697734ab27c999fafa74275c0124d0f726b059d3b63e0, 0x6797c402d7728d465ffeb2edbc7eca5f2fb6d202a15902ecbf61928,
  0x234d848fa777c8645b9bb356043bfffc84cf525d4a6ef31fdf157cb230, 0x5e1fd05c8d7177c28b7ee1824aa435f1a61d013b6017f239f90ba5432cf0, 0x897460790e2527085be4c54c0c506ef1aed51b551767f773502e043bd3c630,
  0x77a7802a3ecd763c700c541591951401638d758df1773ff238652a0bd0625988, 0x423c5f2e453c5c0fec20668b2bf0508c307ce5acf6112c4c3f0948a9cc3b7387a0, 0x1885ee096137c154953eb2930a955fd5670156d693de98ead742faea244077abb220,
  0x6524243670427c9c9b097db62a8b527ba8fa92ab9a53fa1bfcd7434a4bd0644d055a0, 0x12bfcc3ebad805977711c3117f787d7b8b477c5c2d43feaa5093209c582c9baac47b2ac, 0x29115f82b869fc4caa9aa5d4dc20746097f192dc3db0a8c27065381192d618477f075258,
  0x43e7beb9e05338ffda0079373aafa3ee5d69662b9ed02c7bfa3b25b8e2e5cef60f2dfaab8, 0x56545c5d8952f7b474b2970b9bded8c225b562f898a43ed9d5e8fe5cfefb6e8763fe2d9658, 0x55b3892da4f2e778140f6ebb385c12194ccf6118be379da6094085ab5c8d3c452839915234c,
  0x434f8358baabb67d7756fdc482d4681b8826b998bb1b9e71c55bafc8a662de7af24673573be0, 0x2a4bcf4c65e381368d38801c093fd8fcf7e9c526345394576678ae876c6279e3417c53ff03560, 0x1577c47f3e3bbf9d625fcc0122d1b52758bce30dfcf8c3bb821957ef004c20248b04749cce31e0,
  0x8dfa4f74c017a4137f35857e4e6d12d60a3c512804b1018b9d2f190ea7f3550857d4afb700c3f8, 0x3020d6bb5c76f6f77d8d2e67523677598f80ce599673c8f3369acb3b0cc2016440aa99b6e800350, 0xd75cc772efa8dcf45b9757cb6ed6cb713e06166efdaa8a41c6f86962694b23974c7db1c760d2a90,
  0x31f240df44b31bf4740084a938531ad6b6cc99e4ae8095dbad260e70fe30d84862cea8e4ced34750, 0x9a59f5504c6b1801362b4e4532ac91dcf3d043fb8a27c3bdda2e9e74fdefe3520b1c19ceb94498d8, 0x18eaff29ed86ab97b35debe743648ad2fd24e1d89748032dee2317e24c1ee491bbd10f1a7c95ba2a0,
  0x35f45d6e3ae39bf4251d5f52844718bc2e116927a68a87f60526a52cf455f24df746bc03f60846d20, 0x622a441d5c90b32fef25322b9fe20201689acc8e6cbd913411e3a0e1def046d27e3171e2595cb38a0, 0x96572f5e312d2007cad0dc49f86ad471f866a9ee492de6e438c4e02f1b2704e59e2924e693c534856,
  0xc20ed6f071cb53d42f1c8b4e2b7b87710efa06266b4b9ff616a2d2c03ead95c663974e233cc7f96dc, 0xd3464f46e3846f4ae0cc49ad0de9474b2fc119ff75c30f133235d2252c05ad9a1a3ad59b3c3e618cc, 0xc20ed6f071cb53d42f1c8b4e2b7b87710efa06266b4b9ff616a2d2c03ead95c663974e233cc7f96dc,
  0x96572f5e312d2007cad0dc49f86ad471f866a9ee492de6e438c4e02f1b2704e59e2924e693c534856, 0x622a441d5c90b32fef25322b9fe20201689acc8e6cbd913411e3a0e1def046d27e3171e2595cb38a0, 0x35f45d6e3ae39bf4251d5f52844718bc2e116927a68a87f60526a52cf455f24df746bc03f60846d20,
  0x18eaff29ed86ab97b35debe743648ad2fd24e1d89748032dee2317e24c1ee491bbd10f1a7c95ba2a0, 0x9a59f5504c6b1801362b4e4532ac91dcf3d043fb8a27c3bdda2e9e74fdefe3520b1c19ceb94498d8, 0x31f240df44b31bf4740084a938531ad6b6cc99e4ae8095dbad260e70fe30d84862cea8e4ced34750,
  0xd75cc772efa8dcf45b9757cb6ed6cb713e06166efdaa8a41c6f86962694b23974c7db1c760d2a90, 0x3020d6bb5c76f6f77d8d2e67523677598f80ce599673c8f3369acb3b0cc2016440aa99b6e800350, 0x8dfa4f74c017a4137f35857e4e6d12d60a3c512804b1018b9d2f190ea7f3550857d4afb700c3f8,
  0x1577c47f3e3bbf9d625fcc0122d1b52758bce30dfcf8c3bb821957ef004c20248b04749cce31e0, 0x2a4bcf4c65e381368d38801c093fd8fcf7e9c526345394576678ae876c6279e3417c53ff03560, 0x434f8358baabb67d7756fdc482d4681b8826b998bb1b9e71c55bafc8a662de7af24673573be0,
  0x55b3892da4f2e778140f6ebb385c12194ccf6118be379da6094085ab5c8d3c452839915234c, 0x56545c5d8952f7b474b2970b9bded8c225b562f898a43ed9d5e8fe5cfefb6e8763fe2d9658, 0x43e7beb9e05338ffda0079373aafa3ee5d69662b9ed02c7bfa3b25b8e2e5cef60f2dfaab8,
  0x29115f82b869fc4caa9aa5d4dc20746097f192dc3db0a8c27065381192d618477f075258, 0x12bfcc3ebad805977711c3117f787d7b8b477c5c2d43feaa5093209c582c9baac47b2ac, 0x6524243670427c9c9b097db62a8b527ba8fa92ab9a53fa1bfcd7434a4bd0644d055a0,
  0x1885ee096137c154953eb2930a955fd5670156d693de98ead742faea244077abb220, 0x423c5f2e453c5c0fec20668b2bf0508c307ce5acf6112c4c3f0948a9cc3b7387a0, 0x77a7802a3ecd763c700c541591951401638d758df1773ff238652a0bd0625988,
  0x897460790e2527085be4c54c0c506ef1aed51b551767f773502e043bd3c630, 0x5e1fd05c8d7177c28b7ee1824aa435f1a61d013b6017f239f90ba5432cf0, 0x234d848fa777c8645b9bb356043bfffc84cf525d4a6ef31fdf157cb230,
  0x6797c402d7728d465ffeb2edbc7eca5f2fb6d202a15902ecbf61928, 0x7f1b933697734ab27c999fafa74275c0124d0f726b059d3b63e0, 0x342ab70bbc53aed2a02decd71d156ab8200a50900a46f2b60,
  0x5241c58ec71f8f7c0e8e2ccfc1915a523d93d620775e0, 0x128bb72be4b7a4f17decb2b068e37ec9f71b21231, 0x3fffff4c050800802bd19782c1f38d4bdba,
  0x29236be29c700a9b8a57534d7162, 0x1fffffffffffffffba, 0x1]

private theorem eulerianCoefficients_eq : descentCoeffs 69 = eulerianCoefficients := by
  decide +kernel

private theorem upper : upperOK (descentCoeffs 69) first gaps = true := by
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

private theorem lower (i : Fin (lastRepresentative 70 - 2)) :
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

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 70) :
    StrictNegativeInterlacing (originalQuotient 70 k) (eulerian 69) 67 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N070
