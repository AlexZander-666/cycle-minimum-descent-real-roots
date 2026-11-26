import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentPackedData.C127L072.N067

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N067

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L072.N067 LongCycleBounds.DescentNecklace.Packed.C127L072.N067.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L072.N067 LongCycleBounds.DescentNecklace.Packed.C127L072.N067.rows

private theorem actual : RepresentativeChecks 67 previousNodes rows :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L072.N067 LongCycleBounds.DescentNecklace.Packed.C127L072.N067.dataChecks

private def first : LongCycleFinite.Dyadic := ⟨-73786976294838206464, 0⟩

private def gaps : List Window := [
  ⟨⟨-73784583757536165888, 0⟩, ⟨-420758945792, 0⟩⟩,
  ⟨⟨-418610413568, 0⟩, ⟨-179614720, 0⟩⟩,
  ⟨⟨-162591744, 0⟩, ⟨-2348136, 0⟩⟩,
  ⟨⟨-2340392, 0⟩, ⟨-148839, 0⟩⟩,
  ⟨⟨-148732, 0⟩, ⟨-86943, 2⟩⟩,
  ⟨⟨-86917, 2⟩, ⟨-334669, 6⟩⟩,
  ⟨⟨-167307, 5⟩, ⟨-27809, 4⟩⟩,
  ⟨⟨-13903, 3⟩, ⟨-368883, 9⟩⟩,
  ⟨⟨-184427, 8⟩, ⟨-179009, 9⟩⟩,
  ⟨⟨-89499, 8⟩, ⟨-195175, 10⟩⟩,
  ⟨⟨-97583, 9⟩, ⟨-58107, 9⟩⟩,
  ⟨⟨-232419, 11⟩, ⟨-296399, 12⟩⟩,
  ⟨⟨-296389, 12⟩, ⟨-398985, 13⟩⟩,
  ⟨⟨-398973, 13⟩, ⟨-280465, 13⟩⟩,
  ⟨⟨-280457, 13⟩, ⟨-12765, 9⟩⟩,
  ⟨⟨-204235, 13⟩, ⟨-4785, 8⟩⟩,
  ⟨⟨-306233, 14⟩, ⟨-470397, 15⟩⟩,
  ⟨⟨-117597, 13⟩, ⟨-23041, 11⟩⟩,
  ⟨⟨-368649, 15⟩, ⟨-293869, 15⟩⟩,
  ⟨⟨-36733, 12⟩, ⟨-118825, 14⟩⟩,
  ⟨⟨-475293, 16⟩, ⟨-389095, 16⟩⟩,
  ⟨⟨-389089, 16⟩, ⟨-321841, 16⟩⟩,
  ⟨⟨-80459, 14⟩, ⟨-67143, 14⟩⟩,
  ⟨⟨-33571, 13⟩, ⟨-451597, 17⟩⟩,
  ⟨⟨-451591, 17⟩, ⟨-382071, 17⟩⟩,
  ⟨⟨-191033, 16⟩, ⟨-162477, 16⟩⟩,
  ⟨⟨-162475, 16⟩, ⟨-277575, 17⟩⟩,
  ⟨⟨-277571, 17⟩, ⟨-237933, 17⟩⟩,
  ⟨⟨-475861, 18⟩, ⟨-204509, 17⟩⟩,
  ⟨⟨-409013, 18⟩, ⟨-176133, 17⟩⟩,
  ⟨⟨-352261, 18⟩, ⟨-303783, 18⟩⟩,
  ⟨⟨-303779, 18⟩, ⟨-262145, 18⟩⟩,
  ⟨⟨-524285, 19⟩, ⟨-113107, 17⟩⟩,
  ⟨⟨-452423, 19⟩, ⟨-390165, 19⟩⟩,
  ⟨⟨-24385, 15⟩, ⟨-168013, 18⟩⟩,
  ⟨⟨-336021, 19⟩, ⟨-288821, 19⟩⟩,
  ⟨⟨-288817, 19⟩, ⟨-495147, 20⟩⟩,
  ⟨⟨-495141, 20⟩, ⟨-211477, 19⟩⟩,
  ⟨⟨-422949, 20⟩, ⟨-359727, 20⟩⟩,
  ⟨⟨-179861, 19⟩, ⟨-38043, 17⟩⟩,
  ⟨⟨-304339, 20⟩, ⟨-511745, 21⟩⟩,
  ⟨⟨-255869, 20⟩, ⟨-427045, 21⟩⟩,
  ⟨⟨-427039, 21⟩, ⟨-353235, 21⟩⟩,
  ⟨⟨-176615, 20⟩, ⟨-144583, 20⟩⟩,
  ⟨⟨-289161, 21⟩, ⟨-467695, 22⟩⟩,
  ⟨⟨-58461, 19⟩, ⟨-186411, 21⟩⟩,
  ⟨⟨-372815, 22⟩, ⟨-292179, 22⟩⟩,
  ⟨⟨-292173, 22⟩, ⟨-448803, 23⟩⟩,
  ⟨⟨-448795, 23⟩, ⟨-168237, 22⟩⟩,
  ⟨⟨-336467, 23⟩, ⟨-122513, 22⟩⟩,
  ⟨⟨-490041, 24⟩, ⟨-172241, 23⟩⟩,
  ⟨⟨-172237, 23⟩, ⟨-463715, 25⟩⟩,
  ⟨⟨-463703, 25⟩, ⟨-147835, 24⟩⟩,
  ⟨⟨-295661, 25⟩, ⟨-22007, 22⟩⟩,
  ⟨⟨-352101, 26⟩, ⟨-95977, 25⟩⟩,
  ⟨⟨-191947, 26⟩, ⟨-372599, 28⟩⟩,
  ⟨⟨-372583, 28⟩, ⟨-19307, 25⟩⟩,
  ⟨⟨-308897, 29⟩, ⟨-205345, 30⟩⟩,
  ⟨⟨-410667, 31⟩, ⟨-395285, 33⟩⟩,
  ⟨⟨-98815, 31⟩, ⟨-230883, 35⟩⟩,
  ⟨⟨-461733, 36⟩, ⟨-29323, 36⟩⟩,
  ⟨⟨-469131, 40⟩, ⟨-101267, 44⟩⟩,
  ⟨⟨-202517, 45⟩, ⟨-344269, 57⟩⟩,
  ⟨⟨-344237, 57⟩, ⟨-262165, 84⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private def eulerianCoefficients : List ℤ := [
  0x1, 0x3ffffffffffffffbd, 0x1860d7a2aff42c363f04574adac,
  0xfffff99ea79069b9986dcd81dd2781384, 0x25fb331c74c91afc0854eed611752fe8fd615e4, 0x61796dc3bc5e457fc8e748666ab7c56591a6b7cee1c,
  0x26e6a401002bb13074e7e2e19e011a2360060fd49b6389c, 0x3f5ce3f96d8c54a34c381a5b7f6483f1184a3e37012cf485f4, 0x241a219e51e447e9cc16dfaf8457916305016feda79904364785c,
  0x8e57a53d22dfe14356ecb4b1d57a09fe00bdab46ecadd2ea53fb274, 0x1199a5e22b8eb15d10a7799af16c7a616a15f9b9720ba051bffb87966c, 0x1374a5f4e62b673f857f7c8af7857151ab009da34bc5638b799a679e6b04,
  0xd054b788a23362d6d82c1c5138f0cb7bc8a0605ad870e22b1ac0f056ab1c4, 0x59bf6ef0c6e3a5505767629affd030d04f8556765af14714be93f452f74b33c, 0x1a1b785b5fc6e7887aeb9202ec142feee9b544ee4af73d8ff06d27e6529548e5c,
  0x553c13edb4581af39450f91014f48011b220a4d229e758e3e84c80f4b3e34c6174, 0xc94941d4d98d4661da1e210dbe25d5c28b671f320e98942a5bee0cf2ce43c14d100, 0x1609854d132e2013ecda082854859f9bfc6f756b5a43222b2c82def3341d522a79748,
  0x1d3c6cbca5353a950028cba277606d0326175539f8915b2fb694a3e1e974dcb8afb2dc, 0x1de3cc646831cf3391fd39531368e41e4b0477da310acf3c7acbfdaabfba8ed4c149594, 0x17e5396cdeae14ba34df4c597e5c8661922c1470f7d89dd66e653fa2258105d6300f75b4,
  0xf1fa2e67bc77379fcc104eaefb102ebed3b794e44c5283889b57af89dba55e87dcb9d34c, 0x7a85cf3a3208fd3af26333a153c8c93f283fe1531ced41dc2184aefc7a492a9023ab2f58c, 0x321388cfbe7879b11a38dc52fc151d929be510648d266c6c10a89dc83722a573e08da02fc4,
  0x10a56d35d7641dd6eb04a533fd722035a3e2cf4e37e90f07fbc1b9564b473e99b0a5657cdbc, 0x487938abd4ac58dbb104ca23dfd857e59eced9c504ea9ad91e12311f29f123dfb21d7b253f4, 0x103b210737bea298031510f58668314c501db6802da08380d2c175096582433ae25a010e64dc,
  0x301630e2f91a83c098dd36e922951f88cb9a0731aa9b416b95c871f6e529adc5081781f441d4, 0x763afc6ba5ba53d2736825dffb0858325b4742196310a830f8a493ed9268f6e3cfbba78babd4, 0xf1f9eb959beef5154f3daad452d538f6351c2f12b36e8c102e19c45bdb05c8500d6025a7222c,
  0x19d382d6d321b6f5ea87c14d925811c271fb37326aac8a856c45d672f94fda38227396b55ed8c, 0x24dcd9e859042ba556f3707d584e902ddfbf7299743a7c3e06034e7620fff1b204ec7c6318d04, 0x2c0721220ceb4d5e241d641e6af0a16f212f00944951254deec264bf6c8ba9eb01dd50066cb7a,
  0x2c0721220ceb4d5e241d641e6af0a16f212f00944951254deec264bf6c8ba9eb01dd50066cb7a, 0x24dcd9e859042ba556f3707d584e902ddfbf7299743a7c3e06034e7620fff1b204ec7c6318d04, 0x19d382d6d321b6f5ea87c14d925811c271fb37326aac8a856c45d672f94fda38227396b55ed8c,
  0xf1f9eb959beef5154f3daad452d538f6351c2f12b36e8c102e19c45bdb05c8500d6025a7222c, 0x763afc6ba5ba53d2736825dffb0858325b4742196310a830f8a493ed9268f6e3cfbba78babd4, 0x301630e2f91a83c098dd36e922951f88cb9a0731aa9b416b95c871f6e529adc5081781f441d4,
  0x103b210737bea298031510f58668314c501db6802da08380d2c175096582433ae25a010e64dc, 0x487938abd4ac58dbb104ca23dfd857e59eced9c504ea9ad91e12311f29f123dfb21d7b253f4, 0x10a56d35d7641dd6eb04a533fd722035a3e2cf4e37e90f07fbc1b9564b473e99b0a5657cdbc,
  0x321388cfbe7879b11a38dc52fc151d929be510648d266c6c10a89dc83722a573e08da02fc4, 0x7a85cf3a3208fd3af26333a153c8c93f283fe1531ced41dc2184aefc7a492a9023ab2f58c, 0xf1fa2e67bc77379fcc104eaefb102ebed3b794e44c5283889b57af89dba55e87dcb9d34c,
  0x17e5396cdeae14ba34df4c597e5c8661922c1470f7d89dd66e653fa2258105d6300f75b4, 0x1de3cc646831cf3391fd39531368e41e4b0477da310acf3c7acbfdaabfba8ed4c149594, 0x1d3c6cbca5353a950028cba277606d0326175539f8915b2fb694a3e1e974dcb8afb2dc,
  0x1609854d132e2013ecda082854859f9bfc6f756b5a43222b2c82def3341d522a79748, 0xc94941d4d98d4661da1e210dbe25d5c28b671f320e98942a5bee0cf2ce43c14d100, 0x553c13edb4581af39450f91014f48011b220a4d229e758e3e84c80f4b3e34c6174,
  0x1a1b785b5fc6e7887aeb9202ec142feee9b544ee4af73d8ff06d27e6529548e5c, 0x59bf6ef0c6e3a5505767629affd030d04f8556765af14714be93f452f74b33c, 0xd054b788a23362d6d82c1c5138f0cb7bc8a0605ad870e22b1ac0f056ab1c4,
  0x1374a5f4e62b673f857f7c8af7857151ab009da34bc5638b799a679e6b04, 0x1199a5e22b8eb15d10a7799af16c7a616a15f9b9720ba051bffb87966c, 0x8e57a53d22dfe14356ecb4b1d57a09fe00bdab46ecadd2ea53fb274,
  0x241a219e51e447e9cc16dfaf8457916305016feda79904364785c, 0x3f5ce3f96d8c54a34c381a5b7f6483f1184a3e37012cf485f4, 0x26e6a401002bb13074e7e2e19e011a2360060fd49b6389c,
  0x61796dc3bc5e457fc8e748666ab7c56591a6b7cee1c, 0x25fb331c74c91afc0854eed611752fe8fd615e4, 0xfffff99ea79069b9986dcd81dd2781384,
  0x1860d7a2aff42c363f04574adac, 0x3ffffffffffffffbd, 0x1]

private theorem eulerianCoefficients_eq : descentCoeffs 66 = eulerianCoefficients := by
  decide +kernel

private theorem upper : upperOK (descentCoeffs 66) first gaps = true := by
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

private theorem lower (i : Fin (lastRepresentative 67 - 2)) :
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

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 67) :
    StrictNegativeInterlacing (originalQuotient 67 k) (eulerian 66) 64 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N067
