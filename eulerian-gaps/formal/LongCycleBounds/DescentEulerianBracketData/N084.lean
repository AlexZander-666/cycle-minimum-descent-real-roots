import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentPackedData.C127L088.N084

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N084

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L088.N084 LongCycleBounds.DescentNecklace.Packed.C127L088.N084.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L088.N084 LongCycleBounds.DescentNecklace.Packed.C127L088.N084.rows

private theorem actual : RepresentativeChecks 84 previousNodes rows :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L088.N084 LongCycleBounds.DescentNecklace.Packed.C127L088.N084.dataChecks

private def first : LongCycleFinite.Dyadic := ⟨-9671406556917033397649408, 0⟩

private def gaps : List Window := [
  ⟨⟨-9671092962267780335271936, 0⟩, ⟨-522489214009344, 0⟩⟩,
  ⟨⟨-241017458524160, 0⟩, ⟨-23336255488, 0⟩⟩,
  ⟨⟨-23321837568, 0⟩, ⟨-107987968, 0⟩⟩,
  ⟨⟨-106925312, 0⟩, ⟨-3461840, 0⟩⟩,
  ⟨⟨-3456784, 0⟩, ⟨-317282, 0⟩⟩,
  ⟨⟨-317122, 0⟩, ⟨-435465, 3⟩⟩,
  ⟨⟨-435355, 3⟩, ⟨-112055, 3⟩⟩,
  ⟨⟨-224075, 4⟩, ⟨-304309, 6⟩⟩,
  ⟨⟨-76069, 4⟩, ⟨-503669, 8⟩⟩,
  ⟨⟨-503629, 8⟩, ⟨-482455, 9⟩⟩,
  ⟨⟨-241213, 8⟩, ⟨-129099, 8⟩⟩,
  ⟨⟨-258185, 9⟩, ⟨-150635, 9⟩⟩,
  ⟨⟨-301257, 10⟩, ⟨-376395, 11⟩⟩,
  ⟨⟨-376381, 11⟩, ⟨-496835, 12⟩⟩,
  ⟨⟨-124205, 10⟩, ⟨-342987, 12⟩⟩,
  ⟨⟨-342977, 12⟩, ⟨-491457, 13⟩⟩,
  ⟨⟨-491445, 13⟩, ⟨-363189, 13⟩⟩,
  ⟨⟨-363181, 13⟩, ⟨-275509, 13⟩⟩,
  ⟨⟨-275503, 13⟩, ⟨-26711, 10⟩⟩,
  ⟨⟨-53421, 11⟩, ⟨-168917, 13⟩⟩,
  ⟨⟨-84457, 12⟩, ⟨-271461, 14⟩⟩,
  ⟨⟨-271457, 14⟩, ⟨-442469, 15⟩⟩,
  ⟨⟨-442463, 15⟩, ⟨-365071, 15⟩⟩,
  ⟨⟨-365065, 15⟩, ⟨-152229, 14⟩⟩,
  ⟨⟨-304453, 15⟩, ⟨-512617, 16⟩⟩,
  ⟨⟨-512611, 16⟩, ⟨-435111, 16⟩⟩,
  ⟨⟨-217553, 15⟩, ⟨-186001, 15⟩⟩,
  ⟨⟨-371997, 16⟩, ⟨-320075, 16⟩⟩,
  ⟨⟨-320071, 16⟩, ⟨-138467, 15⟩⟩,
  ⟨⟨-276931, 16⟩, ⟨-481565, 17⟩⟩,
  ⟨⟨-60195, 14⟩, ⟨-420491, 17⟩⟩,
  ⟨⟨-210243, 16⟩, ⟨-184265, 16⟩⟩,
  ⟨⟨-184263, 16⟩, ⟨-81007, 15⟩⟩,
  ⟨⟨-40503, 14⟩, ⟨-285683, 17⟩⟩,
  ⟨⟨-17855, 13⟩, ⟨-252459, 17⟩⟩,
  ⟨⟨-252457, 17⟩, ⟨-111763, 16⟩⟩,
  ⟨⟨-55881, 15⟩, ⟨-99107, 16⟩⟩,
  ⟨⟨-49553, 15⟩, ⟨-175977, 17⟩⟩,
  ⟨⟨-175975, 17⟩, ⟨-156363, 17⟩⟩,
  ⟨⟨-156361, 17⟩, ⟨-34751, 15⟩⟩,
  ⟨⟨-278005, 18⟩, ⟨-123593, 17⟩⟩,
  ⟨⟨-15449, 14⟩, ⟨-109873, 17⟩⟩,
  ⟨⟨-6867, 13⟩, ⟨-390509, 19⟩⟩,
  ⟨⟨-195253, 18⟩, ⟨-346695, 19⟩⟩,
  ⟨⟨-86673, 17⟩, ⟨-307435, 19⟩⟩,
  ⟨⟨-38429, 16⟩, ⟨-68051, 17⟩⟩,
  ⟨⟨-272201, 19⟩, ⟨-481095, 20⟩⟩,
  ⟨⟨-481091, 20⟩, ⟨-424163, 20⟩⟩,
  ⟨⟨-424159, 20⟩, ⟨-186471, 19⟩⟩,
  ⟨⟨-186469, 19⟩, ⟨-40857, 17⟩⟩,
  ⟨⟨-81713, 18⟩, ⟨-285403, 20⟩⟩,
  ⟨⟨-35675, 17⟩, ⟨-248145, 20⟩⟩,
  ⟨⟨-496285, 21⟩, ⟨-214701, 20⟩⟩,
  ⟨⟨-429397, 21⟩, ⟨-184731, 20⟩⟩,
  ⟨⟨-184729, 20⟩, ⟨-315877, 21⟩⟩,
  ⟨⟨-315873, 21⟩, ⟨-67029, 19⟩⟩,
  ⟨⟨-16757, 17⟩, ⟨-451423, 22⟩⟩,
  ⟨⟨-451417, 22⟩, ⟨-188239, 21⟩⟩,
  ⟨⟨-47059, 19⟩, ⟨-155311, 21⟩⟩,
  ⟨⟨-310617, 22⟩, ⟨-253153, 22⟩⟩,
  ⟨⟨-506299, 23⟩, ⟨-101707, 21⟩⟩,
  ⟨⟨-406821, 23⟩, ⟨-160797, 22⟩⟩,
  ⟨⟨-321589, 23⟩, ⟨-249435, 23⟩⟩,
  ⟨⟨-498861, 24⟩, ⟨-378429, 24⟩⟩,
  ⟨⟨-189211, 23⟩, ⟨-17479, 20⟩⟩,
  ⟨⟨-139829, 23⟩, ⟨-200361, 24⟩⟩,
  ⟨⟨-400713, 25⟩, ⟨-34579, 22⟩⟩,
  ⟨⟨-17289, 21⟩, ⟨-365157, 26⟩⟩,
  ⟨⟨-365147, 26⟩, ⟨-456213, 27⟩⟩,
  ⟨⟨-456199, 27⟩, ⟨-266157, 27⟩⟩,
  ⟨⟨-266147, 27⟩, ⟨-142441, 27⟩⟩,
  ⟨⟨-284871, 28⟩, ⟨-272883, 29⟩⟩,
  ⟨⟨-272871, 29⟩, ⟨-451669, 31⟩⟩,
  ⟨⟨-7057, 25⟩, ⟨-76669, 30⟩⟩,
  ⟨⟨-76665, 30⟩, ⟨-157815, 33⟩⟩,
  ⟨⟨-315611, 34⟩, ⟨-433203, 37⟩⟩,
  ⟨⟨-216587, 36⟩, ⟨-79451, 38⟩⟩,
  ⟨⟨-79445, 38⟩, ⟨-328235, 45⟩⟩,
  ⟨⟨-328209, 45⟩, ⟨-193069, 52⟩⟩,
  ⟨⟨-193053, 52⟩, ⟨-22355, 63⟩⟩,
  ⟨⟨-178823, 66⟩, ⟨-262149, 101⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private def eulerianCoefficients : List ℤ := [
  0x1, 0x7ffffffffffffffffffac, 0xbba5f8443a8f929da6cb76fb880d97079,
  0x3ffffffc26d8a899cc1eae445453cf5775b8aa1bf0, 0x1a5b0066055584c0bcabf90b82f8def7484b5f897cc868784, 0x5dd271c457c8ad4dfdcbae0771109e33d9131e8f46ac722baa79b0,
  0x2039ad8db4a9c7fee422540fb270bbfea878a4fcce0b002d032609f60d4, 0x1ff56cc1474c28058a690fc9a9c1d177ce2e3343fc87a67dc27802451b5a510, 0x88e3ffbbd7e59515014ab72a803df9cedacc93524fc97fe5aec225efc47736e0c6,
  0xd007a2d2b68639c5daa8e52d76b259e17b8ded7e170afe07df25467c6ebd086a5a168, 0x880c751a336bae503d991ff18b8c5e75f391b44d79a41ef1e333340bf09f89b91762ec06, 0x2c13da3f481eaebfe00ee672bab7fee6247ab016f6336a103075ddf3109dfd6faa1bd82db90,
  0x7dc54957c0967e0a6c86090b131497670ba94a18301d9567b6efe0777d0690e5612d0b6ad3ab4, 0xd624052e9b8ee3e8eeaea761f5daf634c11d73db03f8b0c024d92391cfe25731fc22ddeac680430, 0xe7b555238835bc894a8727c3b47edba13e8c9036da9a4ee120813106b221dc5fdbd636d8998e674e4,
  0xa783e9eea0772a5e285da228b8a9af5f9b415d93e0a622e16f2943ebaaad399c63a1c6de440ba058570, 0x5441135de9d63fec7368981a552d284c74ba2665221c6cdeebbe074172527b40216d5d3ccd294cd9b7825, 0x1e792050aadacd3e326b16c0236e9f1637b682875b98b7823e9a69d2f34a8fd896c6ec9cfb0de7d420d943c,
  0x8254da75a2ad10b7b3f924cd4dcc98ee37afb850d8aa9e9b268bff295f3ef9b324e215d61484b83b6b5fa2cd, 0x1a587692f99a0eb713095fac16462727d15fed0b51e5618f94ec0fa04b231f256b40d81b7ea8e47228124103c0, 0x41b28c3272a31f3a2acd12704653e141b5edaec369d462b46e9849fa35c6ac2bd902f1bb2ebc4254551ea932fd0,
  0x806ad717942a4a958bca3aa4b6bed43af6a1cd4f316a553dba363f2303d7d152aaa78085b5d7d5be8102e63139c0, 0xc790e2ee1895226ee11e3f9fd65f00874d45c468fa8924dbbce3ab428c0c7d314e248b0947ca68551439a0aabdd10, 0xf99a5e7b635b45b0146ddfaffe66a644e32e9fbba99f7f9ca6e42d946129dfa232ec8a21c5393ebf9f6cd55dfa4840,
  0xfdefb0bc14fdc1363d3e68bbb1b025fcc495b03b15c3f06b82b15313750bf6df03082444a4e9961bb8720d574ca7d88, 0xd41858231f6731cd9bfe6d29a4c26bd7da0e4b754f4be0e5cba8d403fd6de74d0479ad2418d8b18f85e68f1cd2395ae0, 0x929dd3e33e91753e36d5b9b23b9f954c0dfba0204d78002fb93a82bc320b9e0d4d95e1f1864b5eee9c57956f4426f1908,
  0x547b67872c79a81676323eac73deea7d4f6bb6b9e6c03a59a3b42252708f1f774b4e7a037dba830d3615fbce332416ff40, 0x28d492f54d1c5a013301756fadd1f5c43d5b99fda1f00f84ed56665e082e7027fbe5815770252e3cd4426d49962a3d65850, 0x10a47e6543e969a9173ad6ec1e0d4ae76321e94f5bed6d010260cb94730758c932d27fb70c01725e53a1675506a3145978c0,
  0x5bfa80650e60620869f7d5239377933de28d09c8ec23f08a155958594bf494b5feee1d25b4934febf46ae6aecd50c3f95010, 0x1b09c9cfd8aff7cca2f88b60134201ce7d7e9664275f18caaab8b904637c861363de9d307fb4d134db60c263b3c5a14cb4cc0, 0x6ca0c41a283d7f7a12c19ca43d72a86d8f56866f64632fbc021b09a1f935fd1cf0f4b2cb7be1cd1c39d9b32924ed245980072,
  0x175fc6910a447b244e2786cf2d3869a707a6fbfe924124fb23ee4105a05124d7a5b504b564d32021f440877fe5ab83379e5018, 0x452713df588d730a2f0ef9fec864b091ed53116d0698b582d7a79499d18a3b1f789c89ebde5cb950b2cd1bcb49e3bd261aea22, 0xb03ab89e413d5a675484e08286b8a6c29f1d5f6950468572d1b37f358e8cf25b34c62421d1896f9a96b3091e3ca1b33b47fe20,
  0x183a1a5e71669417078da26c1172447d18c1fe4d5ee9568956036c58e6d1c2fc9430ee59d7a69cccf2386929229e9186d4a1bb8, 0x2e1262a8f7f3dd1503f326176986d3d544c4ff16836321e390afac8ae5e6ca464677bf2535bafc394f8d1c9a053acc407d2cfa0, 0x4bd953c439c60e3a72b030d1e97051061d23bbae225c54b9b68b3e40b1a8433a62e1128e44b3bbafd99752ed03ab01553e59718,
  0x6c370e702526eae05f3b31ad70a6db7449e12e7f66d249874a574b00ad33ea6737d0ab5f680b0c9efbd2ef710ccbe4599b247e0, 0x85e534b836d1b86a917519dd2b3d1720ca3adcc33e5e388f4f9e2cc317362033451a4e1f5d4abe6bfe2bcfdbf840faef9ad26a4, 0x8fbcd6f4afc33637e2fdfe7c8524b10e2278d01f4c24539978ed348bb6ffdec03c8d3de74f1c4ed9a7c91ec6c97d8aea60a3f70,
  0x85e534b836d1b86a917519dd2b3d1720ca3adcc33e5e388f4f9e2cc317362033451a4e1f5d4abe6bfe2bcfdbf840faef9ad26a4, 0x6c370e702526eae05f3b31ad70a6db7449e12e7f66d249874a574b00ad33ea6737d0ab5f680b0c9efbd2ef710ccbe4599b247e0, 0x4bd953c439c60e3a72b030d1e97051061d23bbae225c54b9b68b3e40b1a8433a62e1128e44b3bbafd99752ed03ab01553e59718,
  0x2e1262a8f7f3dd1503f326176986d3d544c4ff16836321e390afac8ae5e6ca464677bf2535bafc394f8d1c9a053acc407d2cfa0, 0x183a1a5e71669417078da26c1172447d18c1fe4d5ee9568956036c58e6d1c2fc9430ee59d7a69cccf2386929229e9186d4a1bb8, 0xb03ab89e413d5a675484e08286b8a6c29f1d5f6950468572d1b37f358e8cf25b34c62421d1896f9a96b3091e3ca1b33b47fe20,
  0x452713df588d730a2f0ef9fec864b091ed53116d0698b582d7a79499d18a3b1f789c89ebde5cb950b2cd1bcb49e3bd261aea22, 0x175fc6910a447b244e2786cf2d3869a707a6fbfe924124fb23ee4105a05124d7a5b504b564d32021f440877fe5ab83379e5018, 0x6ca0c41a283d7f7a12c19ca43d72a86d8f56866f64632fbc021b09a1f935fd1cf0f4b2cb7be1cd1c39d9b32924ed245980072,
  0x1b09c9cfd8aff7cca2f88b60134201ce7d7e9664275f18caaab8b904637c861363de9d307fb4d134db60c263b3c5a14cb4cc0, 0x5bfa80650e60620869f7d5239377933de28d09c8ec23f08a155958594bf494b5feee1d25b4934febf46ae6aecd50c3f95010, 0x10a47e6543e969a9173ad6ec1e0d4ae76321e94f5bed6d010260cb94730758c932d27fb70c01725e53a1675506a3145978c0,
  0x28d492f54d1c5a013301756fadd1f5c43d5b99fda1f00f84ed56665e082e7027fbe5815770252e3cd4426d49962a3d65850, 0x547b67872c79a81676323eac73deea7d4f6bb6b9e6c03a59a3b42252708f1f774b4e7a037dba830d3615fbce332416ff40, 0x929dd3e33e91753e36d5b9b23b9f954c0dfba0204d78002fb93a82bc320b9e0d4d95e1f1864b5eee9c57956f4426f1908,
  0xd41858231f6731cd9bfe6d29a4c26bd7da0e4b754f4be0e5cba8d403fd6de74d0479ad2418d8b18f85e68f1cd2395ae0, 0xfdefb0bc14fdc1363d3e68bbb1b025fcc495b03b15c3f06b82b15313750bf6df03082444a4e9961bb8720d574ca7d88, 0xf99a5e7b635b45b0146ddfaffe66a644e32e9fbba99f7f9ca6e42d946129dfa232ec8a21c5393ebf9f6cd55dfa4840,
  0xc790e2ee1895226ee11e3f9fd65f00874d45c468fa8924dbbce3ab428c0c7d314e248b0947ca68551439a0aabdd10, 0x806ad717942a4a958bca3aa4b6bed43af6a1cd4f316a553dba363f2303d7d152aaa78085b5d7d5be8102e63139c0, 0x41b28c3272a31f3a2acd12704653e141b5edaec369d462b46e9849fa35c6ac2bd902f1bb2ebc4254551ea932fd0,
  0x1a587692f99a0eb713095fac16462727d15fed0b51e5618f94ec0fa04b231f256b40d81b7ea8e47228124103c0, 0x8254da75a2ad10b7b3f924cd4dcc98ee37afb850d8aa9e9b268bff295f3ef9b324e215d61484b83b6b5fa2cd, 0x1e792050aadacd3e326b16c0236e9f1637b682875b98b7823e9a69d2f34a8fd896c6ec9cfb0de7d420d943c,
  0x5441135de9d63fec7368981a552d284c74ba2665221c6cdeebbe074172527b40216d5d3ccd294cd9b7825, 0xa783e9eea0772a5e285da228b8a9af5f9b415d93e0a622e16f2943ebaaad399c63a1c6de440ba058570, 0xe7b555238835bc894a8727c3b47edba13e8c9036da9a4ee120813106b221dc5fdbd636d8998e674e4,
  0xd624052e9b8ee3e8eeaea761f5daf634c11d73db03f8b0c024d92391cfe25731fc22ddeac680430, 0x7dc54957c0967e0a6c86090b131497670ba94a18301d9567b6efe0777d0690e5612d0b6ad3ab4, 0x2c13da3f481eaebfe00ee672bab7fee6247ab016f6336a103075ddf3109dfd6faa1bd82db90,
  0x880c751a336bae503d991ff18b8c5e75f391b44d79a41ef1e333340bf09f89b91762ec06, 0xd007a2d2b68639c5daa8e52d76b259e17b8ded7e170afe07df25467c6ebd086a5a168, 0x88e3ffbbd7e59515014ab72a803df9cedacc93524fc97fe5aec225efc47736e0c6,
  0x1ff56cc1474c28058a690fc9a9c1d177ce2e3343fc87a67dc27802451b5a510, 0x2039ad8db4a9c7fee422540fb270bbfea878a4fcce0b002d032609f60d4, 0x5dd271c457c8ad4dfdcbae0771109e33d9131e8f46ac722baa79b0,
  0x1a5b0066055584c0bcabf90b82f8def7484b5f897cc868784, 0x3ffffffc26d8a899cc1eae445453cf5775b8aa1bf0, 0xbba5f8443a8f929da6cb76fb880d97079,
  0x7ffffffffffffffffffac, 0x1]

private theorem eulerianCoefficients_eq : descentCoeffs 83 = eulerianCoefficients := by
  decide +kernel

private theorem upper : upperOK (descentCoeffs 83) first gaps = true := by
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

private theorem lower_040 : lowerOK (rows.getD 40 []) gaps = true := by
  decide +kernel

private theorem lower (i : Fin (lastRepresentative 84 - 2)) :
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
  · exact lower_040

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 84) :
    StrictNegativeInterlacing (originalQuotient 84 k) (eulerian 83) 81 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N084
