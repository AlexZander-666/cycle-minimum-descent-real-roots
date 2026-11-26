import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentPackedData.C127L096.N089

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N089

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L096.N089 LongCycleBounds.DescentNecklace.Packed.C127L096.N089.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L096.N089 LongCycleBounds.DescentNecklace.Packed.C127L096.N089.rows

private theorem actual : RepresentativeChecks 89 previousNodes rows :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L096.N089 LongCycleBounds.DescentNecklace.Packed.C127L096.N089.dataChecks

private def first : LongCycleFinite.Dyadic := ⟨-309485009821345068724781056, 0⟩

private def gaps : List Window := [
  ⟨⟨-309474974792568970728701952, 0⟩, ⟨-3137370530512896, 0⟩⟩,
  ⟨⟨-3128565847556096, 0⟩, ⟨-98467053568, 0⟩⟩,
  ⟨⟨-98342273024, 0⟩, ⟨-329750528, 0⟩⟩,
  ⟨⟨-325261312, 0⟩, ⟨-8696352, 0⟩⟩,
  ⟨⟨-8680736, 0⟩, ⟨-694758, 0⟩⟩,
  ⟨⟨-694350, 0⟩, ⟨-431351, 2⟩⟩,
  ⟨⟨-107807, 0⟩, ⟨-411349, 4⟩⟩,
  ⟨⟨-411279, 4⟩, ⟨-263141, 5⟩⟩,
  ⟨⟨-131555, 4⟩, ⟨-415199, 7⟩⟩,
  ⟨⟨-415163, 7⟩, ⟨-191255, 7⟩⟩,
  ⟨⟨-382485, 8⟩, ⟨-49551, 6⟩⟩,
  ⟨⟨-396387, 9⟩, ⟨-225071, 9⟩⟩,
  ⟨⟨-225061, 9⟩, ⟨-274807, 10⟩⟩,
  ⟨⟨-68699, 8⟩, ⟨-177853, 10⟩⟩,
  ⟨⟨-177847, 10⟩, ⟨-30181, 8⟩⟩,
  ⟨⟨-241441, 11⟩, ⟨-340965, 12⟩⟩,
  ⟨⟨-85239, 10⟩, ⟨-248815, 12⟩⟩,
  ⟨⟨-248809, 12⟩, ⟨-186691, 12⟩⟩,
  ⟨⟨-186687, 12⟩, ⟨-286865, 13⟩⟩,
  ⟨⟨-286859, 13⟩, ⟨-224901, 13⟩⟩,
  ⟨⟨-224897, 13⟩, ⟨-22429, 10⟩⟩,
  ⟨⟨-358857, 14⟩, ⟨-145339, 13⟩⟩,
  ⟨⟨-290673, 14⟩, ⟨-477153, 15⟩⟩,
  ⟨⟨-238573, 14⟩, ⟨-396179, 15⟩⟩,
  ⟨⟨-396173, 15⟩, ⟨-332293, 15⟩⟩,
  ⟨⟨-332289, 15⟩, ⟨-140605, 14⟩⟩,
  ⟨⟨-140603, 14⟩, ⟨-239861, 15⟩⟩,
  ⟨⟨-119929, 14⟩, ⟨-206023, 15⟩⟩,
  ⟨⟨-412041, 16⟩, ⟨-89025, 14⟩⟩,
  ⟨⟨-1391, 8⟩, ⟨-38679, 13⟩⟩,
  ⟨⟨-77357, 14⟩, ⟨-270179, 16⟩⟩,
  ⟨⟨-8443, 11⟩, ⟨-473823, 17⟩⟩,
  ⟨⟨-236909, 16⟩, ⟨-417035, 17⟩⟩,
  ⟨⟨-208515, 16⟩, ⟨-368261, 17⟩⟩,
  ⟨⟨-184129, 16⟩, ⟨-40765, 14⟩⟩,
  ⟨⟨-81529, 15⟩, ⟨-289515, 17⟩⟩,
  ⟨⟨-36189, 14⟩, ⟨-515117, 18⟩⟩,
  ⟨⟨-64389, 15⟩, ⟨-229535, 17⟩⟩,
  ⟨⟨-229533, 17⟩, ⟨-204855, 17⟩⟩,
  ⟨⟨-204853, 17⟩, ⟨-45759, 15⟩⟩,
  ⟨⟨-366069, 18⟩, ⟨-327359, 18⟩⟩,
  ⟨⟨-327355, 18⟩, ⟨-292903, 18⟩⟩,
  ⟨⟨-73225, 16⟩, ⟨-262145, 18⟩⟩,
  ⟨⟨-262143, 18⟩, ⟨-469237, 19⟩⟩,
  ⟨⟨-469233, 19⟩, ⟨-419845, 19⟩⟩,
  ⟨⟨-209921, 18⟩, ⟨-187723, 18⟩⟩,
  ⟨⟨-375443, 19⟩, ⟨-335459, 19⟩⟩,
  ⟨⟨-335455, 19⟩, ⟨-74847, 17⟩⟩,
  ⟨⟨-299385, 19⟩, ⟨-266813, 19⟩⟩,
  ⟨⟨-266811, 19⟩, ⟨-474727, 20⟩⟩,
  ⟨⟨-474723, 20⟩, ⟨-421441, 20⟩⟩,
  ⟨⟨-421437, 20⟩, ⟨-11663, 15⟩⟩,
  ⟨⟨-93303, 18⟩, ⟨-329565, 20⟩⟩,
  ⟨⟨-329561, 20⟩, ⟨-72517, 18⟩⟩,
  ⟨⟨-290065, 20⟩, ⟨-508699, 21⟩⟩,
  ⟨⟨-508693, 21⟩, ⟨-444169, 21⟩⟩,
  ⟨⟨-444165, 21⟩, ⟨-385959, 21⟩⟩,
  ⟨⟨-385955, 21⟩, ⟨-166779, 20⟩⟩,
  ⟨⟨-166777, 20⟩, ⟨-286499, 21⟩⟩,
  ⟨⟨-286495, 21⟩, ⟨-488747, 22⟩⟩,
  ⟨⟨-488741, 22⟩, ⟨-413611, 22⟩⟩,
  ⟨⟨-206803, 21⟩, ⟨-346915, 22⟩⟩,
  ⟨⟨-346911, 22⟩, ⟨-144021, 21⟩⟩,
  ⟨⟨-144019, 21⟩, ⟨-472829, 23⟩⟩,
  ⟨⟨-236411, 22⟩, ⟨-95747, 21⟩⟩,
  ⟨⟨-191491, 22⟩, ⟨-305557, 23⟩⟩,
  ⟨⟨-19097, 19⟩, ⟨-479115, 24⟩⟩,
  ⟨⟨-479107, 24⟩, ⟨-11503, 19⟩⟩,
  ⟨⟨-368089, 24⟩, ⟨-276189, 24⟩⟩,
  ⟨⟨-276183, 24⟩, ⟨-50387, 22⟩⟩,
  ⟨⟨-403087, 25⟩, ⟨-284623, 25⟩⟩,
  ⟨⟨-35577, 22⟩, ⟨-96599, 24⟩⟩,
  ⟨⟨-193193, 25⟩, ⟨-500143, 27⟩⟩,
  ⟨⟨-250065, 26⟩, ⟨-305325, 27⟩⟩,
  ⟨⟨-305315, 27⟩, ⟨-173365, 27⟩⟩,
  ⟨⟨-173359, 27⟩, ⟨-359327, 29⟩⟩,
  ⟨⟨-359313, 29⟩, ⟨-10345, 25⟩⟩,
  ⟨⟨-331025, 30⟩, ⟨-522375, 32⟩⟩,
  ⟨⟨-261175, 31⟩, ⟨-334165, 33⟩⟩,
  ⟨⟨-334147, 33⟩, ⟨-318715, 35⟩⟩,
  ⟨⟨-318695, 35⟩, ⟨-395715, 38⟩⟩,
  ⟨⟨-49461, 35⟩, ⟨-252975, 41⟩⟩,
  ⟨⟨-505913, 42⟩, ⟨-427853, 47⟩⟩,
  ⟨⟨-106955, 45⟩, ⟨-91509, 53⟩⟩,
  ⟨⟨-366005, 55⟩, ⟨-188393, 69⟩⟩,
  ⟨⟨-188375, 69⟩, ⟨-262165, 106⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private def eulerianCoefficients : List ℤ := [
  0x1, 0xffffffffffffffffffffa7, 0xb21e8aa8c3b8962ba55321f0c224e58e52d,
  0xfffffffc21361cb53f3d97ad38619334c812c31be92b, 0x141b8e652ef1c7e517df7d0eea059b1e7622205422f69a4a5c07, 0xb21e1acf7ab1010abfe7654519b02fa7ee7137fe4b27096c844ed30b1,
  0x843eb171e384e3c6fb723f1a111d5e5d814816e1b20659b8bdc409a9e60093, 0xffd20586263309b52936eeee853de725efd75f0ddd37f3fb20a38e50a122188ab5, 0x7b95845e91c87c987b7695af3870dabe688b60cfb970a9d8c69301a3091e76400a3992,
  0x13f088200439e71d1f98b040dabbc59362114a0e1da5b4aff9b54b7ab2e336ff714630b1be, 0x151ed0b04b6ce7ef2cabda30f2856b65e0142489f91c589bd4a071768acb67a2318ee417aca0a, 0xaab346a7476651d1efe7d3d8883e0e2cf50de8f25e04a8b2ba319b38f4cb68a494ab9d594c714a6,
  0x2e07f9cb9305a9d01ee839ff6babc7e2910619d14da77722ed482fbd60737baaaf95135e9697665ec6, 0x73986c3920d54ac6e9859d7b50df77ea73e8e166a692dc68bfaebe13beab767048f339fcbf01958b74ea, 0xb4c4d62598b50edb4aa8eb7c8ad47f4e584c60b765bd3a5e560b72f3e909d4b32afd5055524943da5f5f5e,
  0xb9c002e04514947fb5730752d075a62df48c7c32c6006428b3557fff128b3fa58ee447e1ce658f31bfa886f2, 0x82f96167a05611c72caaedcfd04ae9630daf52fcf1e91af587a398ba10e52f2ed22f7277679ab8fec64a417601, 0x41a8e7925e405f5acab3d398035ae430d059693fb3e03e004ac5bba471270d39bd3d924002cb5dc400b4a7de6727,
  0x1819c33ba64644d5d7253f9028cd054ae720581ea5884864a5ca18dddcfbeb2a30ecfe920b5e46d5f4fc5519346e0d, 0x6a362ab05b49c71732cb57f7f049724bdfb3b59f511c5b552df3e84d24c8652dfaa3c5cb809c7f485d28a6fac9444cb, 0x1669ebd790887044b789c8d8fafe7c03c535f56a10593d0d75076c3a59766cbcf0f2b93b7bf0c7e6511bab66ff9c157ff,
  0x3b04bbd60f47e2980545de2727ca232f3641e0571ff235a90873d77ea03d2d4c82e39ec48834cfc48f13ffd8c40d975ef9, 0x7b0c6dd7af45e1139cf7ab0b20d41dae48631351332858fa934a8888414cfe46e05b372b2c6f1e29d4fbe4eb47145ea8e0b, 0xcdd1e879d0f96fe5e3ded217442d0ccd9dba5639c79235621d9c042c7be044d0538601041cf8694d499f8e5544c8624298fd,
  0x1175f1713e3b25a14ee881e48a3ef30cea35f9af99ee0daaee24486cbc0db7882bcc834cdef451868bc032778dcddddb7f15f8, 0x136cf0cc5f3ceb65f6de6a53d38e5a54c098efd3f323a80ed95a995a020f9bc179cfd8cd01488e282d0d61751da34f89d230ac8, 0x11de7af61791f27628225a10891d54c1758b54199fff035cf1f5a08018edfff08f08645e1db49ee7dbb1819a3790a2b3c78c0c18,
  0xdb229bc72955fc5f4c52b33a2a002902787692f349b294334435950a143a4118c728c1b789ded80ce36ec2073ed5f72a69dd1b28, 0x8ce6ca1a234200314535dd64e7dc4f3bf2995f5261c021ce23e9d99071fcb257b6b9b0ef11c3e50434a296f8992fa7d6de58defe8, 0x4c7619abd4794bf70ea9f2532144ca075a7e006becbac0bb68417e82bfd5e0e96c0ec51658cc1c27d911a6d3dde196d5181dbcb558,
  0x233465a2c3d8f1f9603d173b2f5899d750d1c29c2f641611c238b4ee82ca32f11519cfa35cdb8b62f6f47ec0d59b3f119f0d0d69488, 0xdd15629d6f18de526009d2a5a915f694fc0f434659175ea52ac5385cfac483565c17447d350019afd449af2c7f03009ee93de59ae38, 0x4a4808fc0d45e48c8374e8bad2691b1c05c8f7a206979784a7b42e09545ec0f82988614dec43973e06cb1ec7e0e04ae1914b9672ac62,
  0x15717801123656e3dd2213ec9f5bd52228b445018caf3550633caaf5d0b0f0cf1d46588b814a8053cbefa5b2da0f489e3ff6b5fea07ee, 0x555f47e31956e4ce6ec849e65740f98bb73ede9620432664f1b0fad93445e68928f0639aad2e18fb09cc1d0e416d816adc92f20a97eba, 0x125d0b19843231385d35c20d7419eefce54cd67fdefc4ac728d1a1f145e77457654c52541a595049aaeb155fd62159a0da9eb5eb28d0f6,
  0x36c46ef90c4b4edda344753791307a6b472660536f0c89ac901adb246abaca25f4da088da1937419890cc7dd2767ee44b615994806870e, 0x8dd99720bdc25df78743c0a54a561cd5f8e95c8455f297ee03b2cdbbbf819bae5a8f5d6723c2a860bfff0fab9196d6ce03abdd92ab3462, 0x13fa5feb3e0af6ecae90e0dd541236a39164bb5ac3938639a41023477f3bb46f453ef64a1ed0be53aa164ebaa62005206fc33278821c4a6,
  0x273a6d2a5ece94f7e43d813466e8538a3012bacc802b5d7f75736f21748238928dc5d1e07e5b390cf8d2b113a2dc15f825fd702c6ea27ea, 0x43342c0650ac429941c249a60cb4b61aab5f4ae40a49cee0ae8d7f59e2c1d328890f9528d665f686fabdce49aa4aca44712fb1d746b0d4c, 0x648c00ec0798dd5cfd68d84eebccb982980a59a923fbbce1d9258d2453da4519de44b8ee7dfc51fbfc6e841df3654ba539f63bad04b8d94,
  0x83798e998bfaa2adc4030dadb42526ee6c355f79a703559c6ea66396b5bebaf03c1567cca32b0d9d84d453bd77795d988be3817f7ba699c, 0x9652d4c3ef55f263b94593e97ff04c3469a0efffeb1eefb0cee6b4596771a154da028d63e79d6612157e67dbd1a9d5a2453150df38c4784, 0x9652d4c3ef55f263b94593e97ff04c3469a0efffeb1eefb0cee6b4596771a154da028d63e79d6612157e67dbd1a9d5a2453150df38c4784,
  0x83798e998bfaa2adc4030dadb42526ee6c355f79a703559c6ea66396b5bebaf03c1567cca32b0d9d84d453bd77795d988be3817f7ba699c, 0x648c00ec0798dd5cfd68d84eebccb982980a59a923fbbce1d9258d2453da4519de44b8ee7dfc51fbfc6e841df3654ba539f63bad04b8d94, 0x43342c0650ac429941c249a60cb4b61aab5f4ae40a49cee0ae8d7f59e2c1d328890f9528d665f686fabdce49aa4aca44712fb1d746b0d4c,
  0x273a6d2a5ece94f7e43d813466e8538a3012bacc802b5d7f75736f21748238928dc5d1e07e5b390cf8d2b113a2dc15f825fd702c6ea27ea, 0x13fa5feb3e0af6ecae90e0dd541236a39164bb5ac3938639a41023477f3bb46f453ef64a1ed0be53aa164ebaa62005206fc33278821c4a6, 0x8dd99720bdc25df78743c0a54a561cd5f8e95c8455f297ee03b2cdbbbf819bae5a8f5d6723c2a860bfff0fab9196d6ce03abdd92ab3462,
  0x36c46ef90c4b4edda344753791307a6b472660536f0c89ac901adb246abaca25f4da088da1937419890cc7dd2767ee44b615994806870e, 0x125d0b19843231385d35c20d7419eefce54cd67fdefc4ac728d1a1f145e77457654c52541a595049aaeb155fd62159a0da9eb5eb28d0f6, 0x555f47e31956e4ce6ec849e65740f98bb73ede9620432664f1b0fad93445e68928f0639aad2e18fb09cc1d0e416d816adc92f20a97eba,
  0x15717801123656e3dd2213ec9f5bd52228b445018caf3550633caaf5d0b0f0cf1d46588b814a8053cbefa5b2da0f489e3ff6b5fea07ee, 0x4a4808fc0d45e48c8374e8bad2691b1c05c8f7a206979784a7b42e09545ec0f82988614dec43973e06cb1ec7e0e04ae1914b9672ac62, 0xdd15629d6f18de526009d2a5a915f694fc0f434659175ea52ac5385cfac483565c17447d350019afd449af2c7f03009ee93de59ae38,
  0x233465a2c3d8f1f9603d173b2f5899d750d1c29c2f641611c238b4ee82ca32f11519cfa35cdb8b62f6f47ec0d59b3f119f0d0d69488, 0x4c7619abd4794bf70ea9f2532144ca075a7e006becbac0bb68417e82bfd5e0e96c0ec51658cc1c27d911a6d3dde196d5181dbcb558, 0x8ce6ca1a234200314535dd64e7dc4f3bf2995f5261c021ce23e9d99071fcb257b6b9b0ef11c3e50434a296f8992fa7d6de58defe8,
  0xdb229bc72955fc5f4c52b33a2a002902787692f349b294334435950a143a4118c728c1b789ded80ce36ec2073ed5f72a69dd1b28, 0x11de7af61791f27628225a10891d54c1758b54199fff035cf1f5a08018edfff08f08645e1db49ee7dbb1819a3790a2b3c78c0c18, 0x136cf0cc5f3ceb65f6de6a53d38e5a54c098efd3f323a80ed95a995a020f9bc179cfd8cd01488e282d0d61751da34f89d230ac8,
  0x1175f1713e3b25a14ee881e48a3ef30cea35f9af99ee0daaee24486cbc0db7882bcc834cdef451868bc032778dcddddb7f15f8, 0xcdd1e879d0f96fe5e3ded217442d0ccd9dba5639c79235621d9c042c7be044d0538601041cf8694d499f8e5544c8624298fd, 0x7b0c6dd7af45e1139cf7ab0b20d41dae48631351332858fa934a8888414cfe46e05b372b2c6f1e29d4fbe4eb47145ea8e0b,
  0x3b04bbd60f47e2980545de2727ca232f3641e0571ff235a90873d77ea03d2d4c82e39ec48834cfc48f13ffd8c40d975ef9, 0x1669ebd790887044b789c8d8fafe7c03c535f56a10593d0d75076c3a59766cbcf0f2b93b7bf0c7e6511bab66ff9c157ff, 0x6a362ab05b49c71732cb57f7f049724bdfb3b59f511c5b552df3e84d24c8652dfaa3c5cb809c7f485d28a6fac9444cb,
  0x1819c33ba64644d5d7253f9028cd054ae720581ea5884864a5ca18dddcfbeb2a30ecfe920b5e46d5f4fc5519346e0d, 0x41a8e7925e405f5acab3d398035ae430d059693fb3e03e004ac5bba471270d39bd3d924002cb5dc400b4a7de6727, 0x82f96167a05611c72caaedcfd04ae9630daf52fcf1e91af587a398ba10e52f2ed22f7277679ab8fec64a417601,
  0xb9c002e04514947fb5730752d075a62df48c7c32c6006428b3557fff128b3fa58ee447e1ce658f31bfa886f2, 0xb4c4d62598b50edb4aa8eb7c8ad47f4e584c60b765bd3a5e560b72f3e909d4b32afd5055524943da5f5f5e, 0x73986c3920d54ac6e9859d7b50df77ea73e8e166a692dc68bfaebe13beab767048f339fcbf01958b74ea,
  0x2e07f9cb9305a9d01ee839ff6babc7e2910619d14da77722ed482fbd60737baaaf95135e9697665ec6, 0xaab346a7476651d1efe7d3d8883e0e2cf50de8f25e04a8b2ba319b38f4cb68a494ab9d594c714a6, 0x151ed0b04b6ce7ef2cabda30f2856b65e0142489f91c589bd4a071768acb67a2318ee417aca0a,
  0x13f088200439e71d1f98b040dabbc59362114a0e1da5b4aff9b54b7ab2e336ff714630b1be, 0x7b95845e91c87c987b7695af3870dabe688b60cfb970a9d8c69301a3091e76400a3992, 0xffd20586263309b52936eeee853de725efd75f0ddd37f3fb20a38e50a122188ab5,
  0x843eb171e384e3c6fb723f1a111d5e5d814816e1b20659b8bdc409a9e60093, 0xb21e1acf7ab1010abfe7654519b02fa7ee7137fe4b27096c844ed30b1, 0x141b8e652ef1c7e517df7d0eea059b1e7622205422f69a4a5c07,
  0xfffffffc21361cb53f3d97ad38619334c812c31be92b, 0xb21e8aa8c3b8962ba55321f0c224e58e52d, 0xffffffffffffffffffffa7,
  0x1]

private theorem eulerianCoefficients_eq : descentCoeffs 88 = eulerianCoefficients := by
  decide +kernel

private theorem upper : upperOK (descentCoeffs 88) first gaps = true := by
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

private theorem lower_041 : lowerOK (rows.getD 41 []) gaps = true := by
  decide +kernel

private theorem lower_042 : lowerOK (rows.getD 42 []) gaps = true := by
  decide +kernel

private theorem lower (i : Fin (lastRepresentative 89 - 2)) :
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
  · exact lower_041
  · exact lower_042

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 89) :
    StrictNegativeInterlacing (originalQuotient 89 k) (eulerian 88) 86 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N089
