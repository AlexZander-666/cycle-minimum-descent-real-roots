import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentPackedData.C127L112.N108

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N108

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L112.N108 LongCycleBounds.DescentNecklace.Packed.C127L112.N108.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L112.N108 LongCycleBounds.DescentNecklace.Packed.C127L112.N108.rows

private theorem actual : RepresentativeChecks 108 previousNodes rows :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L112.N108 LongCycleBounds.DescentNecklace.Packed.C127L112.N108.dataChecks

private def first : LongCycleFinite.Dyadic := ⟨-162259276829213363391578010288128, 0⟩

private def gaps : List Window := [
  ⟨⟨-162254015584046400525409689010176, 0⟩, ⟨-8602860450696134656, 0⟩⟩,
  ⟨⟨-3991227208826880000, 0⟩, ⟨-23375493726208, 0⟩⟩,
  ⟨⟨-23137525694464, 0⟩, ⟨-23588569088, 0⟩⟩,
  ⟨⟨-22525902848, 0⟩, ⟨-285660160, 0⟩⟩,
  ⟨⟨-284558336, 0⟩, ⟨-13493024, 0⟩⟩,
  ⟨⟨-13479232, 0⟩, ⟨-1427000, 0⟩⟩,
  ⟨⟨-1426364, 0⟩, ⟨-254224, 0⟩⟩,
  ⟨⟨-254161, 0⟩, ⟨-517661, 3⟩⟩,
  ⟨⟨-258789, 2⟩, ⟨-169965, 3⟩⟩,
  ⟨⟨-339891, 4⟩, ⟨-269449, 5⟩⟩,
  ⟨⟨-269425, 5⟩, ⟨-492825, 7⟩⟩,
  ⟨⟨-61599, 4⟩, ⟨-503685, 8⟩⟩,
  ⟨⟨-503657, 8⟩, ⟨-140549, 7⟩⟩,
  ⟨⟨-70271, 6⟩, ⟨-168425, 8⟩⟩,
  ⟨⟨-84209, 7⟩, ⟨-106953, 8⟩⟩,
  ⟨⟨-427797, 10⟩, ⟨-142523, 9⟩⟩,
  ⟨⟨-71259, 8⟩, ⟨-197717, 10⟩⟩,
  ⟨⟨-395423, 11⟩, ⟨-283779, 11⟩⟩,
  ⟨⟨-283771, 11⟩, ⟨-419275, 12⟩⟩,
  ⟨⟨-209633, 11⟩, ⟨-317541, 12⟩⟩,
  ⟨⟨-317535, 12⟩, ⟨-245727, 12⟩⟩,
  ⟨⟨-491445, 13⟩, ⟨-387503, 13⟩⟩,
  ⟨⟨-48437, 10⟩, ⟨-155293, 12⟩⟩,
  ⟨⟨-77645, 11⟩, ⟨-126275, 12⟩⟩,
  ⟨⟨-126273, 12⟩, ⟨-415985, 14⟩⟩,
  ⟨⟨-415979, 14⟩, ⟨-346479, 14⟩⟩,
  ⟨⟨-173237, 13⟩, ⟨-291503, 14⟩⟩,
  ⟨⟨-291499, 14⟩, ⟨-61865, 12⟩⟩,
  ⟨⟨-247457, 14⟩, ⟨-26471, 11⟩⟩,
  ⟨⟨-211765, 14⟩, ⟨-91267, 13⟩⟩,
  ⟨⟨-45633, 12⟩, ⟨-158361, 14⟩⟩,
  ⟨⟨-316719, 15⟩, ⟨-138195, 14⟩⟩,
  ⟨⟨-138193, 14⟩, ⟨-484937, 16⟩⟩,
  ⟨⟨-121233, 14⟩, ⟨-427455, 16⟩⟩,
  ⟨⟨-213725, 15⟩, ⟨-378411, 16⟩⟩,
  ⟨⟨-47301, 13⟩, ⟨-336303, 16⟩⟩,
  ⟨⟨-336299, 16⟩, ⟨-299935, 16⟩⟩,
  ⟨⟨-74983, 14⟩, ⟨-268351, 16⟩⟩,
  ⟨⟨-67087, 14⟩, ⟨-240783, 16⟩⟩,
  ⟨⟨-240781, 16⟩, ⟨-216605, 16⟩⟩,
  ⟨⟨-216603, 16⟩, ⟨-195307, 16⟩⟩,
  ⟨⟨-195305, 16⟩, ⟨-352937, 17⟩⟩,
  ⟨⟨-176467, 16⟩, ⟨-79871, 15⟩⟩,
  ⟨⟨-319481, 17⟩, ⟨-289673, 17⟩⟩,
  ⟨⟨-144835, 16⟩, ⟨-263019, 17⟩⟩,
  ⟨⟨-263017, 17⟩, ⟨-478225, 18⟩⟩,
  ⟨⟨-478221, 18⟩, ⟨-108805, 16⟩⟩,
  ⟨⟨-27201, 14⟩, ⟨-198215, 17⟩⟩,
  ⟨⟨-396427, 18⟩, ⟨-180677, 17⟩⟩,
  ⟨⟨-361351, 18⟩, ⟨-329561, 18⟩⟩,
  ⟨⟨-164779, 17⟩, ⟨-300685, 18⟩⟩,
  ⟨⟨-150341, 17⟩, ⟨-137201, 17⟩⟩,
  ⟨⟨-274399, 18⟩, ⟨-250435, 18⟩⟩,
  ⟨⟨-250433, 18⟩, ⟨-457089, 19⟩⟩,
  ⟨⟨-228543, 18⟩, ⟨-417039, 19⟩⟩,
  ⟨⟨-104259, 17⟩, ⟨-380347, 19⟩⟩,
  ⟨⟨-47543, 16⟩, ⟨-346695, 19⟩⟩,
  ⟨⟨-86673, 17⟩, ⟨-157897, 18⟩⟩,
  ⟨⟨-19737, 15⟩, ⟨-71849, 17⟩⟩,
  ⟨⟨-287393, 19⟩, ⟨-261275, 19⟩⟩,
  ⟨⟨-261273, 19⟩, ⟨-474467, 20⟩⟩,
  ⟨⟨-474463, 20⟩, ⟨-215097, 19⟩⟩,
  ⟨⟨-215095, 19⟩, ⟨-194709, 19⟩⟩,
  ⟨⟨-389415, 20⟩, ⟨-21991, 16⟩⟩,
  ⟨⟨-87963, 18⟩, ⟨-317261, 20⟩⟩,
  ⟨⟨-158629, 19⟩, ⟨-285403, 20⟩⟩,
  ⟨⟨-35675, 17⟩, ⟨-512165, 21⟩⟩,
  ⟨⟨-512161, 21⟩, ⟨-458235, 21⟩⟩,
  ⟨⟨-458231, 21⟩, ⟨-51085, 18⟩⟩,
  ⟨⟨-102169, 19⟩, ⟨-363203, 21⟩⟩,
  ⟨⟨-5675, 15⟩, ⟨-80383, 19⟩⟩,
  ⟨⟨-40191, 18⟩, ⟨-283419, 21⟩⟩,
  ⟨⟨-283415, 21⟩, ⟨-497271, 22⟩⟩,
  ⟨⟨-248633, 21⟩, ⟨-433947, 22⟩⟩,
  ⟨⟨-433943, 22⟩, ⟨-376479, 22⟩⟩,
  ⟨⟨-188237, 21⟩, ⟨-81127, 20⟩⟩,
  ⟨⟨-40563, 19⟩, ⟨-138851, 21⟩⟩,
  ⟨⟨-277699, 22⟩, ⟨-471489, 23⟩⟩,
  ⟨⟨-117871, 21⟩, ⟨-49585, 20⟩⟩,
  ⟨⟨-198337, 22⟩, ⟨-330399, 23⟩⟩,
  ⟨⟨-165197, 22⟩, ⟨-136053, 22⟩⟩,
  ⟨⟨-136051, 22⟩, ⟨-442525, 24⟩⟩,
  ⟨⟨-221259, 23⟩, ⟨-354685, 24⟩⟩,
  ⟨⟨-354679, 24⟩, ⟨-17479, 20⟩⟩,
  ⟨⟨-279659, 24⟩, ⟨-6763, 19⟩⟩,
  ⟨⟨-54103, 22⟩, ⟨-327807, 25⟩⟩,
  ⟨⟨-40975, 22⟩, ⟨-484327, 26⟩⟩,
  ⟨⟨-484317, 26⟩, ⟨-86893, 24⟩⟩,
  ⟨⟨-86891, 24⟩, ⟨-482187, 27⟩⟩,
  ⟨⟨-482175, 27⟩, ⟨-40159, 24⟩⟩,
  ⟨⟨-321263, 27⟩, ⟨-204013, 27⟩⟩,
  ⟨⟨-204007, 27⟩, ⟨-955, 20⟩⟩,
  ⟨⟨-488945, 29⟩, ⟨-136441, 28⟩⟩,
  ⟨⟨-34109, 26⟩, ⟨-278897, 30⟩⟩,
  ⟨⟨-139443, 29⟩, ⟨-63763, 29⟩⟩,
  ⟨⟨-255041, 31⟩, ⟨-202169, 32⟩⟩,
  ⟨⟨-404319, 33⟩, ⟨-265525, 34⟩⟩,
  ⟨⟨-132755, 33⟩, ⟨-135167, 35⟩⟩,
  ⟨⟨-135159, 35⟩, ⟨-48171, 36⟩⟩,
  ⟨⟨-385343, 39⟩, ⟨-326211, 42⟩⟩,
  ⟨⟨-81547, 40⟩, ⟨-123395, 45⟩⟩,
  ⟨⟨-493543, 47⟩, ⟨-389411, 53⟩⟩,
  ⟨⟨-97345, 51⟩, ⟨-395263, 63⟩⟩,
  ⟨⟨-395229, 63⟩, ⟨-87021, 79⟩⟩,
  ⟨⟨-348051, 81⟩, ⟨-262149, 125⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private def eulerianCoefficients : List ℤ := [
  0x1, 0x7ffffffffffffffffffffffff94, 0x30336cdd21fc654f9bd9c8d0bb0268abc114411610d,
  0x3ffffffffebaa4e12b5a98536eb401f47f11afbd78a8b748b176a0, 0x15ccfe3b85d80e3101daf3cfe71d87ec01fac424e37d0ba6d7bef409f1ee57a, 0x1819b5db694a1b3bdb8d19af247ee98677bebf3834e7abb2c1af86cbb23eaf31d9efb8,
  0x14ec187112e0d895d297f6054ab33cdf750438e09c8e658b7f128ccb31e5bf4081ecc8d4155a, 0x1fff72c63862ce15d31089418c4c0877ef50983f516f359bdeb96ac4d8edd931d7ae511db841ceda0, 0x9127b29535ede62aaf540a59c622ea6f99ccd964f51147b0dd4fba17b63bf7436abb8a086626c4d7ad471,
  0xae2ab24aa02e6023e483b85f5616226e3ae83d06c2d013306d3c80686922aee012300e0ad82630ed9b0e514e4, 0x472dbe6b1dd1f330ba6a23b1b5c647d1ab00b5b7c0b3d4ec3b1d458bf599b9517cc5dab8b775c5352f277fbe30255, 0xbeec4449b8f41e881ae26bfbf7a16a7b5997681bbb3faca2b6a585fcc6a7aa75743aeac39873ab424aa1e8a107f6f780,
  0xf1b727b4ffaee7a0c1e07c7c8f8f6f6047d395a6b04d51d4a6ddd2fb40d1ac8373b7670a9440c693c7184740c2dcf523548, 0xa0f04c2cbb61df7d01b5fa4e5f98caef323ee24aa00c800b62aea61919a51d92d5d95339fb58ab94d2f7e337de5793ca01c7e0, 0x3d58d97e78096cabd2f972fb6d69e4e09f4962319c6e3ebfffef3c2e54c246a42f912f19b757b5413157d69a9238db762651b8d88,
  0xe5341ea908f070829a944d8ac69daebd2d6fdeb7bebeb58fd8de08dca71a43dc7591b54a77128111f713b2bd75c3edf682a60cbf980, 0x22a1b3acbe2f375d325dc8de5f6f7949d68794b16f737821fadc781ad64ff6fce3dc7359248d1efbb0b73240cf5018c1414792609b4736, 0x38a828d586ebe27b53f19280ef5e2d7a744dab2b8f4ed7d6c6752218eb57b209df02175f05e41bd5df4529df10f66da2f92e24c6693b3ef8,
  0x4118cb565157379ee3ba20a238304b737251bdbcbbf48cdfc304cc3a3862d291f459641037f4109bcea0bc5a95cc6649210e077f5f770d605e, 0x362f909334421887b56f668894eaee3bad70a1e93e03e255b2653a7d334107c808e9110124e2b226b019c9a69d7d474712dc1380c266f3d8fe40, 0x218b77c229f211565a1394a1d957b662a93f15afed37bad75ac1ba09298991f1faa6de348e217abba48e8ca90e7e9f789ef810a4bea7f0ec663854,
  0xfcb3bd113c781d98c707ee7ca19bbfe7fe2e70b92f7656e09ea6ea70dc728d36241f415ac325fb73e818497162c504fc2216d0f04f1b4f80b809070, 0x5c3e43fdc497e2e1e670f178ad3e19771de4929714162dd8c988cc51be539afffceedd82f2c3a7e8a2c2f45d618940dd1702e34b87e68db260a6d3ad4, 0x1a8abbe73951cdb2fefed002d32448c81e77195ba534f2d47849842d086424c24e8900edf53508cc9b960d7d630ee6ac47f91b29ca1e03f3bc3802a3240,
  0x61b9305648e2f8ff6a2e496288015a2e972837c05d339ac1c4a19a97c792562a6e622439b1d3bf4c224f252f12a1a8d9e7b5b60355fc565f146296b6bece, 0x123694c5bfc2e29a343a9053a3dfb0b97fdf3328bf698b97c24a655a088aa0d8f013a4fc4d3aa2c7d89848c0b41df39bea29bef6ee07affbd046ddb9a421b8, 0x2c7b09255f30b9a57d691b0266dfc98f26e898b0ac6daa52a6c9649f90420de255340e1058722f6766bb863eb0564e3701f4ad1e1019bb693c061de2a88d5e6,
  0x59d8f4ffafa211b2ef745634f3ce688e1b577c90bf1bf57682363d34516ab4ed404df8ec9862489aabc5e4f9baa039de19f8a8b7306adc01b1e22581554b0b80, 0x976be5d159660e1bc9378112fb9f41ea66da6dc7f2086b663c517949e3ec57e20b24b64bc343eec5763288f44f77fb0671360c70bef665acc064352e0020a6668, 0xd6959366571f87009af211b0864cd01c8d0126cb4e633f0b678cc7c2ba87438066cced641735ac98021c57722c4a29c1b9b4c10c624e76a52a81aebafa115e4860,
  0x1017dae2e838b231c1b251302e0b6af68fb3a486833b54111c361b23b74d773a69673bfc5040cc92423106efc0e0466fea6cfcec0c756a53bfecf47ed33d87fda128, 0x10743b0d95a8c835261cd72c82b9c73366b0366a92ec5daf43e09266acfbd1ea97451759dfa30b543e4a2895075163b7060f8519942257d073e6158db5fc5e048a180, 0xe6a2d406d0432eb6e00d81c0f75d4743b3b700037740bd3359d3acd7970f0bfbc9d3448403908df509b922e74bd92fda860afc55af0f45e7c4fcdc1eef956062aba73,
  0xae0182cab5dcf72a5f6d8bdae08481587df2e27f9548df4ac18dee6d326495ed262994fe380d076ac67b2310994a676710216b8a8a84bb08e5ce63081ec54de144e93c, 0x71935b215842af6efd778d528f47a35e3303a41289d12e69f30fdaddb56b3f78169b511043eac4adf85e787cf6e18b67fdd7c8fb90670c82ad15a9de20d68f0c356a577, 0x40663e9771c33be1f9d70c7d6d87c698a318639b611ecdc20a3586c110f4c40b82ae7fd49afc0f7630002a1c85d0b0503adb5a5d2f3b93778fc1cab6190d1c1c8723e260,
  0x1fd70e55f9ca6528aa85e2c9ba084660b808d111b4c7bec134704e7c5ac6ea8661db70b845738877516087434f83f7b3b0307209d501519e154a1ceec22163e4d3ca4ad46, 0xdc5dfceccfe68160325ad4fef7841b6f5f66576e13d41dc9cbff34a1a246855046137dc4a2dc07c58541800f700703af56640bc1c1f8c8d156caf2b15a0c984b7fc1aa8c8, 0x53a763f6416d8215a10d13664528b0a16c489a40a50f4360239a1d19a0f8ac58d23e83dda56da5d4a689601b64825cc75cbc0cc982506674cdbeb66b465bc97e28b03138a6,
  0x1bf202a8eb8bd6924cd9ca80861b0cf44f7382af2b3e2c79df5e515c807735c377d85a0923df87e6713f21f10dc511206c5b00c74c9ddcdde3e1228c65862c03f3adcac1560, 0x83c5530eeaa25f67ebb3553920781f56a8c4874e76a4a2091bf4fa407bd05a2af7d9223470505a8a03ae3d737d45d016dae57393f7a9dd79d06324978b07bf322a451f13a6b, 0x22560273b450d2e8369e99ad6cff41e20d18c92808283bbcb5c20fa6061884cafc9ca871189f898a36081d1023887ec72cfbca21943103ad9b9f502ff23dd836a005305bd3cc,
  0x7ed40536ec17b51629e1a52df46827ef4e86cd0ccc4aabf063290351937cdb5e555b4f70c2c9ab6e3f4cdd249e53254f85e92a39a86f53c3b8f8503afe1674b119cd212a1217, 0x19fcc485805d88e835e0b69ad7c2cb7c763ebb2475661bb515d1661f71e0c235c70249b82533b81ca144d957c79c98931a95b438489055265de792c8e8d98c660375144241700, 0x4bbd8443e21fecd0aaeb0ea3cfd0d59ee0ae95fb5d207d6c4ccb23c222d546a7f3130981e3b10f083a45d33f0f6021a70d50b405e2f2d76d42c57c5ef60e34e0bea14e0612790,
  0xc4852e1f6bb40c1e9b6dd6cea1534637973ad5e8340d37b7c984bd7f2214c821bec50d44514b8d954a5164566480be668cdfed5dab1c1f6b4c044acba74059dbc735495e98fc0, 0x1c682e7ce322823eabd00641254197e822e095cc876ef750f74a012fe3b4ee9d1cdb61ea5a6f13c665b91df04f10fc10afe0258451a604fbf78ff015e6bf8352f9f99485247e10, 0x3aa03561edd92e69d9ba9bc62aa7e92dad2050f0566d88d7fc90089e71532a6c82ec99e372a7bcdfa2baa6dfa0aba4028445603db44510c1db3aaebd3f8d1fe7ade9015e284b00,
  0x6c1057babeca82941d9a86df09714d7f4885126892f812d97c1b73592c07b0fd3992c6b2797a499c9ae70fe2448e18119314845ddf45fcff6d7cb3582b08323fa08a7c6e57b404, 0xb20bf30bfee2f19204b1f0fc3c53baf46cb8753e56b8a6867a0364599f7aa41b7c69595c549cf76835d00637dd24681721e51a579521cbc777f33c4f89f2be5de0c8d37e9acdd0, 0x1065fa54cccbfe7a2bffc3e9048a0d8215086fd4b649e031f33b39ef993925280f4a7451fd1f19a42a4b989cb19ff96c3c80e9ff64aad462612246d39c6d050968c5a9d8cb42b74,
  0x159fa48e18c3ac08c02296a3fd9d81d759f19c1b545a1c5d270bf66cfec60c3ca5b8ff81df1a4243e46c87b09a320c0126fe3b37a78e4446464bd7c96df62ec15c7f5861abb7380, 0x198619ac64e1024f07f5324ddd8dacb5a379c296e6745964633c70e69381998e9a81f671e3bd246cccfe17ad4421832c88c35e712cbb976058b49d4d31301c2afd8aff432683c18, 0x1af94a1e40866dcfde4c59e0a2d466eea9ea5071b40e8f9e30a21108a6aa873b24cb3e01707666a9d362fbfb3d2403564a38932511089cb9c75703d75c93bc30362b233e2826e20,
  0x198619ac64e1024f07f5324ddd8dacb5a379c296e6745964633c70e69381998e9a81f671e3bd246cccfe17ad4421832c88c35e712cbb976058b49d4d31301c2afd8aff432683c18, 0x159fa48e18c3ac08c02296a3fd9d81d759f19c1b545a1c5d270bf66cfec60c3ca5b8ff81df1a4243e46c87b09a320c0126fe3b37a78e4446464bd7c96df62ec15c7f5861abb7380, 0x1065fa54cccbfe7a2bffc3e9048a0d8215086fd4b649e031f33b39ef993925280f4a7451fd1f19a42a4b989cb19ff96c3c80e9ff64aad462612246d39c6d050968c5a9d8cb42b74,
  0xb20bf30bfee2f19204b1f0fc3c53baf46cb8753e56b8a6867a0364599f7aa41b7c69595c549cf76835d00637dd24681721e51a579521cbc777f33c4f89f2be5de0c8d37e9acdd0, 0x6c1057babeca82941d9a86df09714d7f4885126892f812d97c1b73592c07b0fd3992c6b2797a499c9ae70fe2448e18119314845ddf45fcff6d7cb3582b08323fa08a7c6e57b404, 0x3aa03561edd92e69d9ba9bc62aa7e92dad2050f0566d88d7fc90089e71532a6c82ec99e372a7bcdfa2baa6dfa0aba4028445603db44510c1db3aaebd3f8d1fe7ade9015e284b00,
  0x1c682e7ce322823eabd00641254197e822e095cc876ef750f74a012fe3b4ee9d1cdb61ea5a6f13c665b91df04f10fc10afe0258451a604fbf78ff015e6bf8352f9f99485247e10, 0xc4852e1f6bb40c1e9b6dd6cea1534637973ad5e8340d37b7c984bd7f2214c821bec50d44514b8d954a5164566480be668cdfed5dab1c1f6b4c044acba74059dbc735495e98fc0, 0x4bbd8443e21fecd0aaeb0ea3cfd0d59ee0ae95fb5d207d6c4ccb23c222d546a7f3130981e3b10f083a45d33f0f6021a70d50b405e2f2d76d42c57c5ef60e34e0bea14e0612790,
  0x19fcc485805d88e835e0b69ad7c2cb7c763ebb2475661bb515d1661f71e0c235c70249b82533b81ca144d957c79c98931a95b438489055265de792c8e8d98c660375144241700, 0x7ed40536ec17b51629e1a52df46827ef4e86cd0ccc4aabf063290351937cdb5e555b4f70c2c9ab6e3f4cdd249e53254f85e92a39a86f53c3b8f8503afe1674b119cd212a1217, 0x22560273b450d2e8369e99ad6cff41e20d18c92808283bbcb5c20fa6061884cafc9ca871189f898a36081d1023887ec72cfbca21943103ad9b9f502ff23dd836a005305bd3cc,
  0x83c5530eeaa25f67ebb3553920781f56a8c4874e76a4a2091bf4fa407bd05a2af7d9223470505a8a03ae3d737d45d016dae57393f7a9dd79d06324978b07bf322a451f13a6b, 0x1bf202a8eb8bd6924cd9ca80861b0cf44f7382af2b3e2c79df5e515c807735c377d85a0923df87e6713f21f10dc511206c5b00c74c9ddcdde3e1228c65862c03f3adcac1560, 0x53a763f6416d8215a10d13664528b0a16c489a40a50f4360239a1d19a0f8ac58d23e83dda56da5d4a689601b64825cc75cbc0cc982506674cdbeb66b465bc97e28b03138a6,
  0xdc5dfceccfe68160325ad4fef7841b6f5f66576e13d41dc9cbff34a1a246855046137dc4a2dc07c58541800f700703af56640bc1c1f8c8d156caf2b15a0c984b7fc1aa8c8, 0x1fd70e55f9ca6528aa85e2c9ba084660b808d111b4c7bec134704e7c5ac6ea8661db70b845738877516087434f83f7b3b0307209d501519e154a1ceec22163e4d3ca4ad46, 0x40663e9771c33be1f9d70c7d6d87c698a318639b611ecdc20a3586c110f4c40b82ae7fd49afc0f7630002a1c85d0b0503adb5a5d2f3b93778fc1cab6190d1c1c8723e260,
  0x71935b215842af6efd778d528f47a35e3303a41289d12e69f30fdaddb56b3f78169b511043eac4adf85e787cf6e18b67fdd7c8fb90670c82ad15a9de20d68f0c356a577, 0xae0182cab5dcf72a5f6d8bdae08481587df2e27f9548df4ac18dee6d326495ed262994fe380d076ac67b2310994a676710216b8a8a84bb08e5ce63081ec54de144e93c, 0xe6a2d406d0432eb6e00d81c0f75d4743b3b700037740bd3359d3acd7970f0bfbc9d3448403908df509b922e74bd92fda860afc55af0f45e7c4fcdc1eef956062aba73,
  0x10743b0d95a8c835261cd72c82b9c73366b0366a92ec5daf43e09266acfbd1ea97451759dfa30b543e4a2895075163b7060f8519942257d073e6158db5fc5e048a180, 0x1017dae2e838b231c1b251302e0b6af68fb3a486833b54111c361b23b74d773a69673bfc5040cc92423106efc0e0466fea6cfcec0c756a53bfecf47ed33d87fda128, 0xd6959366571f87009af211b0864cd01c8d0126cb4e633f0b678cc7c2ba87438066cced641735ac98021c57722c4a29c1b9b4c10c624e76a52a81aebafa115e4860,
  0x976be5d159660e1bc9378112fb9f41ea66da6dc7f2086b663c517949e3ec57e20b24b64bc343eec5763288f44f77fb0671360c70bef665acc064352e0020a6668, 0x59d8f4ffafa211b2ef745634f3ce688e1b577c90bf1bf57682363d34516ab4ed404df8ec9862489aabc5e4f9baa039de19f8a8b7306adc01b1e22581554b0b80, 0x2c7b09255f30b9a57d691b0266dfc98f26e898b0ac6daa52a6c9649f90420de255340e1058722f6766bb863eb0564e3701f4ad1e1019bb693c061de2a88d5e6,
  0x123694c5bfc2e29a343a9053a3dfb0b97fdf3328bf698b97c24a655a088aa0d8f013a4fc4d3aa2c7d89848c0b41df39bea29bef6ee07affbd046ddb9a421b8, 0x61b9305648e2f8ff6a2e496288015a2e972837c05d339ac1c4a19a97c792562a6e622439b1d3bf4c224f252f12a1a8d9e7b5b60355fc565f146296b6bece, 0x1a8abbe73951cdb2fefed002d32448c81e77195ba534f2d47849842d086424c24e8900edf53508cc9b960d7d630ee6ac47f91b29ca1e03f3bc3802a3240,
  0x5c3e43fdc497e2e1e670f178ad3e19771de4929714162dd8c988cc51be539afffceedd82f2c3a7e8a2c2f45d618940dd1702e34b87e68db260a6d3ad4, 0xfcb3bd113c781d98c707ee7ca19bbfe7fe2e70b92f7656e09ea6ea70dc728d36241f415ac325fb73e818497162c504fc2216d0f04f1b4f80b809070, 0x218b77c229f211565a1394a1d957b662a93f15afed37bad75ac1ba09298991f1faa6de348e217abba48e8ca90e7e9f789ef810a4bea7f0ec663854,
  0x362f909334421887b56f668894eaee3bad70a1e93e03e255b2653a7d334107c808e9110124e2b226b019c9a69d7d474712dc1380c266f3d8fe40, 0x4118cb565157379ee3ba20a238304b737251bdbcbbf48cdfc304cc3a3862d291f459641037f4109bcea0bc5a95cc6649210e077f5f770d605e, 0x38a828d586ebe27b53f19280ef5e2d7a744dab2b8f4ed7d6c6752218eb57b209df02175f05e41bd5df4529df10f66da2f92e24c6693b3ef8,
  0x22a1b3acbe2f375d325dc8de5f6f7949d68794b16f737821fadc781ad64ff6fce3dc7359248d1efbb0b73240cf5018c1414792609b4736, 0xe5341ea908f070829a944d8ac69daebd2d6fdeb7bebeb58fd8de08dca71a43dc7591b54a77128111f713b2bd75c3edf682a60cbf980, 0x3d58d97e78096cabd2f972fb6d69e4e09f4962319c6e3ebfffef3c2e54c246a42f912f19b757b5413157d69a9238db762651b8d88,
  0xa0f04c2cbb61df7d01b5fa4e5f98caef323ee24aa00c800b62aea61919a51d92d5d95339fb58ab94d2f7e337de5793ca01c7e0, 0xf1b727b4ffaee7a0c1e07c7c8f8f6f6047d395a6b04d51d4a6ddd2fb40d1ac8373b7670a9440c693c7184740c2dcf523548, 0xbeec4449b8f41e881ae26bfbf7a16a7b5997681bbb3faca2b6a585fcc6a7aa75743aeac39873ab424aa1e8a107f6f780,
  0x472dbe6b1dd1f330ba6a23b1b5c647d1ab00b5b7c0b3d4ec3b1d458bf599b9517cc5dab8b775c5352f277fbe30255, 0xae2ab24aa02e6023e483b85f5616226e3ae83d06c2d013306d3c80686922aee012300e0ad82630ed9b0e514e4, 0x9127b29535ede62aaf540a59c622ea6f99ccd964f51147b0dd4fba17b63bf7436abb8a086626c4d7ad471,
  0x1fff72c63862ce15d31089418c4c0877ef50983f516f359bdeb96ac4d8edd931d7ae511db841ceda0, 0x14ec187112e0d895d297f6054ab33cdf750438e09c8e658b7f128ccb31e5bf4081ecc8d4155a, 0x1819b5db694a1b3bdb8d19af247ee98677bebf3834e7abb2c1af86cbb23eaf31d9efb8,
  0x15ccfe3b85d80e3101daf3cfe71d87ec01fac424e37d0ba6d7bef409f1ee57a, 0x3ffffffffebaa4e12b5a98536eb401f47f11afbd78a8b748b176a0, 0x30336cdd21fc654f9bd9c8d0bb0268abc114411610d,
  0x7ffffffffffffffffffffffff94, 0x1]

private theorem eulerianCoefficients_eq : descentCoeffs 107 = eulerianCoefficients := by
  decide +kernel

private theorem upper : upperOK (descentCoeffs 107) first gaps = true := by
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

private theorem lower_043 : lowerOK (rows.getD 43 []) gaps = true := by
  decide +kernel

private theorem lower_044 : lowerOK (rows.getD 44 []) gaps = true := by
  decide +kernel

private theorem lower_045 : lowerOK (rows.getD 45 []) gaps = true := by
  decide +kernel

private theorem lower_046 : lowerOK (rows.getD 46 []) gaps = true := by
  decide +kernel

private theorem lower_047 : lowerOK (rows.getD 47 []) gaps = true := by
  decide +kernel

private theorem lower_048 : lowerOK (rows.getD 48 []) gaps = true := by
  decide +kernel

private theorem lower_049 : lowerOK (rows.getD 49 []) gaps = true := by
  decide +kernel

private theorem lower_050 : lowerOK (rows.getD 50 []) gaps = true := by
  decide +kernel

private theorem lower_051 : lowerOK (rows.getD 51 []) gaps = true := by
  decide +kernel

private theorem lower_052 : lowerOK (rows.getD 52 []) gaps = true := by
  decide +kernel

private theorem lower (i : Fin (lastRepresentative 108 - 2)) :
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
  · exact lower_043
  · exact lower_044
  · exact lower_045
  · exact lower_046
  · exact lower_047
  · exact lower_048
  · exact lower_049
  · exact lower_050
  · exact lower_051
  · exact lower_052

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 108) :
    StrictNegativeInterlacing (originalQuotient 108 k) (eulerian 107) 105 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N108
