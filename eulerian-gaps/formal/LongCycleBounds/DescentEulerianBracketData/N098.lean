import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentPackedData.C127L104.N098

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N098

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L104.N098 LongCycleBounds.DescentNecklace.Packed.C127L104.N098.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L104.N098 LongCycleBounds.DescentNecklace.Packed.C127L104.N098.rows

private theorem actual : RepresentativeChecks 98 previousNodes rows :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L104.N098 LongCycleBounds.DescentNecklace.Packed.C127L104.N098.dataChecks

private def first : LongCycleFinite.Dyadic := ⟨-158456325028528675187087900672, 0⟩

private def gaps : List Window := [
  ⟨⟨-158451187093795313013095399424, 0⟩, ⟨-124948226502557696, 0⟩⟩,
  ⟨⟨-120444626875187200, 0⟩, ⟨-1313614069760, 0⟩⟩,
  ⟨⟨-1308845146112, 0⟩, ⟨-2492293120, 0⟩⟩,
  ⟨⟨-2432286720, 0⟩, ⟨-45538304, 0⟩⟩,
  ⟨⟨-45421312, 0⟩, ⟨-2838624, 0⟩⟩,
  ⟨⟨-2836456, 0⟩, ⟨-367295, 0⟩⟩,
  ⟨⟨-367165, 0⟩, ⟨-305295, 2⟩⟩,
  ⟨⟨-305233, 2⟩, ⟨-350669, 4⟩⟩,
  ⟨⟨-350621, 4⟩, ⟨-31713, 2⟩⟩,
  ⟨⟨-507359, 6⟩, ⟨-217743, 6⟩⟩,
  ⟨⟨-435453, 7⟩, ⟨-425507, 8⟩⟩,
  ⟨⟨-212741, 7⟩, ⟨-229929, 8⟩⟩,
  ⟨⟨-114959, 7⟩, ⟨-134575, 8⟩⟩,
  ⟨⟨-134569, 8⟩, ⟨-336031, 10⟩⟩,
  ⟨⟨-336019, 10⟩, ⟨-442193, 11⟩⟩,
  ⟨⟨-442179, 11⟩, ⟨-75975, 9⟩⟩,
  ⟨⟨-303891, 11⟩, ⟨-216603, 11⟩⟩,
  ⟨⟨-433195, 12⟩, ⟨-159203, 11⟩⟩,
  ⟨⟨-318399, 12⟩, ⟨-120123, 11⟩⟩,
  ⟨⟨-240241, 12⟩, ⟨-92695, 11⟩⟩,
  ⟨⟨-92693, 11⟩, ⟨-72933, 11⟩⟩,
  ⟨⟨-291727, 13⟩, ⟨-233439, 13⟩⟩,
  ⟨⟨-233435, 13⟩, ⟨-379141, 14⟩⟩,
  ⟨⟨-379135, 14⟩, ⟨-311899, 14⟩⟩,
  ⟨⟨-155947, 13⟩, ⟨-519047, 15⟩⟩,
  ⟨⟨-4055, 8⟩, ⟨-218133, 14⟩⟩,
  ⟨⟨-109065, 13⟩, ⟨-184989, 14⟩⟩,
  ⟨⟨-184987, 14⟩, ⟨-19767, 11⟩⟩,
  ⟨⟨-79067, 13⟩, ⟨-8509, 10⟩⟩,
  ⟨⟨-68071, 13⟩, ⟨-117955, 14⟩⟩,
  ⟨⟨-471815, 16⟩, ⟨-102777, 14⟩⟩,
  ⟨⟨-12847, 11⟩, ⟨-360027, 16⟩⟩,
  ⟨⟨-360023, 16⟩, ⟨-316727, 16⟩⟩,
  ⟨⟨-79181, 14⟩, ⟨-279765, 16⟩⟩,
  ⟨⟨-139881, 15⟩, ⟨-15501, 12⟩⟩,
  ⟨⟨-124007, 15⟩, ⟨-441159, 17⟩⟩,
  ⟨⟨-441155, 17⟩, ⟨-98371, 15⟩⟩,
  ⟨⟨-49185, 14⟩, ⟨-175927, 16⟩⟩,
  ⟨⟨-351851, 17⟩, ⟨-315331, 17⟩⟩,
  ⟨⟨-4927, 11⟩, ⟨-141575, 16⟩⟩,
  ⟨⟨-283147, 17⟩, ⟨-509361, 18⟩⟩,
  ⟨⟨-127339, 16⟩, ⟨-229401, 17⟩⟩,
  ⟨⟨-229399, 17⟩, ⟨-206875, 17⟩⟩,
  ⟨⟨-206873, 17⟩, ⟨-373483, 18⟩⟩,
  ⟨⟨-46685, 15⟩, ⟨-168691, 17⟩⟩,
  ⟨⟨-337379, 18⟩, ⟨-304929, 18⟩⟩,
  ⟨⟨-152463, 17⟩, ⟨-68921, 16⟩⟩,
  ⟨⟨-137841, 17⟩, ⟨-498541, 19⟩⟩,
  ⟨⟨-498537, 19⟩, ⟨-56341, 16⟩⟩,
  ⟨⟨-112681, 17⟩, ⟨-203687, 18⟩⟩,
  ⟨⟨-407371, 19⟩, ⟨-91999, 17⟩⟩,
  ⟨⟨-367993, 19⟩, ⟨-332181, 19⟩⟩,
  ⟨⟨-166089, 18⟩, ⟨-299563, 19⟩⟩,
  ⟨⟨-299561, 19⟩, ⟨-269829, 19⟩⟩,
  ⟨⟨-269827, 19⟩, ⟨-242699, 19⟩⟩,
  ⟨⟨-242697, 19⟩, ⟨-108965, 18⟩⟩,
  ⟨⟨-27241, 16⟩, ⟨-390617, 20⟩⟩,
  ⟨⟨-195307, 19⟩, ⟨-349289, 20⟩⟩,
  ⟨⟨-349285, 20⟩, ⟨-38943, 17⟩⟩,
  ⟨⟨-311541, 20⟩, ⟨-277079, 20⟩⟩,
  ⟨⟨-69269, 18⟩, ⟨-122817, 19⟩⟩,
  ⟨⟨-491263, 21⟩, ⟨-433939, 21⟩⟩,
  ⟨⟨-433935, 21⟩, ⟨-381751, 21⟩⟩,
  ⟨⟨-381747, 21⟩, ⟨-334319, 21⟩⟩,
  ⟨⟨-334315, 21⟩, ⟨-291299, 21⟩⟩,
  ⟨⟨-9103, 16⟩, ⟨-504763, 22⟩⟩,
  ⟨⟨-504757, 22⟩, ⟨-217281, 21⟩⟩,
  ⟨⟨-434557, 22⟩, ⟨-371481, 22⟩⟩,
  ⟨⟨-92869, 20⟩, ⟨-315039, 22⟩⟩,
  ⟨⟨-157517, 21⟩, ⟨-66199, 20⟩⟩,
  ⟨⟨-33099, 19⟩, ⟨-440659, 23⟩⟩,
  ⟨⟨-440653, 23⟩, ⟨-362509, 23⟩⟩,
  ⟨⟨-362503, 23⟩, ⟨-18399, 19⟩⟩,
  ⟨⟨-294379, 23⟩, ⟨-117781, 22⟩⟩,
  ⟨⟨-471117, 24⟩, ⟨-370681, 24⟩⟩,
  ⟨⟨-185337, 23⟩, ⟨-286045, 24⟩⟩,
  ⟨⟨-286039, 24⟩, ⟨-431653, 25⟩⟩,
  ⟨⟨-431645, 25⟩, ⟨-158635, 24⟩⟩,
  ⟨⟨-317263, 25⟩, ⟨-452261, 26⟩⟩,
  ⟨⟨-452251, 26⟩, ⟨-310821, 26⟩⟩,
  ⟨⟨-310813, 26⟩, ⟨-409019, 27⟩⟩,
  ⟨⟨-25563, 23⟩, ⟨-510645, 28⟩⟩,
  ⟨⟨-255315, 27⟩, ⟨-149445, 27⟩⟩,
  ⟨⟨-2335, 21⟩, ⟨-80755, 27⟩⟩,
  ⟨⟨-5047, 23⟩, ⟨-315619, 30⟩⟩,
  ⟨⟨-157803, 29⟩, ⟨-270875, 31⟩⟩,
  ⟨⟨-270863, 31⟩, ⟨-48999, 30⟩⟩,
  ⟨⟨-97993, 31⟩, ⟨-7035, 29⟩⟩,
  ⟨⟨-450215, 35⟩, ⟨-374207, 37⟩⟩,
  ⟨⟨-374183, 37⟩, ⟨-387647, 40⟩⟩,
  ⟨⟨-96905, 38⟩, ⟨-386697, 44⟩⟩,
  ⟨⟨-96667, 42⟩, ⟨-455965, 50⟩⟩,
  ⟨⟨-455929, 50⟩, ⟨-6861, 53⟩⟩,
  ⟨⟨-439067, 59⟩, ⟨-78405, 73⟩⟩,
  ⟨⟨-156795, 74⟩, ⟨-262149, 115⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private def eulerianCoefficients : List ℤ := [
  0x1, 0x1ffffffffffffffffffffff9e, 0x357f023f0dc1f8b0cdc846ca921f1add8448514,
  0x3fffffffeb856123dcbbbc6df13954e6741017b7335c9d7ba, 0x257412a30ee03b3d50239529048b85fb95798b5f6a59397d7b47ef930, 0x6afdf627ac5ce16fc4e414f8c18316f637a3f5099a0fe80c9f743d94a9ab9e6,
  0x13e1c2b81195646015a7296b9768fa8c0a8119104c9b133d1372e7d69cd4490aa7a5c, 0x7ff8638b8a1e88f4b3b844cdbb3beedf50366dbab6832ba37fb394967763cfcd78f53e1e2, 0xb2ac60868900e2837ca6758ec2b3739a625b9674887e1be0a4663fba309cddb60f313b17d49e4,
  0x4aa3b601096b6953ccd1d116eba08d71fff5da3fabae1ca9544d78fff2db441745cbc83770b6890d6, 0xbb8e1b8a629e1417bef0a01615c1149b5a880b1f932f4d745194942422e1f4132e0111f2c335440c4a54, 0xd179ba7e5d190d90fda1302378dd35f508b45c70b1cad5c75e85d103e2eb5dde234e8368b496983e1cd4402,
  0x75f20cd4d62ca46abe0b3728f5fa9300cac70950cd242a08e071aa410144765b4934798eba5bd0a8b78b17bc10, 0x24e1ce67f44a8e8124219030e9b18cf43c7f75b636bf40392d0e82de4132419290bb08a3c24af4bc787a9bee837de, 0x6e8da450bbeaaf1a315da2906bc10d6652e2cfee35ca599fd359eb2105f7eae63d64a7d31203c6e0960cf7f74a636bc,
  0xd2e080d758f9cfb184af98f5711bb9d3d5992eac03c4dac7833171450601d6cf11b2457266df318ece5f4fec15e7d6f2a, 0x10cbf6b510583cbca6cc0d4d9967f7d990f707115a872184e1b08d3206b3aa6d0402d3e5ab07809c6b70e6270d98c9307a62, 0xee239e55a9e85a7d2192819a1cff0c60163f4d9490adfe8e42c959d16241b18edc15a2f6d74c73ff1618060ae397552a01f52,
  0x97a48383c39cdf60893d36321861994f84c6bce0f59f2f2802621a9a775f0127ced6def13995db2c2b0e7cd862b7dbbea303c2c, 0x475628a5cf03663c95b933fec1d0d95951d62fab5714f193ee5994654f7fd47f05b7ad4e3137dbca993ae2ee2f2c7cbbde4277ed6, 0x19607cd7f6eacefd1b40165f0b8e1cb8a92ae791f164789fa43947075f922e79e2851b314decc748e41ae8964f099f088b2a1849250,
  0x6f6b362df8eaa2d18ba0d3b6a342dc42698a9aa3cbb338da9a6a7faa8cb9c763ca1756307d698d1cc703a9679418272f04ea000b408a, 0x17fdb820e028d5d81cb686ab42846ce86613273af5ec3c609df9404ad44f86ab825dd53a47bbadddd2ca3d203d9cdf13f3a40f4660bc24, 0x41d2574f735ce561bed6587ce5cab475ec9d08702f0b8ad3039301be8dc1147f97a6a76acc1835f0bd2ed9b4316513067f4c3dc82c546ae,
  0x91ac222816b1a802b1b9c73574868e94d58b2f3878ecb7a9c960b38957d4a22babbf13bd321e31931cc6569a068c1239ba1f192332244254, 0x10700ae37d14151851bfc14f8fa995d8b4a8e0f788124c76ff7986b85b508d8dab5954ca37c4975c0707085bbd37ce472a5c69c25610ea612a, 0x187363675b0af0a0e405d9cacff893e3d743491a0f4ea7b763ee928d1b553f77f16539a5d8b9c3c9d55b574b533d715ed48c02c5299647c6fcc,
  0x1e3a47cb8e2b2e668d62b5207b8899f996a5d9b505cb451a9a5c4f4356c9f8d3d7bd6bb2366efec2af452091832004afaed28bb53c3a2dc591be, 0x1f4cb01b34343d8ba43f0abe0ed4189d4eb03b7520e2d12c57e9603d4b7cfb407d269c076e61abd723f011cda62f42aae04d7c61d7de78d820df0, 0x1b55236dd4745c343f5996d08cec7773b598af7e16c6f49719315b3c9248b40f32b02a8a3279d1af8d540566b63e63f0f14ecc6b5c916e78c88662,
  0x1440d1b5d87ced220077ebecbf9e5d8a74ef73bf4f4364fa91e3970db5ca63e3640ba1400961092e69b425e4aaaa0cfe292f2557c67d1d63e343a64, 0xccde5de57933dae9bafd8f18fcc265f0a5c8331f23c254e07d8e620d4f1bc8272266f39fc14166754bf369fce2efcb400cef96cfe59560621eacc56, 0x6f0c67bb7ea051987c75ed1cb45a6bafc51c41e76267185ea1666e413c739a11c2e561de87f6a3629aafaf743e0569a38653c19369f71eb2c79b736f,
  0x33d5edb9ea1da25e82af667cb18b9b953a6f4c7924a6bad96c723b2f5cc6f637916c2e86ee119022dffb1a538bcf45ad1117bd34485dfb2fd2ecbe32c, 0x14eb1bf49695cf86f58d32297b8f7be766169cfbebba68ffd4c51755a953b06c1d1654854b2a5f3080d529cd05a881bddd459df2d4494553a058d2c448, 0x752e5bf22cccd44d30dea0e71e35d2e0057e2a08ede18d1d02f336041edb02f805a63b884c074de162e61790b35370483dd548da3733833351d9053344,
  0x23b4b753bad7a0ef5e3c8eb40b7c5c65481f83bb032b876800496c943f627715553a51f02af70b9ffb7b1feebb18133bb2b968c28b9eeb5e02841e075e0, 0x97ed2ef37482b4e93edc4622771f93310479aaae3c1e3b65de3a39777555dffd003a2a779d254f1833b0ba9e549186d15f5359326e59dcd541cb364a8fc, 0x235966807180d65667195c52f957e3f4567bbe5efaf1fabfc1b5f69b2d730a3c89e95bab556aef18f3ef1ec22f4f0124bb64b711b6ebf01dce57366b6918,
  0x73647d0174d0d68efbaa03fe7aee654a0188e1a3dfd3d856ac398735459355941f653eabcd06e31bd2c57b82d93fd85b692359ca555d8bdabb3d43cdf9d4, 0x14af0f3a6eca85e457ed4f06bfe09c0b89ed70ea1a989b956f41af140f1ac05a0b8c32228604d5f1dd7eb650e0bbb27c35225b75550003ac344f66c37ffc8, 0x343499390dee971784fe1332af97ddce56a8ea51fa9cc812efda3580805845a57dc44de89e61f16a6f16baab3adda0396923fc83611b112fef6c0578a539c,
  0x74219834c829c5d8ec31419b97de9de64699e8481f784deab256b07cbc3438c3621b86bdba114de68a58481fa491a8cdf756067018f149b1735385f6ef648, 0xe3f76f5f7d974e0a66a794c13c83ae16d8d5c4ebb3522828ba4b55e603213601d143d6b66d40ef10d93f19ba3534132a7e22a3ba8540551a335949ea77ed4, 0x18b4e302cf8b82715ca4bbc9abadf3d9c56d6f48ab43e1b0159a9d1169b32c246f893910e25bbfc23332cbc1a527612866fd37c97be0175af127e3c7c234a0,
  0x25e08fc2f04cab69cd27fe90c4b5f2db3e41e26e1bd06b8bdb2f63818c37c8346e4571ec11d103f4c0afb2c8c4ed0c8c891f34b005a01a3d65d3ac0093bfec, 0x335f38a9dce2e7685b2350f8d3ca1c29fba0460e84d190dc1627eb73b576e83d80c61590babe7bab73e4b6c4de2d0e982ab098b1d63cd612f310ee1c6fb958, 0x3daadfd6de51a52273a7d51bb9d22e4abbafeef147cdf017c894fff9f008cf9b546661e0983e0c77b7aeab3be9ecd6a3e3de3de7161ef7ab8626cd5ce75a64,
  0x41897775d07e856176912278519dc8acb0c4d3ff44a5996960080c2a598f75846e24dc492d2ce3d8eed2dc5dd9e2380b0016bf24735f52690a66a34e350c5c, 0x3daadfd6de51a52273a7d51bb9d22e4abbafeef147cdf017c894fff9f008cf9b546661e0983e0c77b7aeab3be9ecd6a3e3de3de7161ef7ab8626cd5ce75a64, 0x335f38a9dce2e7685b2350f8d3ca1c29fba0460e84d190dc1627eb73b576e83d80c61590babe7bab73e4b6c4de2d0e982ab098b1d63cd612f310ee1c6fb958,
  0x25e08fc2f04cab69cd27fe90c4b5f2db3e41e26e1bd06b8bdb2f63818c37c8346e4571ec11d103f4c0afb2c8c4ed0c8c891f34b005a01a3d65d3ac0093bfec, 0x18b4e302cf8b82715ca4bbc9abadf3d9c56d6f48ab43e1b0159a9d1169b32c246f893910e25bbfc23332cbc1a527612866fd37c97be0175af127e3c7c234a0, 0xe3f76f5f7d974e0a66a794c13c83ae16d8d5c4ebb3522828ba4b55e603213601d143d6b66d40ef10d93f19ba3534132a7e22a3ba8540551a335949ea77ed4,
  0x74219834c829c5d8ec31419b97de9de64699e8481f784deab256b07cbc3438c3621b86bdba114de68a58481fa491a8cdf756067018f149b1735385f6ef648, 0x343499390dee971784fe1332af97ddce56a8ea51fa9cc812efda3580805845a57dc44de89e61f16a6f16baab3adda0396923fc83611b112fef6c0578a539c, 0x14af0f3a6eca85e457ed4f06bfe09c0b89ed70ea1a989b956f41af140f1ac05a0b8c32228604d5f1dd7eb650e0bbb27c35225b75550003ac344f66c37ffc8,
  0x73647d0174d0d68efbaa03fe7aee654a0188e1a3dfd3d856ac398735459355941f653eabcd06e31bd2c57b82d93fd85b692359ca555d8bdabb3d43cdf9d4, 0x235966807180d65667195c52f957e3f4567bbe5efaf1fabfc1b5f69b2d730a3c89e95bab556aef18f3ef1ec22f4f0124bb64b711b6ebf01dce57366b6918, 0x97ed2ef37482b4e93edc4622771f93310479aaae3c1e3b65de3a39777555dffd003a2a779d254f1833b0ba9e549186d15f5359326e59dcd541cb364a8fc,
  0x23b4b753bad7a0ef5e3c8eb40b7c5c65481f83bb032b876800496c943f627715553a51f02af70b9ffb7b1feebb18133bb2b968c28b9eeb5e02841e075e0, 0x752e5bf22cccd44d30dea0e71e35d2e0057e2a08ede18d1d02f336041edb02f805a63b884c074de162e61790b35370483dd548da3733833351d9053344, 0x14eb1bf49695cf86f58d32297b8f7be766169cfbebba68ffd4c51755a953b06c1d1654854b2a5f3080d529cd05a881bddd459df2d4494553a058d2c448,
  0x33d5edb9ea1da25e82af667cb18b9b953a6f4c7924a6bad96c723b2f5cc6f637916c2e86ee119022dffb1a538bcf45ad1117bd34485dfb2fd2ecbe32c, 0x6f0c67bb7ea051987c75ed1cb45a6bafc51c41e76267185ea1666e413c739a11c2e561de87f6a3629aafaf743e0569a38653c19369f71eb2c79b736f, 0xccde5de57933dae9bafd8f18fcc265f0a5c8331f23c254e07d8e620d4f1bc8272266f39fc14166754bf369fce2efcb400cef96cfe59560621eacc56,
  0x1440d1b5d87ced220077ebecbf9e5d8a74ef73bf4f4364fa91e3970db5ca63e3640ba1400961092e69b425e4aaaa0cfe292f2557c67d1d63e343a64, 0x1b55236dd4745c343f5996d08cec7773b598af7e16c6f49719315b3c9248b40f32b02a8a3279d1af8d540566b63e63f0f14ecc6b5c916e78c88662, 0x1f4cb01b34343d8ba43f0abe0ed4189d4eb03b7520e2d12c57e9603d4b7cfb407d269c076e61abd723f011cda62f42aae04d7c61d7de78d820df0,
  0x1e3a47cb8e2b2e668d62b5207b8899f996a5d9b505cb451a9a5c4f4356c9f8d3d7bd6bb2366efec2af452091832004afaed28bb53c3a2dc591be, 0x187363675b0af0a0e405d9cacff893e3d743491a0f4ea7b763ee928d1b553f77f16539a5d8b9c3c9d55b574b533d715ed48c02c5299647c6fcc, 0x10700ae37d14151851bfc14f8fa995d8b4a8e0f788124c76ff7986b85b508d8dab5954ca37c4975c0707085bbd37ce472a5c69c25610ea612a,
  0x91ac222816b1a802b1b9c73574868e94d58b2f3878ecb7a9c960b38957d4a22babbf13bd321e31931cc6569a068c1239ba1f192332244254, 0x41d2574f735ce561bed6587ce5cab475ec9d08702f0b8ad3039301be8dc1147f97a6a76acc1835f0bd2ed9b4316513067f4c3dc82c546ae, 0x17fdb820e028d5d81cb686ab42846ce86613273af5ec3c609df9404ad44f86ab825dd53a47bbadddd2ca3d203d9cdf13f3a40f4660bc24,
  0x6f6b362df8eaa2d18ba0d3b6a342dc42698a9aa3cbb338da9a6a7faa8cb9c763ca1756307d698d1cc703a9679418272f04ea000b408a, 0x19607cd7f6eacefd1b40165f0b8e1cb8a92ae791f164789fa43947075f922e79e2851b314decc748e41ae8964f099f088b2a1849250, 0x475628a5cf03663c95b933fec1d0d95951d62fab5714f193ee5994654f7fd47f05b7ad4e3137dbca993ae2ee2f2c7cbbde4277ed6,
  0x97a48383c39cdf60893d36321861994f84c6bce0f59f2f2802621a9a775f0127ced6def13995db2c2b0e7cd862b7dbbea303c2c, 0xee239e55a9e85a7d2192819a1cff0c60163f4d9490adfe8e42c959d16241b18edc15a2f6d74c73ff1618060ae397552a01f52, 0x10cbf6b510583cbca6cc0d4d9967f7d990f707115a872184e1b08d3206b3aa6d0402d3e5ab07809c6b70e6270d98c9307a62,
  0xd2e080d758f9cfb184af98f5711bb9d3d5992eac03c4dac7833171450601d6cf11b2457266df318ece5f4fec15e7d6f2a, 0x6e8da450bbeaaf1a315da2906bc10d6652e2cfee35ca599fd359eb2105f7eae63d64a7d31203c6e0960cf7f74a636bc, 0x24e1ce67f44a8e8124219030e9b18cf43c7f75b636bf40392d0e82de4132419290bb08a3c24af4bc787a9bee837de,
  0x75f20cd4d62ca46abe0b3728f5fa9300cac70950cd242a08e071aa410144765b4934798eba5bd0a8b78b17bc10, 0xd179ba7e5d190d90fda1302378dd35f508b45c70b1cad5c75e85d103e2eb5dde234e8368b496983e1cd4402, 0xbb8e1b8a629e1417bef0a01615c1149b5a880b1f932f4d745194942422e1f4132e0111f2c335440c4a54,
  0x4aa3b601096b6953ccd1d116eba08d71fff5da3fabae1ca9544d78fff2db441745cbc83770b6890d6, 0xb2ac60868900e2837ca6758ec2b3739a625b9674887e1be0a4663fba309cddb60f313b17d49e4, 0x7ff8638b8a1e88f4b3b844cdbb3beedf50366dbab6832ba37fb394967763cfcd78f53e1e2,
  0x13e1c2b81195646015a7296b9768fa8c0a8119104c9b133d1372e7d69cd4490aa7a5c, 0x6afdf627ac5ce16fc4e414f8c18316f637a3f5099a0fe80c9f743d94a9ab9e6, 0x257412a30ee03b3d50239529048b85fb95798b5f6a59397d7b47ef930,
  0x3fffffffeb856123dcbbbc6df13954e6741017b7335c9d7ba, 0x357f023f0dc1f8b0cdc846ca921f1add8448514, 0x1ffffffffffffffffffffff9e,
  0x1]

private theorem eulerianCoefficients_eq : descentCoeffs 97 = eulerianCoefficients := by
  decide +kernel

private theorem upper : upperOK (descentCoeffs 97) first gaps = true := by
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

private theorem lower (i : Fin (lastRepresentative 98 - 2)) :
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

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 98) :
    StrictNegativeInterlacing (originalQuotient 98 k) (eulerian 97) 95 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N098
