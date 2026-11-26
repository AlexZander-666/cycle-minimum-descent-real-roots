import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentPackedData.C127L127.N121

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N121

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L127.N121 LongCycleBounds.DescentNecklace.Packed.C127L127.N121.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L127.N121 LongCycleBounds.DescentNecklace.Packed.C127L127.N121.rows

private theorem actual : RepresentativeChecks 121 previousNodes rows :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L127.N121 LongCycleBounds.DescentNecklace.Packed.C127L127.N121.dataChecks

private def first : LongCycleFinite.Dyadic := ⟨-1329227995784915872903807060280344576, 0⟩

private def gaps : List Window := [
  ⟨⟨-1329184895664508113104156172371361792, 0⟩, ⟨-1385127101394069749760, 0⟩⟩,
  ⟨⟨-1348229109647023276032, 0⟩, ⟨-1018098375196672, 0⟩⟩,
  ⟨⟨-964123521187840, 0⟩, ⟨-424147943424, 0⟩⟩,
  ⟨⟨-378499235840, 0⟩, ⟨-3106308096, 0⟩⟩,
  ⟨⟨-3086139392, 0⟩, ⟨-101814528, 0⟩⟩,
  ⟨⟨-101663232, 0⟩, ⟨-8280800, 0⟩⟩,
  ⟨⟨-8275904, 0⟩, ⟨-1207116, 0⟩⟩,
  ⟨⟨-1206736, 0⟩, ⟨-262385, 0⟩⟩,
  ⟨⟨-262334, 0⟩, ⟨-303527, 2⟩⟩,
  ⟨⟨-151743, 1⟩, ⟨-216785, 3⟩⟩,
  ⟨⟨-216763, 3⟩, ⟨-363483, 5⟩⟩,
  ⟨⟨-181727, 4⟩, ⟨-345171, 6⟩⟩,
  ⟨⟨-345149, 6⟩, ⟨-180903, 6⟩⟩,
  ⟨⟨-180893, 6⟩, ⟨-410695, 8⟩⟩,
  ⟨⟨-410677, 8⟩, ⟨-248781, 8⟩⟩,
  ⟨⟨-497543, 9⟩, ⟨-159051, 8⟩⟩,
  ⟨⟨-318091, 9⟩, ⟨-425543, 10⟩⟩,
  ⟨⟨-212765, 9⟩, ⟨-295715, 10⟩⟩,
  ⟨⟨-147853, 9⟩, ⟨-106147, 9⟩⟩,
  ⟨⟨-424577, 11⟩, ⟨-78367, 9⟩⟩,
  ⟨⟨-313461, 11⟩, ⟨-237105, 11⟩⟩,
  ⟨⟨-474201, 12⟩, ⟨-183173, 11⟩⟩,
  ⟨⟨-366339, 12⟩, ⟨-288293, 12⟩⟩,
  ⟨⟨-9009, 7⟩, ⟨-115297, 11⟩⟩,
  ⟨⟨-115295, 11⟩, ⟨-374235, 13⟩⟩,
  ⟨⟨-93557, 11⟩, ⟨-153793, 12⟩⟩,
  ⟨⟨-153791, 12⟩, ⟨-127855, 12⟩⟩,
  ⟨⟨-511413, 14⟩, ⟨-429535, 14⟩⟩,
  ⟨⟨-429529, 14⟩, ⟨-91021, 12⟩⟩,
  ⟨⟨-364079, 14⟩, ⟨-2431, 7⟩⟩,
  ⟨⟨-311163, 14⟩, ⟨-133967, 13⟩⟩,
  ⟨⟨-267931, 14⟩, ⟨-116135, 13⟩⟩,
  ⟨⟨-464535, 15⟩, ⟨-6331, 9⟩⟩,
  ⟨⟨-101295, 13⟩, ⟨-355383, 15⟩⟩,
  ⟨⟨-355379, 15⟩, ⟨-313289, 15⟩⟩,
  ⟨⟨-313285, 15⟩, ⟨-277459, 15⟩⟩,
  ⟨⟨-17341, 11⟩, ⟨-246765, 15⟩⟩,
  ⟨⟨-493525, 16⟩, ⟨-27539, 12⟩⟩,
  ⟨⟨-110155, 14⟩, ⟨-394779, 16⟩⟩,
  ⟨⟨-394775, 16⟩, ⟨-44355, 13⟩⟩,
  ⟨⟨-354837, 16⟩, ⟨-39985, 13⟩⟩,
  ⟨⟨-319877, 16⟩, ⟨-72285, 14⟩⟩,
  ⟨⟨-289137, 16⟩, ⟨-261993, 16⟩⟩,
  ⟨⟨-261991, 16⟩, ⟨-475855, 17⟩⟩,
  ⟨⟨-118963, 15⟩, ⟨-433023, 17⟩⟩,
  ⟨⟨-433019, 17⟩, ⟨-394773, 17⟩⟩,
  ⟨⟨-197385, 16⟩, ⟨-360505, 17⟩⟩,
  ⟨⟨-180251, 16⟩, ⟨-82427, 15⟩⟩,
  ⟨⟨-329705, 17⟩, ⟨-75487, 15⟩⟩,
  ⟨⟨-150973, 16⟩, ⟨-69215, 15⟩⟩,
  ⟨⟨-138429, 16⟩, ⟨-254127, 17⟩⟩,
  ⟨⟨-254125, 17⟩, ⟨-233479, 17⟩⟩,
  ⟨⟨-233477, 17⟩, ⟨-429361, 18⟩⟩,
  ⟨⟨-214679, 17⟩, ⟨-197531, 17⟩⟩,
  ⟨⟨-395059, 18⟩, ⟨-363705, 18⟩⟩,
  ⟨⟨-181851, 17⟩, ⟨-83747, 16⟩⟩,
  ⟨⟨-167493, 17⟩, ⟨-9645, 13⟩⟩,
  ⟨⟨-154319, 17⟩, ⟨-284429, 18⟩⟩,
  ⟨⟨-284427, 18⟩, ⟨-131073, 17⟩⟩,
  ⟨⟨-524287, 19⟩, ⟨-241607, 18⟩⟩,
  ⟨⟨-483211, 19⟩, ⟨-445307, 19⟩⟩,
  ⟨⟨-445303, 19⟩, ⟨-410283, 19⟩⟩,
  ⟨⟨-51285, 16⟩, ⟨-11809, 14⟩⟩,
  ⟨⟨-377885, 19⟩, ⟨-43487, 16⟩⟩,
  ⟨⟨-347893, 19⟩, ⟨-40013, 16⟩⟩,
  ⟨⟨-160051, 18⟩, ⟨-294331, 19⟩⟩,
  ⟨⟨-294329, 19⟩, ⟨-16901, 15⟩⟩,
  ⟨⟨-270413, 19⟩, ⟨-62053, 17⟩⟩,
  ⟨⟨-124105, 18⟩, ⟨-227589, 19⟩⟩,
  ⟨⟨-227587, 19⟩, ⟨-208427, 19⟩⟩,
  ⟨⟨-416851, 20⟩, ⟨-95311, 18⟩⟩,
  ⟨⟨-381241, 20⟩, ⟨-174075, 19⟩⟩,
  ⟨⟨-348147, 20⟩, ⟨-158699, 19⟩⟩,
  ⟨⟨-317395, 20⟩, ⟨-72207, 18⟩⟩,
  ⟨⟨-288825, 20⟩, ⟨-262297, 20⟩⟩,
  ⟨⟨-262295, 20⟩, ⟨-475341, 21⟩⟩,
  ⟨⟨-237669, 20⟩, ⟨-429661, 21⟩⟩,
  ⟨⟨-214829, 20⟩, ⟨-193665, 20⟩⟩,
  ⟨⟨-387327, 21⟩, ⟨-174073, 20⟩⟩,
  ⟨⟨-348143, 21⟩, ⟨-155961, 20⟩⟩,
  ⟨⟨-311919, 21⟩, ⟨-278483, 21⟩⟩,
  ⟨⟨-278481, 21⟩, ⟨-61919, 19⟩⟩,
  ⟨⟨-495347, 22⟩, ⟨-109675, 20⟩⟩,
  ⟨⟨-54837, 19⟩, ⟨-386737, 22⟩⟩,
  ⟨⟨-386733, 22⟩, ⟨-169603, 21⟩⟩,
  ⟨⟨-339203, 22⟩, ⟨-36983, 19⟩⟩,
  ⟨⟨-295861, 22⟩, ⟨-512965, 23⟩⟩,
  ⟨⟨-8015, 17⟩, ⟨-220847, 22⟩⟩,
  ⟨⟨-441689, 23⟩, ⟨-377499, 23⟩⟩,
  ⟨⟨-377495, 23⟩, ⟨-39997, 20⟩⟩,
  ⟨⟨-79993, 21⟩, ⟨-134371, 22⟩⟩,
  ⟨⟨-134369, 22⟩, ⟨-223419, 23⟩⟩,
  ⟨⟨-27927, 20⟩, ⟨-367259, 24⟩⟩,
  ⟨⟨-367253, 24⟩, ⟨-149009, 23⟩⟩,
  ⟨⟨-298013, 24⟩, ⟨-476745, 25⟩⟩,
  ⟨⟨-238369, 24⟩, ⟨-375171, 25⟩⟩,
  ⟨⟨-375165, 25⟩, ⟨-72457, 23⟩⟩,
  ⟨⟨-289823, 25⟩, ⟨-219225, 25⟩⟩,
  ⟨⟨-438441, 26⟩, ⟨-323707, 26⟩⟩,
  ⟨⟨-80925, 24⟩, ⟨-464783, 27⟩⟩,
  ⟨⟨-464773, 27⟩, ⟨-322985, 27⟩⟩,
  ⟨⟨-322977, 27⟩, ⟨-432065, 28⟩⟩,
  ⟨⟨-216027, 27⟩, ⟨-276233, 28⟩⟩,
  ⟨⟨-276225, 28⟩, ⟨-334663, 29⟩⟩,
  ⟨⟨-334653, 29⟩, ⟨-379879, 30⟩⟩,
  ⟨⟨-189933, 29⟩, ⟨-99549, 29⟩⟩,
  ⟨⟨-398181, 31⟩, ⟨-378131, 32⟩⟩,
  ⟨⟨-378115, 32⟩, ⟨-317007, 33⟩⟩,
  ⟨⟨-316993, 33⟩, ⟨-452825, 35⟩⟩,
  ⟨⟨-226401, 34⟩, ⟨-32741, 33⟩⟩,
  ⟨⟨-523827, 37⟩, ⟨-455589, 39⟩⟩,
  ⟨⟨-455561, 39⟩, ⟨-132853, 40⟩⟩,
  ⟨⟨-33211, 38⟩, ⟨-345703, 45⟩⟩,
  ⟨⟨-345679, 45⟩, ⟨-364777, 50⟩⟩,
  ⟨⟨-364749, 50⟩, ⟨-340901, 57⟩⟩,
  ⟨⟨-170437, 56⟩, ⟨-300335, 68⟩⟩,
  ⟨⟨-150155, 67⟩, ⟨-228929, 88⟩⟩,
  ⟨⟨-457815, 89⟩, ⟨-262165, 138⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private def eulerianCoefficients : List ℤ := [
  0x1, 0xffffffffffffffffffffffffffff87, 0x4949a9b699bf15c710b11e42db8e5bb060f0fcebb0ee60bd,
  0xffffffffffdd5c2ec8b154aeb4cc4748b26639b6a9a22e1874995f5d493b, 0x63236b1a07d0a88ed9490f63b300f1036d82bd3aa86610c0cfe753e1d350256126dc2f, 0x4949a987be01765d031172be2a9a6854f3cab40a98374c339f0568b3ba05cb90f072ab10060169,
  0x1d7fb79d040d9c040d9e67e9155201037caad1925c2d4b554e9e16a53266717768ffdcf049a3ec2834f6b, 0xffff20ea1b2b8882639f5552854608cbec14b7121e2fef0dcbca2e3163d482e807fcc04e45d3fb2b22aafd007d, 0x14fa9efc929e64ea5bd034c5b140d69ed489670b0d57ed7d94c1fa6b30667295442ecbddf6c29f4e350681770a679a56,
  0x63198088867ff842a83629db2892174b36217794cf0c388217c95a815c92bf2be2c34f58c5b5c7195edcbdd06b666e204bda, 0x8c0f96f9e062ebdf694d83053a20682bb7d09f998cde09a5f18ee4fb8c8c0bbaa4a7b0a0380c16f6a164699a448bc338c197c91e, 0x49076b2e9e7d0d1cd5db8de1a484cf8373170f5748b4bb63d07eea84a2f522a78cce8f1f7d876ff99db228a5d62edc9ba09f253eefb2,
  0x10760111584f6b1266a3caddc4c38cb96b0a496df0cef6822ff97090e33643e717dd6a75152f039c319cb8417b0cd4bc96140be81c82c342, 0x1d02b99d902bda6f86fb8dc248ca575dd6a8fc16c652e4e897302748373d5faaac0e4c60ef9deb66a161b7331bf0675b5a119f613b16766220e, 0x1b845fd5a67e4a70b28951a77172205ab8fbb444042c9ac1b2a152077465aed2030461269b8797d401205b6fac7515aff2e36b19e9f7d7afe7f42a,
  0xf2c9db8f55c58d51c643d7a1e4a3ff021e88314640e27498520817193f6f955a0982509b86ab6992d0dd8b6f7010be56c81136ebcb6bdf134a62f586, 0x52dcc574c9f37f2f62c987c91416521962a91a320e18c3778e76a90690814dcc6722e2dc04833ce20b8ce35fceb34e16bebaae7be7f843ae88298d0b127, 0x126c9a3c607847b574492e7874f81d4eac005d39fd4dd59e51dd009f7d63c30ae877c63abaf59bd3802e694468b9048b7b55b7d13bb2dda068e6fb36f1e111,
  0x2c8e97c15e822730a1c45023b89b171a0ae9c44bbe1a96f18c7a3068f9f4256cb00222bf9a7f1d852580282bff5784a0f6ec0b10e2c0f9a7eefa105fa8b96f6b, 0x4be85cd46c119aa7351e191fb29f18688aa234ef1a0b8fe3c11c0c601a79202c83d907c246ec59bd4d527e65acf30024eb8c70c6efb5dcb749eb049b09684732dd, 0x5de109e51f7cdff2c512328011fb7b77012e6303f2458fc7933ce80b67c67aae1b2eba261de4ad2bd85999883671dad3e07d3a2dd047744f8bdbf064c18e5800c4d1,
  0x567a29f26fafaf3486a36fbc8f77140ef4df76b5b96af943495c0176f0f1b5a432ea336253158a21d7d6034dfea9958a3115e1f29c1291def9964742ba26b68cb74917, 0x3ca6ee5f254a37b7a6f50afaac2172b7d929cb429a88df71faa972d5a6fbe3f19d70b10a2e2eff7326b438125dbd8e2902ea0004a98dd7c1fc7314ed48b224e407146bf5, 0x2102fcca989531744199a509d4cf65c3ff4e422e2b3a68153b72fe92d7b24aea139d0bbb80a2ba88a8279c7a0cf78860d07709ae69410f6c5c2c4a6009c790a450a61f7ea3,
  0xe2d1d3c81abecde407fafd9335dd60baf2021f989c642aa04724a5ecae67e89e7590094aff692014f483fc052cbe39bab1dce3b40e022fa9fc6e22ed217a7808547df29cd8c, 0x4df8fc197339b548c134a291e8033a86dea508b5c3be4e3791be9dd957c4bee6a3d020a3152a689f0e90f8e1d3b43f605f595c67646a4ef31f2e25b2239653952fb9175c4b7d4, 0x15bb911901136e7f3c45196876482e58f0ed673e3e4d88e800f76621bfb49cc3cc19e10c3864b78d97c9637ac4f9a00236474bf59bb255f69314b888eb3073c578818d7ed7d061c,
  0x4f78eec89cd8d051f626165b49f89f6a6b76c77f9b66a47dee2647d717d94c869512d9ada5067cf9239cb817e52b630d15508e939769988b26181dca4fb5587e7a9f5d9f74822a84, 0xf0b49a6a3a59cef48abba2416786d491aa21fb4ef2ddb29bfaa200279a3724f68d5cebe3a97bcddd88eab8ff5bea9123fbd3b4b661539e7389b2eea4b79d09a759f70a410c524f844, 0x2614477c71b561e79bfe35313bc6305b9781e13ad888998063170bd4ad170486bd02ae6e1ffce843ad3f9e49f30b64db016b40bdeea434b61e57aabbb25f69ce927881e69ada130665c,
  0x513288236fd0b5b4be3bec30bbdbedc54760984e88d5e03874ec5cae161e12e5279f4d4b8c85c1fc96f100ff73e9ca00388b0b5ef28fa3f1efdb2c2a6816e335897559b42c6a1f5d4294, 0x92e94b49a060ef58cf765ef526eb9fb6b885d279e74f87c0ec3e222f72bac4ce5c3f950f0a97d676c47836f1a25352733d19e217a8d325896f9f378b51eec6838251eca3fa17298c454cc, 0xe302b66ff46d060c3b3d6c079ed551713324f34ee32a8842b14c8bac66b5aa8b217fed1ffcb3845369bfbefc54adc74924556c00d1a7d38949930dcef0b4d948abaa9ddbce8ef3b5468cf1,
  0x12d581406d327b569640b2100f4f526c9b6c0498b77adbea449a715de2c82b84c9c91b334711985a30a1e5ba4a4bc43d7b16f3d567e291a5c0252b8ecb071754f735b83953459c03f423e117, 0x15978f09b0e176b17f102ee17121bcd7e8c8630846ba0b88dadc847ca5d5b28522df3b96fecd11bdcc8e2f9667b4fcb893869371e61e0ad4b62233e18b90c3e7566cc0781653a050a659cb6ad, 0x157b65062dee6265e517075791120797f7d85bb4a485eb5de7e301b4529ee6da16e7fe06960ec7f27cf0e69009b6e12c864ab000e41fccba0dba4c2365d45386c71c6486b32fedb80c351998cb,
  0x12a114701e4aa33282331445fed608f9cc0b3f99ed24f141548d5682adea515956944487b07fd1a4eb6a0631bf5a12aba1c7a90022702a1e0ae57cb7337edfceb55d220a06c5812bb87e7f731af, 0xe2359c096c26604da1fa134ec2ee759b996de87b1a5e289ede91b1b3f516f3002e036d9bf38f3beac8be02d4e98b9f64097dce24fc6fe020fa6d4061c4ff3753e4862018d062dae6e8deb7d10e9, 0x96c9ee9087c8ce20152d085ecdce3a6f163ba162841983e766c5594983e63eea9526c9bb6c40f843705775bd2cefa20e99fecd300be9a70bb0798ff8c46917a88d1feb7b055cd50293471251182b,
  0x58949f94d17bd02d4befd65cd0f0ffe7918ad05085ab8f42be0fc7029a48c2e6237146f773145998ab46d78a251156d568e560607841091ae8d989cb27330298bef3ddcf216b1921b4d8aa22a56bd, 0x2dff9764e29314502a7e463301a0b345a47e0a20e25f334424fcd78ffc1535719db39bd833769c284c6ce24859a0db71e03aba1748ad076603edccbf9966092b9e4ea53bb0c642735f4635e601a9fa, 0x152c6ae2beffce57ee9e547fbfa84f9a6f65826534e5e1fb6696f3789d277c593fc33ebf005c045350a7c9eb6d08aa5e9a7169aeb832a05796a138154b605691c0c6f05e4c0e10736489ebe5aabbc56,
  0x8a95b3b9ee1359261a0cb67d951540c0e4eb4092d13e0902e4572c14722017c2ade2b744be10332d8f267b10d3fad960127b3d60a34667dc7c5ab0a91402634ce37607b43ef23e96ceb9e94d1a6d872, 0x327fc0636eb5c5775ca73daf16b56ad0e57dc80b217a090d1da5a5a4432cebb27318eda2baacae259c9982324c94fbabd07267e25e5e150e1ead53f661b917cbf5a4f7f87cba8d91fe912a69d3c7823e, 0x106d21f8293a51df1b5be1f36d00831a142e64c3b26bf242764699f89aea8c3c5d860e84207ef5c0219622c5f1663ae08ed43eb5200e6aa119520ae6b694d057ca973ed56221c43669a9f7f414d179c0e,
  0x4c766d21ba6eb589d84b83ec46724e6cd71470d496d98d89f1f7f1d1e6c9e5dbf557a16a1d1d9f6e6c5de2a8252ca8556a2d8f5ccbea4f7445256ed9c8a6ef9532e8183bfab80b07cc314c5c874ed5d22, 0x13ee74d09ce4db0633711b013dc743128c8bdc42620978cb423716bda65354317b37ce8f88d3cca49aec5982b766dff99057b022a3be820f46dd067b0983a056a79a37d90e0e47f5a593a3b862a0491de6, 0x4a9a07a26160e391869e43b5b00ed9ae2e38183996f0db08d5bfd98736946d9c733ce59d393364a7bcdccf57328303ef5035b551d561a2734099d705ed26abf2981484d507cb3856b08f8e0ca8558b99ea,
  0xfaf387454891c5c85ed5a75f970bebb86856bc19c310907ca04f8ce19cc33cf01b9bbac78f5f557c6852158072efbe3cf8a0ceef0d3191db5ab4be26f8d4b2686fd5d8e95a9f052f686ab85c2f0c8aa81f, 0x2f7aeeea0e76e39f9b3d341f9bb014c2d11183c6bd077c020c5b5ec20dec57fb474aab34902864610ffd68ba1086d87a96f1a647dd5d006e8cb04ccb7ec85ec43c6d61cd9b01bc88414d45fa4feb20efad9, 0x81801286953cb7aa3d10737228eed0d8c8219f306081cda87d71977d32e8de80680b56334b9902bec8d1e114c77762055c67911e24ab05293d5b0ef01b6640c7cf17f30330700020a4e7ff82b6eb7ef68c3,
  0x13e9135e03c709f80de2cc110004f1c1be4b8e8570b11d006d870d324d0916e576e7a70df875cf2c59865e03e7f739d2f80ccafec7f2d3cd38dadd60b3c33bcaf3371dcf4f0b96f6d0d9e6e2c359efb460c5, 0x2c378864cd6ceaf2e067990bae8ae686c5ac24932310a58fe08820a010ab2bc4c324317fac22144fd642a8ef32ebe729013f3e9fab1c096a18df9fbdec3dd873e3a0fbc35c142f0ab6df45730791273657a9, 0x58b8a14666d119f9cf6eb2e56108760a280ca8759664bd88d0a04b12328d56c5a811b530a63bbd8c55d7fa3bb578640ae6ce2351aab74647d36cd3380a77ff611917cff1178bb51b8423be5092bf748314ff,
  0xa0f46f79575c6c92c887e7c1109002fe6f3b3691b28a392e274d080291adf9acc42ac1b0bb67594e7a150aa01bb71e8fdaf403909d8980099b13ebfc03a7558c192b88e017c4b7cfd28b1d83164ed4f88fed, 0x1082a9a232919334cb799f6c8b1bbfc3ef042e737d022502fe43b79e02eadbbe5a57a2aaa94a3bb9a5e739d79afdde39fd034869ba1455d962994c7b165d7f8d9d5cd525993b5405829942fc745c4150823eb, 0x1886e20a749a956f23f3a5ea5a6d7249481bc7bcc5073f00ab1330263052d53b7b5146123f1659a65b3b9e3870c4848710f08bf05e95173e4f84229d2ed65fa68351c8cc23c47f41462f673c39c0b84c929e8,
  0x20fdf2a35844caddec3c776a5c3cc7346b5c2e517515475a625da38f15c20b83788a115c54ea4c8e643256d5529c332181a4f3a3f33e1369507b9cfc582d459bf81546ed08dcb6844d131944a179753dacb58, 0x28322a2d517db8c4b4974a4b7a7ce99e8b1690000029e4de2df31204f8bb198d5523192109f633ff8ce9a6cb38094c1193fea2e73d0c00b3532117e38b5923ed66373a3838ed25af708839dcddf16fdcf12c8, 0x2c5da54f988c192d253c3e37137ee5806c13beec344a7a22be81a271792fc5340ce88e76dbcd79046d47ccd587bdee25ad147938725397cd0739e3362023a15c46f12a68444ea4af21fd08d509bb1bef06bf8,
  0x2c5da54f988c192d253c3e37137ee5806c13beec344a7a22be81a271792fc5340ce88e76dbcd79046d47ccd587bdee25ad147938725397cd0739e3362023a15c46f12a68444ea4af21fd08d509bb1bef06bf8, 0x28322a2d517db8c4b4974a4b7a7ce99e8b1690000029e4de2df31204f8bb198d5523192109f633ff8ce9a6cb38094c1193fea2e73d0c00b3532117e38b5923ed66373a3838ed25af708839dcddf16fdcf12c8, 0x20fdf2a35844caddec3c776a5c3cc7346b5c2e517515475a625da38f15c20b83788a115c54ea4c8e643256d5529c332181a4f3a3f33e1369507b9cfc582d459bf81546ed08dcb6844d131944a179753dacb58,
  0x1886e20a749a956f23f3a5ea5a6d7249481bc7bcc5073f00ab1330263052d53b7b5146123f1659a65b3b9e3870c4848710f08bf05e95173e4f84229d2ed65fa68351c8cc23c47f41462f673c39c0b84c929e8, 0x1082a9a232919334cb799f6c8b1bbfc3ef042e737d022502fe43b79e02eadbbe5a57a2aaa94a3bb9a5e739d79afdde39fd034869ba1455d962994c7b165d7f8d9d5cd525993b5405829942fc745c4150823eb, 0xa0f46f79575c6c92c887e7c1109002fe6f3b3691b28a392e274d080291adf9acc42ac1b0bb67594e7a150aa01bb71e8fdaf403909d8980099b13ebfc03a7558c192b88e017c4b7cfd28b1d83164ed4f88fed,
  0x58b8a14666d119f9cf6eb2e56108760a280ca8759664bd88d0a04b12328d56c5a811b530a63bbd8c55d7fa3bb578640ae6ce2351aab74647d36cd3380a77ff611917cff1178bb51b8423be5092bf748314ff, 0x2c378864cd6ceaf2e067990bae8ae686c5ac24932310a58fe08820a010ab2bc4c324317fac22144fd642a8ef32ebe729013f3e9fab1c096a18df9fbdec3dd873e3a0fbc35c142f0ab6df45730791273657a9, 0x13e9135e03c709f80de2cc110004f1c1be4b8e8570b11d006d870d324d0916e576e7a70df875cf2c59865e03e7f739d2f80ccafec7f2d3cd38dadd60b3c33bcaf3371dcf4f0b96f6d0d9e6e2c359efb460c5,
  0x81801286953cb7aa3d10737228eed0d8c8219f306081cda87d71977d32e8de80680b56334b9902bec8d1e114c77762055c67911e24ab05293d5b0ef01b6640c7cf17f30330700020a4e7ff82b6eb7ef68c3, 0x2f7aeeea0e76e39f9b3d341f9bb014c2d11183c6bd077c020c5b5ec20dec57fb474aab34902864610ffd68ba1086d87a96f1a647dd5d006e8cb04ccb7ec85ec43c6d61cd9b01bc88414d45fa4feb20efad9, 0xfaf387454891c5c85ed5a75f970bebb86856bc19c310907ca04f8ce19cc33cf01b9bbac78f5f557c6852158072efbe3cf8a0ceef0d3191db5ab4be26f8d4b2686fd5d8e95a9f052f686ab85c2f0c8aa81f,
  0x4a9a07a26160e391869e43b5b00ed9ae2e38183996f0db08d5bfd98736946d9c733ce59d393364a7bcdccf57328303ef5035b551d561a2734099d705ed26abf2981484d507cb3856b08f8e0ca8558b99ea, 0x13ee74d09ce4db0633711b013dc743128c8bdc42620978cb423716bda65354317b37ce8f88d3cca49aec5982b766dff99057b022a3be820f46dd067b0983a056a79a37d90e0e47f5a593a3b862a0491de6, 0x4c766d21ba6eb589d84b83ec46724e6cd71470d496d98d89f1f7f1d1e6c9e5dbf557a16a1d1d9f6e6c5de2a8252ca8556a2d8f5ccbea4f7445256ed9c8a6ef9532e8183bfab80b07cc314c5c874ed5d22,
  0x106d21f8293a51df1b5be1f36d00831a142e64c3b26bf242764699f89aea8c3c5d860e84207ef5c0219622c5f1663ae08ed43eb5200e6aa119520ae6b694d057ca973ed56221c43669a9f7f414d179c0e, 0x327fc0636eb5c5775ca73daf16b56ad0e57dc80b217a090d1da5a5a4432cebb27318eda2baacae259c9982324c94fbabd07267e25e5e150e1ead53f661b917cbf5a4f7f87cba8d91fe912a69d3c7823e, 0x8a95b3b9ee1359261a0cb67d951540c0e4eb4092d13e0902e4572c14722017c2ade2b744be10332d8f267b10d3fad960127b3d60a34667dc7c5ab0a91402634ce37607b43ef23e96ceb9e94d1a6d872,
  0x152c6ae2beffce57ee9e547fbfa84f9a6f65826534e5e1fb6696f3789d277c593fc33ebf005c045350a7c9eb6d08aa5e9a7169aeb832a05796a138154b605691c0c6f05e4c0e10736489ebe5aabbc56, 0x2dff9764e29314502a7e463301a0b345a47e0a20e25f334424fcd78ffc1535719db39bd833769c284c6ce24859a0db71e03aba1748ad076603edccbf9966092b9e4ea53bb0c642735f4635e601a9fa, 0x58949f94d17bd02d4befd65cd0f0ffe7918ad05085ab8f42be0fc7029a48c2e6237146f773145998ab46d78a251156d568e560607841091ae8d989cb27330298bef3ddcf216b1921b4d8aa22a56bd,
  0x96c9ee9087c8ce20152d085ecdce3a6f163ba162841983e766c5594983e63eea9526c9bb6c40f843705775bd2cefa20e99fecd300be9a70bb0798ff8c46917a88d1feb7b055cd50293471251182b, 0xe2359c096c26604da1fa134ec2ee759b996de87b1a5e289ede91b1b3f516f3002e036d9bf38f3beac8be02d4e98b9f64097dce24fc6fe020fa6d4061c4ff3753e4862018d062dae6e8deb7d10e9, 0x12a114701e4aa33282331445fed608f9cc0b3f99ed24f141548d5682adea515956944487b07fd1a4eb6a0631bf5a12aba1c7a90022702a1e0ae57cb7337edfceb55d220a06c5812bb87e7f731af,
  0x157b65062dee6265e517075791120797f7d85bb4a485eb5de7e301b4529ee6da16e7fe06960ec7f27cf0e69009b6e12c864ab000e41fccba0dba4c2365d45386c71c6486b32fedb80c351998cb, 0x15978f09b0e176b17f102ee17121bcd7e8c8630846ba0b88dadc847ca5d5b28522df3b96fecd11bdcc8e2f9667b4fcb893869371e61e0ad4b62233e18b90c3e7566cc0781653a050a659cb6ad, 0x12d581406d327b569640b2100f4f526c9b6c0498b77adbea449a715de2c82b84c9c91b334711985a30a1e5ba4a4bc43d7b16f3d567e291a5c0252b8ecb071754f735b83953459c03f423e117,
  0xe302b66ff46d060c3b3d6c079ed551713324f34ee32a8842b14c8bac66b5aa8b217fed1ffcb3845369bfbefc54adc74924556c00d1a7d38949930dcef0b4d948abaa9ddbce8ef3b5468cf1, 0x92e94b49a060ef58cf765ef526eb9fb6b885d279e74f87c0ec3e222f72bac4ce5c3f950f0a97d676c47836f1a25352733d19e217a8d325896f9f378b51eec6838251eca3fa17298c454cc, 0x513288236fd0b5b4be3bec30bbdbedc54760984e88d5e03874ec5cae161e12e5279f4d4b8c85c1fc96f100ff73e9ca00388b0b5ef28fa3f1efdb2c2a6816e335897559b42c6a1f5d4294,
  0x2614477c71b561e79bfe35313bc6305b9781e13ad888998063170bd4ad170486bd02ae6e1ffce843ad3f9e49f30b64db016b40bdeea434b61e57aabbb25f69ce927881e69ada130665c, 0xf0b49a6a3a59cef48abba2416786d491aa21fb4ef2ddb29bfaa200279a3724f68d5cebe3a97bcddd88eab8ff5bea9123fbd3b4b661539e7389b2eea4b79d09a759f70a410c524f844, 0x4f78eec89cd8d051f626165b49f89f6a6b76c77f9b66a47dee2647d717d94c869512d9ada5067cf9239cb817e52b630d15508e939769988b26181dca4fb5587e7a9f5d9f74822a84,
  0x15bb911901136e7f3c45196876482e58f0ed673e3e4d88e800f76621bfb49cc3cc19e10c3864b78d97c9637ac4f9a00236474bf59bb255f69314b888eb3073c578818d7ed7d061c, 0x4df8fc197339b548c134a291e8033a86dea508b5c3be4e3791be9dd957c4bee6a3d020a3152a689f0e90f8e1d3b43f605f595c67646a4ef31f2e25b2239653952fb9175c4b7d4, 0xe2d1d3c81abecde407fafd9335dd60baf2021f989c642aa04724a5ecae67e89e7590094aff692014f483fc052cbe39bab1dce3b40e022fa9fc6e22ed217a7808547df29cd8c,
  0x2102fcca989531744199a509d4cf65c3ff4e422e2b3a68153b72fe92d7b24aea139d0bbb80a2ba88a8279c7a0cf78860d07709ae69410f6c5c2c4a6009c790a450a61f7ea3, 0x3ca6ee5f254a37b7a6f50afaac2172b7d929cb429a88df71faa972d5a6fbe3f19d70b10a2e2eff7326b438125dbd8e2902ea0004a98dd7c1fc7314ed48b224e407146bf5, 0x567a29f26fafaf3486a36fbc8f77140ef4df76b5b96af943495c0176f0f1b5a432ea336253158a21d7d6034dfea9958a3115e1f29c1291def9964742ba26b68cb74917,
  0x5de109e51f7cdff2c512328011fb7b77012e6303f2458fc7933ce80b67c67aae1b2eba261de4ad2bd85999883671dad3e07d3a2dd047744f8bdbf064c18e5800c4d1, 0x4be85cd46c119aa7351e191fb29f18688aa234ef1a0b8fe3c11c0c601a79202c83d907c246ec59bd4d527e65acf30024eb8c70c6efb5dcb749eb049b09684732dd, 0x2c8e97c15e822730a1c45023b89b171a0ae9c44bbe1a96f18c7a3068f9f4256cb00222bf9a7f1d852580282bff5784a0f6ec0b10e2c0f9a7eefa105fa8b96f6b,
  0x126c9a3c607847b574492e7874f81d4eac005d39fd4dd59e51dd009f7d63c30ae877c63abaf59bd3802e694468b9048b7b55b7d13bb2dda068e6fb36f1e111, 0x52dcc574c9f37f2f62c987c91416521962a91a320e18c3778e76a90690814dcc6722e2dc04833ce20b8ce35fceb34e16bebaae7be7f843ae88298d0b127, 0xf2c9db8f55c58d51c643d7a1e4a3ff021e88314640e27498520817193f6f955a0982509b86ab6992d0dd8b6f7010be56c81136ebcb6bdf134a62f586,
  0x1b845fd5a67e4a70b28951a77172205ab8fbb444042c9ac1b2a152077465aed2030461269b8797d401205b6fac7515aff2e36b19e9f7d7afe7f42a, 0x1d02b99d902bda6f86fb8dc248ca575dd6a8fc16c652e4e897302748373d5faaac0e4c60ef9deb66a161b7331bf0675b5a119f613b16766220e, 0x10760111584f6b1266a3caddc4c38cb96b0a496df0cef6822ff97090e33643e717dd6a75152f039c319cb8417b0cd4bc96140be81c82c342,
  0x49076b2e9e7d0d1cd5db8de1a484cf8373170f5748b4bb63d07eea84a2f522a78cce8f1f7d876ff99db228a5d62edc9ba09f253eefb2, 0x8c0f96f9e062ebdf694d83053a20682bb7d09f998cde09a5f18ee4fb8c8c0bbaa4a7b0a0380c16f6a164699a448bc338c197c91e, 0x63198088867ff842a83629db2892174b36217794cf0c388217c95a815c92bf2be2c34f58c5b5c7195edcbdd06b666e204bda,
  0x14fa9efc929e64ea5bd034c5b140d69ed489670b0d57ed7d94c1fa6b30667295442ecbddf6c29f4e350681770a679a56, 0xffff20ea1b2b8882639f5552854608cbec14b7121e2fef0dcbca2e3163d482e807fcc04e45d3fb2b22aafd007d, 0x1d7fb79d040d9c040d9e67e9155201037caad1925c2d4b554e9e16a53266717768ffdcf049a3ec2834f6b,
  0x4949a987be01765d031172be2a9a6854f3cab40a98374c339f0568b3ba05cb90f072ab10060169, 0x63236b1a07d0a88ed9490f63b300f1036d82bd3aa86610c0cfe753e1d350256126dc2f, 0xffffffffffdd5c2ec8b154aeb4cc4748b26639b6a9a22e1874995f5d493b,
  0x4949a9b699bf15c710b11e42db8e5bb060f0fcebb0ee60bd, 0xffffffffffffffffffffffffffff87, 0x1]

private theorem eulerianCoefficients_eq : descentCoeffs 120 = eulerianCoefficients := by
  decide +kernel

private theorem upper : upperOK (descentCoeffs 120) first gaps = true := by
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

private theorem lower_053 : lowerOK (rows.getD 53 []) gaps = true := by
  decide +kernel

private theorem lower_054 : lowerOK (rows.getD 54 []) gaps = true := by
  decide +kernel

private theorem lower_055 : lowerOK (rows.getD 55 []) gaps = true := by
  decide +kernel

private theorem lower_056 : lowerOK (rows.getD 56 []) gaps = true := by
  decide +kernel

private theorem lower_057 : lowerOK (rows.getD 57 []) gaps = true := by
  decide +kernel

private theorem lower_058 : lowerOK (rows.getD 58 []) gaps = true := by
  decide +kernel

private theorem lower (i : Fin (lastRepresentative 121 - 2)) :
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
  · exact lower_053
  · exact lower_054
  · exact lower_055
  · exact lower_056
  · exact lower_057
  · exact lower_058

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 121) :
    StrictNegativeInterlacing (originalQuotient 121 k) (eulerian 120) 118 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N121
