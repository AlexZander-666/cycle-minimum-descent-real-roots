import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentPackedData.C127L096.N095

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N095

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L096.N095 LongCycleBounds.DescentNecklace.Packed.C127L096.N095.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L096.N095 LongCycleBounds.DescentNecklace.Packed.C127L096.N095.rows

private theorem actual : RepresentativeChecks 95 previousNodes rows :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L096.N095 LongCycleBounds.DescentNecklace.Packed.C127L096.N095.dataChecks

private def first : LongCycleFinite.Dyadic := ⟨-19807040628566084398385987584, 0⟩

private def gaps : List Window := [
  ⟨⟨-19806398386724414126636924928, 0⟩, ⟨-35722033274814464, 0⟩⟩,
  ⟨⟨-35159014601916416, 0⟩, ⟨-554531028992, 0⟩⟩,
  ⟨⟨-553104965632, 0⟩, ⟨-1262145536, 0⟩⟩,
  ⟨⟨-1236877312, 0⟩, ⟨-26254400, 0⟩⟩,
  ⟨⟨-26194048, 0⟩, ⟨-1776400, 0⟩⟩,
  ⟨⟨-1775156, 0⟩, ⟨-488619, 1⟩⟩,
  ⟨⟨-244229, 0⟩, ⟨-106269, 1⟩⟩,
  ⟨⟨-212497, 2⟩, ⟨-506165, 5⟩⟩,
  ⟨⟨-126525, 3⟩, ⟨-376985, 6⟩⟩,
  ⟨⟨-376949, 6⟩, ⟨-165651, 6⟩⟩,
  ⟨⟨-165639, 6⟩, ⟨-330155, 8⟩⟩,
  ⟨⟨-41267, 5⟩, ⟨-11337, 4⟩⟩,
  ⟨⟨-362767, 9⟩, ⟨-430723, 10⟩⟩,
  ⟨⟨-215353, 9⟩, ⟨-136073, 9⟩⟩,
  ⟨⟨-272137, 10⟩, ⟨-361901, 11⟩⟩,
  ⟨⟨-180945, 10⟩, ⟨-501991, 12⟩⟩,
  ⟨⟨-501977, 12⟩, ⟨-22541, 8⟩⟩,
  ⟨⟨-360647, 12⟩, ⟨-266945, 12⟩⟩,
  ⟨⟨-133469, 11⟩, ⟨-405311, 13⟩⟩,
  ⟨⟨-202651, 12⟩, ⟨-157231, 12⟩⟩,
  ⟨⟨-39307, 10⟩, ⟨-248599, 13⟩⟩,
  ⟨⟨-248595, 13⟩, ⟨-399529, 14⟩⟩,
  ⟨⟨-199761, 13⟩, ⟨-325645, 14⟩⟩,
  ⟨⟨-325639, 14⟩, ⟨-33595, 11⟩⟩,
  ⟨⟨-67189, 12⟩, ⟨-56065, 12⟩⟩,
  ⟨⟨-224257, 14⟩, ⟨-188955, 14⟩⟩,
  ⟨⟨-377905, 15⟩, ⟨-20073, 11⟩⟩,
  ⟨⟨-321163, 15⟩, ⟨-275035, 15⟩⟩,
  ⟨⟨-275031, 15⟩, ⟨-474273, 16⟩⟩,
  ⟨⟨-474267, 16⟩, ⟨-51425, 13⟩⟩,
  ⟨⟨-411395, 16⟩, ⟨-358795, 16⟩⟩,
  ⟨⟨-358791, 16⟩, ⟨-314427, 16⟩⟩,
  ⟨⟨-314423, 16⟩, ⟨-276729, 16⟩⟩,
  ⟨⟨-276725, 16⟩, ⟨-955, 8⟩⟩,
  ⟨⟨-122239, 15⟩, ⟨-433449, 17⟩⟩,
  ⟨⟨-433445, 17⟩, ⟨-385393, 17⟩⟩,
  ⟨⟨-385389, 17⟩, ⟨-171785, 16⟩⟩,
  ⟨⟨-343567, 17⟩, ⟨-19187, 13⟩⟩,
  ⟨⟨-306989, 17⟩, ⟨-68715, 15⟩⟩,
  ⟨⟨-274857, 17⟩, ⟨-246511, 17⟩⟩,
  ⟨⟨-246509, 17⟩, ⟨-55351, 15⟩⟩,
  ⟨⟨-110701, 16⟩, ⟨-398179, 18⟩⟩,
  ⟨⟨-398175, 18⟩, ⟨-89595, 16⟩⟩,
  ⟨⟨-358377, 18⟩, ⟨-322783, 18⟩⟩,
  ⟨⟨-80695, 16⟩, ⟨-290857, 18⟩⟩,
  ⟨⟨-145427, 17⟩, ⟨-262145, 18⟩⟩,
  ⟨⟨-524285, 19⟩, ⟨-472539, 19⟩⟩,
  ⟨⟨-472535, 19⟩, ⟨-425797, 19⟩⟩,
  ⟨⟨-425793, 19⟩, ⟨-23969, 15⟩⟩,
  ⟨⟨-383501, 19⟩, ⟨-86293, 17⟩⟩,
  ⟨⟨-345169, 19⟩, ⟨-310383, 19⟩⟩,
  ⟨⟨-77595, 17⟩, ⟨-69693, 17⟩⟩,
  ⟨⟨-278769, 19⟩, ⟨-500039, 20⟩⟩,
  ⟨⟨-500035, 20⟩, ⟨-447697, 20⟩⟩,
  ⟨⟨-447693, 20⟩, ⟨-400037, 20⟩⟩,
  ⟨⟨-400033, 20⟩, ⟨-356625, 20⟩⟩,
  ⟨⟨-178311, 19⟩, ⟨-158543, 19⟩⟩,
  ⟨⟨-158541, 19⟩, ⟨-140543, 19⟩⟩,
  ⟨⟨-281083, 20⟩, ⟨-496661, 21⟩⟩,
  ⟨⟨-31041, 17⟩, ⟨-109279, 19⟩⟩,
  ⟨⟨-54639, 18⟩, ⟨-191531, 20⟩⟩,
  ⟨⟨-191529, 20⟩, ⟨-334079, 21⟩⟩,
  ⟨⟨-334075, 21⟩, ⟨-144897, 20⟩⟩,
  ⟨⟨-289791, 21⟩, ⟨-499721, 22⟩⟩,
  ⟨⟨-124929, 20⟩, ⟨-53493, 19⟩⟩,
  ⟨⟨-213969, 21⟩, ⟨-181843, 21⟩⟩,
  ⟨⟨-181841, 21⟩, ⟨-306431, 22⟩⟩,
  ⟨⟨-306427, 22⟩, ⟨-15981, 18⟩⟩,
  ⟨⟨-255693, 22⟩, ⟨-211029, 22⟩⟩,
  ⟨⟨-105513, 21⟩, ⟨-172005, 22⟩⟩,
  ⟨⟨-344005, 23⟩, ⟨-276429, 23⟩⟩,
  ⟨⟨-34553, 20⟩, ⟨-437071, 24⟩⟩,
  ⟨⟨-54633, 21⟩, ⟨-10597, 19⟩⟩,
  ⟨⟨-169549, 23⟩, ⟨-257435, 24⟩⟩,
  ⟨⟨-514861, 25⟩, ⟨-381091, 25⟩⟩,
  ⟨⟨-381083, 25⟩, ⟨-273795, 25⟩⟩,
  ⟨⟨-273789, 25⟩, ⟨-379773, 26⟩⟩,
  ⟨⟨-94941, 24⟩, ⟨-252511, 26⟩⟩,
  ⟨⟨-505009, 27⟩, ⟨-79777, 25⟩⟩,
  ⟨⟨-159549, 26⟩, ⟨-23679, 24⟩⟩,
  ⟨⟨-94713, 26⟩, ⟨-208155, 28⟩⟩,
  ⟨⟨-416295, 29⟩, ⟨-103717, 28⟩⟩,
  ⟨⟨-103713, 28⟩, ⟨-364593, 31⟩⟩,
  ⟨⟨-364577, 31⟩, ⟨-135775, 31⟩⟩,
  ⟨⟨-16971, 28⟩, ⟨-80837, 32⟩⟩,
  ⟨⟨-323329, 34⟩, ⟨-140687, 35⟩⟩,
  ⟨⟨-70339, 34⟩, ⟨-154821, 38⟩⟩,
  ⟨⟨-77405, 37⟩, ⟨-167781, 42⟩⟩,
  ⟨⟨-335537, 43⟩, ⟨-446263, 49⟩⟩,
  ⟨⟨-111557, 47⟩, ⟨-520603, 58⟩⟩,
  ⟨⟨-520559, 58⟩, ⟨-264629, 73⟩⟩,
  ⟨⟨-66151, 71⟩, ⟨-262165, 112⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private def eulerianCoefficients : List ℤ := [
  0x1, 0x3fffffffffffffffffffffa1, 0x1fb38f8da9566feb249c9bba698db11af91f2a,
  0xffffffff43c5dba6e28e803bd69e235d2d46b46fd91cbaa, 0x4cb45f565df42fb2cdf971e64f81e0a96d9fb5291947e0e52141a0b, 0x7ece21bfb5e741cef4c7b825400966e122930a8f9c3eeb9f8b68c0f32f7ab,
  0xed6b5164795f7ba63ece7218b75c5d1fe226393c78264b75aaf43e6c22f0c85964, 0x3ffa7e49fa0309a12e3a2a6846787f7be3f0ec677ef7f7083dbbc602b1111218555ff64, 0x3eb7ec68cacaab11ce5674301f22df7ae2c3b5d26ee6909c2469bcbef7823084a68160e5191,
  0x1315cd38dd4dffa50c4f5fd7e88c458c4d7480d8f153a867e63685090472893eb9f982d93f319b1, 0x23f95e1b697cb3416269fa4204eb4ba6a990f2eefbd371047862c28cc4ea36f807cf7d6c502cbbf566, 0x1edca26d676032872b610840e4513ad1978fa9f5e152655b8219e44d33f2266e8e8d0f54554d3aaab8fe6,
  0xd9ba8305a892a445cd65b91e8ae788437b0804d1ac70bd7c8b09441031b2a274e9e06f9ee9b590ea038ae43, 0x362c2057c43c4515aba8f2c8a4d31e6d01703c2730835b9c4ff2af0da829e25c00cbbd3373199b3972986d2063, 0x82e92840ffc5a123f33ed9d814aa680342a7717f00be43090f1b0644a46bda63304cd4b43a5d35d3fa07fea9f358,
  0xcb877fc42e960c7c221550a2f74e27f6d1297d8217f6ce5ed317984eed3ee7151ee0bfd7c4448860b2b733098a4358, 0xd55bcae9cb14fcd7300e4748f26ee27b0981acea604692da4deed003ed1970cab686edd00c5b0b2a7e2a3b43200ad40f, 0x9cb5d6d0f682f667b022ccb907aa6a774a9f0e11d55d3638981ce7268e5ae2d38f0cb56a7ae5c97dc3d701fd572a57216f,
  0x53408067c617a34e195a8106de711309e45b8bd86843486348da72086ed6e80b48059ab7291002d5e66a5b85fdcabdbb5e1e, 0x20d9f82da26f254ce81b582e6c92f023e07e7764e6238014719832d32181858671f71f74b9033f00dc7eada95c56cfb471c99e, 0x9d90ae9fa91362c83ae5166527e55987a88038a5d61eb1a2f69427fb22c38ccb87a91530bc6347ea416f54eccfa0c0cb7930415,
  0x24935ed89b1eb1cae29778118e8c5319889e0487ca3335749f6a778d637a410363973af9fd1186ecda8250297c9d4e504ce046375, 0x6af067900a40ae649ca64bd0fec2fdbdb73225b92f4da7904eeed3db228d21aa40aba361f097b4f4435c159229c5cdc191f0588e94, 0xf9a969c8021474721ba417c86e279897c1a1eecaeeb218b6c8bc7eefc25fa94a935fa6e4701d7bd929e93a629f2788504bd9a7e1094,
  0x1d735d685e3f015f8b626ab0a6d5c25fed46c05f804bb3ba561389a90d212e6ddec28a002c4d1e11e94d11a48da64ef6bd9a497a08d57, 0x2d6d1b72d3711cb77bc2b9ef5e9e608b0eadd23da63e8ddc50184ae46ce45dfa677eef76bc12a47767fba8dd5408ccc547c475c0322d37, 0x39cf342f64feba00390b7409e05ee266b9e884e97e3a38200ddfb19043b1b1b5b44fd792fa60950cf34d3fa70f4377cf030510a26d636b2,
  0x3d358576b269b68f09e8f560a7262add3b6e75bde1c5e95a5c175a5e042d560f27b638f0a7177028dd6c211f486b03c21b5b50d58c941832, 0x3652bdb602dc2efac14c43455f453cd0fd7bbb93f9d901b319efd13044ff5614fe00d9b395875387f01655311cfae0d2c604be05023f0dd65, 0x28addda80ecabddd9d62c2612680f4cfe02965d6f0012b7c51b79737ca14862fd55b8d0b299e89d1e2dcb572e3ee4428b6166c9cda8685d345,
  0x19da92e73fa0356a69adbd3a820cd90f4a577212327d7f4b0a10da33ba2b81c939b774d4648cd8b3345d777ad4ec01739f66e72000b1bd96420, 0xe04d7319b2e8d76e5f6eb2cd6af477c6b95662a8078d48bcbe9395127d3e6c6a91900454cfa79c0b9805c5171e694334ea187a4318d246f4420, 0x6840b42e5f67631d32e82733755039acbd070968ba6038dbc7019afd3d1cde0972e154eb34c9ba9ba4b24924b21e9297d321adab2976be2220ea,
  0x29b5143671a7098ea6978d69dddaba9f486a22c3b6428f6e7b26d2cefdab0c84a63ae6f3cede35bac58a468614c256088597a87f82e643ad0cd2a, 0xe6a4cda65e41dcfd39c4de74f7375d6c36890de1c72e292385fdf1fd83bf28cddeca529ee829511e9cafb751299fcafbb21953fd8e9f42423d044, 0x4519574e54c0b5ab111b0965b2a5274e7783bb1ba313092fc9805946c86c7ab77f4f862a55c9fa01eb74e9773eb6de3deda266842dcbec33135d44,
  0x11ff386a0238364e4e4b607ca334a84ca0e2d0386186eab37ed256826a90f07598c364c216c79ee1583d54fab6ddc824d6ba1e4374fe1a3a261e14e, 0x415e8f82d4d6652f9b358f613c61c1182de50a6ca02bc5237c39a65c78b1791999b5cd566f17a590048cc0733fef53b6fd220015c294550a83c798e, 0xcf6e65b68d7f0937a223cd56fd54dd3dc933b9f7d22ddf2107d25fa3b4d2538a4072041a02d7a242e0ef03c1941251df89f79eb8bac4b3e4820ba08,
  0x240325898454faa102f2b3e18d71544d57eb3c586c5a1382966b039e38e0c48a89ef7acd3b0fb48c81affa2d2aa8a76e1e9b12f8b73dbbb0743ef608, 0x57b86c6b1745e978c62e317c9e93df0a3720d106e11946a5c135723b31c0611ebd5a293419e2bfe0f3c4590ebb7aa02155ec9bee141e8590687fd06a, 0xbba6be11c05aacc74eb15f14e59523debb1d54d121585875ec64ee675ac56e04fc38bd5dbbe5928bce3e14ae6c8d38754236a9dbd5c286453bffbdaa,
  0x160faa8688cf4f5814ea2a954415c5960cb41843dbb8e8a577626c9b2d191fdf5faee477f48b9305a5965691f070c86f544e4c706185e553de77de15c, 0x24870aaf802e0a4d9d2ece7dc9a8454b7c1af0f7b875c8e2502e1910f75ba2078930c701a9cdbb48acf745ea953cc596df5f297085a0d79ed39010a5c, 0x35477bcc2f6dd67fff8053a18aaabf908cb859d9351d5edcbe4419c28f31e2acc5208232d0dd7cdd60818173803b25afb608b810a83e433f9a680821e,
  0x448097dbf621d8f3deea2ef25ab630b6749748f930d132f2529ecf493677a73c2217a72fdbfefb9e954d09361e8f083d668f707d63e02b2bf5b3d935e, 0x4daab652d21f98a87f51859edd0f011c0f1e6c9b265a0ddf5c6b1bb65bf67f43c684c5ab00e2e129bd414a8d38a0f56d905a9f29b4b3e3d086cee7910, 0x4daab652d21f98a87f51859edd0f011c0f1e6c9b265a0ddf5c6b1bb65bf67f43c684c5ab00e2e129bd414a8d38a0f56d905a9f29b4b3e3d086cee7910,
  0x448097dbf621d8f3deea2ef25ab630b6749748f930d132f2529ecf493677a73c2217a72fdbfefb9e954d09361e8f083d668f707d63e02b2bf5b3d935e, 0x35477bcc2f6dd67fff8053a18aaabf908cb859d9351d5edcbe4419c28f31e2acc5208232d0dd7cdd60818173803b25afb608b810a83e433f9a680821e, 0x24870aaf802e0a4d9d2ece7dc9a8454b7c1af0f7b875c8e2502e1910f75ba2078930c701a9cdbb48acf745ea953cc596df5f297085a0d79ed39010a5c,
  0x160faa8688cf4f5814ea2a954415c5960cb41843dbb8e8a577626c9b2d191fdf5faee477f48b9305a5965691f070c86f544e4c706185e553de77de15c, 0xbba6be11c05aacc74eb15f14e59523debb1d54d121585875ec64ee675ac56e04fc38bd5dbbe5928bce3e14ae6c8d38754236a9dbd5c286453bffbdaa, 0x57b86c6b1745e978c62e317c9e93df0a3720d106e11946a5c135723b31c0611ebd5a293419e2bfe0f3c4590ebb7aa02155ec9bee141e8590687fd06a,
  0x240325898454faa102f2b3e18d71544d57eb3c586c5a1382966b039e38e0c48a89ef7acd3b0fb48c81affa2d2aa8a76e1e9b12f8b73dbbb0743ef608, 0xcf6e65b68d7f0937a223cd56fd54dd3dc933b9f7d22ddf2107d25fa3b4d2538a4072041a02d7a242e0ef03c1941251df89f79eb8bac4b3e4820ba08, 0x415e8f82d4d6652f9b358f613c61c1182de50a6ca02bc5237c39a65c78b1791999b5cd566f17a590048cc0733fef53b6fd220015c294550a83c798e,
  0x11ff386a0238364e4e4b607ca334a84ca0e2d0386186eab37ed256826a90f07598c364c216c79ee1583d54fab6ddc824d6ba1e4374fe1a3a261e14e, 0x4519574e54c0b5ab111b0965b2a5274e7783bb1ba313092fc9805946c86c7ab77f4f862a55c9fa01eb74e9773eb6de3deda266842dcbec33135d44, 0xe6a4cda65e41dcfd39c4de74f7375d6c36890de1c72e292385fdf1fd83bf28cddeca529ee829511e9cafb751299fcafbb21953fd8e9f42423d044,
  0x29b5143671a7098ea6978d69dddaba9f486a22c3b6428f6e7b26d2cefdab0c84a63ae6f3cede35bac58a468614c256088597a87f82e643ad0cd2a, 0x6840b42e5f67631d32e82733755039acbd070968ba6038dbc7019afd3d1cde0972e154eb34c9ba9ba4b24924b21e9297d321adab2976be2220ea, 0xe04d7319b2e8d76e5f6eb2cd6af477c6b95662a8078d48bcbe9395127d3e6c6a91900454cfa79c0b9805c5171e694334ea187a4318d246f4420,
  0x19da92e73fa0356a69adbd3a820cd90f4a577212327d7f4b0a10da33ba2b81c939b774d4648cd8b3345d777ad4ec01739f66e72000b1bd96420, 0x28addda80ecabddd9d62c2612680f4cfe02965d6f0012b7c51b79737ca14862fd55b8d0b299e89d1e2dcb572e3ee4428b6166c9cda8685d345, 0x3652bdb602dc2efac14c43455f453cd0fd7bbb93f9d901b319efd13044ff5614fe00d9b395875387f01655311cfae0d2c604be05023f0dd65,
  0x3d358576b269b68f09e8f560a7262add3b6e75bde1c5e95a5c175a5e042d560f27b638f0a7177028dd6c211f486b03c21b5b50d58c941832, 0x39cf342f64feba00390b7409e05ee266b9e884e97e3a38200ddfb19043b1b1b5b44fd792fa60950cf34d3fa70f4377cf030510a26d636b2, 0x2d6d1b72d3711cb77bc2b9ef5e9e608b0eadd23da63e8ddc50184ae46ce45dfa677eef76bc12a47767fba8dd5408ccc547c475c0322d37,
  0x1d735d685e3f015f8b626ab0a6d5c25fed46c05f804bb3ba561389a90d212e6ddec28a002c4d1e11e94d11a48da64ef6bd9a497a08d57, 0xf9a969c8021474721ba417c86e279897c1a1eecaeeb218b6c8bc7eefc25fa94a935fa6e4701d7bd929e93a629f2788504bd9a7e1094, 0x6af067900a40ae649ca64bd0fec2fdbdb73225b92f4da7904eeed3db228d21aa40aba361f097b4f4435c159229c5cdc191f0588e94,
  0x24935ed89b1eb1cae29778118e8c5319889e0487ca3335749f6a778d637a410363973af9fd1186ecda8250297c9d4e504ce046375, 0x9d90ae9fa91362c83ae5166527e55987a88038a5d61eb1a2f69427fb22c38ccb87a91530bc6347ea416f54eccfa0c0cb7930415, 0x20d9f82da26f254ce81b582e6c92f023e07e7764e6238014719832d32181858671f71f74b9033f00dc7eada95c56cfb471c99e,
  0x53408067c617a34e195a8106de711309e45b8bd86843486348da72086ed6e80b48059ab7291002d5e66a5b85fdcabdbb5e1e, 0x9cb5d6d0f682f667b022ccb907aa6a774a9f0e11d55d3638981ce7268e5ae2d38f0cb56a7ae5c97dc3d701fd572a57216f, 0xd55bcae9cb14fcd7300e4748f26ee27b0981acea604692da4deed003ed1970cab686edd00c5b0b2a7e2a3b43200ad40f,
  0xcb877fc42e960c7c221550a2f74e27f6d1297d8217f6ce5ed317984eed3ee7151ee0bfd7c4448860b2b733098a4358, 0x82e92840ffc5a123f33ed9d814aa680342a7717f00be43090f1b0644a46bda63304cd4b43a5d35d3fa07fea9f358, 0x362c2057c43c4515aba8f2c8a4d31e6d01703c2730835b9c4ff2af0da829e25c00cbbd3373199b3972986d2063,
  0xd9ba8305a892a445cd65b91e8ae788437b0804d1ac70bd7c8b09441031b2a274e9e06f9ee9b590ea038ae43, 0x1edca26d676032872b610840e4513ad1978fa9f5e152655b8219e44d33f2266e8e8d0f54554d3aaab8fe6, 0x23f95e1b697cb3416269fa4204eb4ba6a990f2eefbd371047862c28cc4ea36f807cf7d6c502cbbf566,
  0x1315cd38dd4dffa50c4f5fd7e88c458c4d7480d8f153a867e63685090472893eb9f982d93f319b1, 0x3eb7ec68cacaab11ce5674301f22df7ae2c3b5d26ee6909c2469bcbef7823084a68160e5191, 0x3ffa7e49fa0309a12e3a2a6846787f7be3f0ec677ef7f7083dbbc602b1111218555ff64,
  0xed6b5164795f7ba63ece7218b75c5d1fe226393c78264b75aaf43e6c22f0c85964, 0x7ece21bfb5e741cef4c7b825400966e122930a8f9c3eeb9f8b68c0f32f7ab, 0x4cb45f565df42fb2cdf971e64f81e0a96d9fb5291947e0e52141a0b,
  0xffffffff43c5dba6e28e803bd69e235d2d46b46fd91cbaa, 0x1fb38f8da9566feb249c9bba698db11af91f2a, 0x3fffffffffffffffffffffa1,
  0x1]

private theorem eulerianCoefficients_eq : descentCoeffs 94 = eulerianCoefficients := by
  decide +kernel

private theorem upper : upperOK (descentCoeffs 94) first gaps = true := by
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

private theorem lower (i : Fin (lastRepresentative 95 - 2)) :
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

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 95) :
    StrictNegativeInterlacing (originalQuotient 95 k) (eulerian 94) 92 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N095
