import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentPackedData.C127L104.N101

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N101

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L104.N101 LongCycleBounds.DescentNecklace.Packed.C127L104.N101.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L104.N101 LongCycleBounds.DescentNecklace.Packed.C127L104.N101.rows

private theorem actual : RepresentativeChecks 101 previousNodes rows :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L104.N101 LongCycleBounds.DescentNecklace.Packed.C127L104.N101.dataChecks

private def first : LongCycleFinite.Dyadic := ⟨-1267650600228229401496703205376, 0⟩

private def gaps : List Window := [
  ⟨⟨-1267609496750362504104763195392, 0⟩, ⟨-442447877063573504, 0⟩⟩,
  ⟨⟨-406417980532981760, 0⟩, ⟨-3113356361728, 0⟩⟩,
  ⟨⟨-3097711607808, 0⟩, ⟨-4857298944, 0⟩⟩,
  ⟨⟨-4715200512, 0⟩, ⟨-79060480, 0⟩⟩,
  ⟨⟨-78828288, 0⟩, ⟨-4530672, 0⟩⟩,
  ⟨⟨-4526896, 0⟩, ⟨-552244, 0⟩⟩,
  ⟨⟨-552036, 0⟩, ⟨-438261, 2⟩⟩,
  ⟨⟨-219083, 1⟩, ⟨-242749, 3⟩⟩,
  ⟨⟨-121357, 2⟩, ⟨-341249, 5⟩⟩,
  ⟨⟨-170607, 4⟩, ⟨-285999, 6⟩⟩,
  ⟨⟨-35747, 3⟩, ⟨-273963, 7⟩⟩,
  ⟨⟨-136973, 6⟩, ⟨-145589, 7⟩⟩,
  ⟨⟨-145581, 7⟩, ⟨-84013, 7⟩⟩,
  ⟨⟨-336037, 9⟩, ⟨-414467, 10⟩⟩,
  ⟨⟨-414451, 10⟩, ⟨-134919, 9⟩⟩,
  ⟨⟨-67457, 8⟩, ⟨-367489, 11⟩⟩,
  ⟨⟨-183739, 10⟩, ⟨-519641, 12⟩⟩,
  ⟨⟨-129907, 10⟩, ⟨-189623, 11⟩⟩,
  ⟨⟨-379237, 12⟩, ⟨-284369, 12⟩⟩,
  ⟨⟨-284363, 12⟩, ⟨-218235, 12⟩⟩,
  ⟨⟨-218231, 12⟩, ⟨-341743, 13⟩⟩,
  ⟨⟨-341737, 13⟩, ⟨-272281, 13⟩⟩,
  ⟨⟨-68069, 11⟩, ⟨-440547, 14⟩⟩,
  ⟨⟨-110135, 12⟩, ⟨-361197, 14⟩⟩,
  ⟨⟨-45149, 11⟩, ⟨-299657, 14⟩⟩,
  ⟨⟨-299653, 14⟩, ⟨-502425, 15⟩⟩,
  ⟨⟨-251209, 14⟩, ⟨-212567, 14⟩⟩,
  ⟨⟨-425129, 15⟩, ⟨-362719, 15⟩⟩,
  ⟨⟨-181357, 14⟩, ⟨-311761, 15⟩⟩,
  ⟨⟨-311757, 15⟩, ⟨-134869, 14⟩⟩,
  ⟨⟨-269735, 15⟩, ⟨-469533, 16⟩⟩,
  ⟨⟨-58691, 13⟩, ⟨-410831, 16⟩⟩,
  ⟨⟨-205413, 15⟩, ⟨-361191, 16⟩⟩,
  ⟨⟨-361187, 16⟩, ⟨-318909, 16⟩⟩,
  ⟨⟨-318905, 16⟩, ⟨-282661, 16⟩⟩,
  ⟨⟨-141329, 15⟩, ⟨-125699, 15⟩⟩,
  ⟨⟨-502791, 17⟩, ⟨-112141, 15⟩⟩,
  ⟨⟨-28035, 13⟩, ⟨-200641, 16⟩⟩,
  ⟨⟨-401279, 17⟩, ⟨-359863, 17⟩⟩,
  ⟨⟨-359859, 17⟩, ⟨-323415, 17⟩⟩,
  ⟨⟨-80853, 15⟩, ⟨-291211, 17⟩⟩,
  ⟨⟨-36401, 14⟩, ⟨-65661, 15⟩⟩,
  ⟨⟨-131321, 16⟩, ⟨-474429, 18⟩⟩,
  ⟨⟨-474425, 18⟩, ⟨-214503, 17⟩⟩,
  ⟨⟨-214501, 17⟩, ⟨-388309, 18⟩⟩,
  ⟨⟨-194153, 17⟩, ⟨-175873, 17⟩⟩,
  ⟨⟨-351743, 18⟩, ⟨-318807, 18⟩⟩,
  ⟨⟨-79701, 16⟩, ⟨-36133, 15⟩⟩,
  ⟨⟨-144531, 17⟩, ⟨-262145, 18⟩⟩,
  ⟨⟨-524285, 19⟩, ⟨-475465, 19⟩⟩,
  ⟨⟨-475461, 19⟩, ⟨-215553, 18⟩⟩,
  ⟨⟨-431103, 19⟩, ⟨-390737, 19⟩⟩,
  ⟨⟨-195367, 18⟩, ⟨-44243, 16⟩⟩,
  ⟨⟨-353941, 19⟩, ⟨-160185, 18⟩⟩,
  ⟨⟨-320367, 19⟩, ⟨-289695, 19⟩⟩,
  ⟨⟨-72423, 17⟩, ⟨-523295, 20⟩⟩,
  ⟨⟨-261645, 19⟩, ⟨-471961, 20⟩⟩,
  ⟨⟨-471957, 20⟩, ⟨-424965, 20⟩⟩,
  ⟨⟨-424961, 20⟩, ⟨-190961, 19⟩⟩,
  ⟨⟨-381919, 20⟩, ⟨-171251, 19⟩⟩,
  ⟨⟨-342499, 20⟩, ⟨-9575, 15⟩⟩,
  ⟨⟨-306397, 20⟩, ⟨-273353, 20⟩⟩,
  ⟨⟨-136675, 19⟩, ⟨-486237, 21⟩⟩,
  ⟨⟨-486233, 21⟩, ⟨-107743, 19⟩⟩,
  ⟨⟨-430967, 21⟩, ⟨-47565, 18⟩⟩,
  ⟨⟨-95129, 19⟩, ⟨-167271, 20⟩⟩,
  ⟨⟨-167269, 20⟩, ⟨-146359, 20⟩⟩,
  ⟨⟨-292715, 21⟩, ⟨-127383, 20⟩⟩,
  ⟨⟨-509527, 22⟩, ⟨-220427, 21⟩⟩,
  ⟨⟨-440849, 22⟩, ⟨-378917, 22⟩⟩,
  ⟨⟨-378913, 22⟩, ⟨-323289, 22⟩⟩,
  ⟨⟨-323285, 22⟩, ⟨-273555, 22⟩⟩,
  ⟨⟨-273551, 22⟩, ⟨-458661, 23⟩⟩,
  ⟨⟨-458655, 23⟩, ⟨-380517, 23⟩⟩,
  ⟨⟨-11891, 18⟩, ⟨-311979, 23⟩⟩,
  ⟨⟨-155987, 22⟩, ⟨-504773, 24⟩⟩,
  ⟨⟨-252383, 23⟩, ⟨-402179, 24⟩⟩,
  ⟨⟨-402173, 24⟩, ⟨-314895, 24⟩⟩,
  ⟨⟨-314889, 24⟩, ⟨-241661, 24⟩⟩,
  ⟨⟨-483313, 25⟩, ⟨-362407, 25⟩⟩,
  ⟨⟨-11325, 20⟩, ⟨-264493, 25⟩⟩,
  ⟨⟨-264487, 25⟩, ⟨-187003, 25⟩⟩,
  ⟨⟨-186999, 25⟩, ⟨-127339, 25⟩⟩,
  ⟨⟨-509343, 27⟩, ⟨-165809, 26⟩⟩,
  ⟨⟨-331609, 27⟩, ⟨-51125, 25⟩⟩,
  ⟨⟨-102247, 26⟩, ⟨-118009, 27⟩⟩,
  ⟨⟨-472021, 29⟩, ⟨-501707, 30⟩⟩,
  ⟨⟨-501689, 30⟩, ⟨-240305, 30⟩⟩,
  ⟨⟨-240295, 30⟩, ⟨-100695, 30⟩⟩,
  ⟨⟨-402761, 32⟩, ⟨-283103, 33⟩⟩,
  ⟨⟨-283089, 33⟩, ⟨-78409, 33⟩⟩,
  ⟨⟨-156809, 34⟩, ⟨-62237, 35⟩⟩,
  ⟨⟨-62233, 35⟩, ⟨-121371, 39⟩⟩,
  ⟨⟨-242725, 40⟩, ⟨-445771, 45⟩⟩,
  ⟨⟨-222869, 44⟩, ⟨-465995, 51⟩⟩,
  ⟨⟨-232979, 50⟩, ⟨-185181, 59⟩⟩,
  ⟨⟨-370331, 60⟩, ⟨-371715, 77⟩⟩,
  ⟨⟨-11615, 72⟩, ⟨-262165, 118⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private def eulerianCoefficients : List ℤ := [
  0x1, 0xfffffffffffffffffffffff9b, 0x5a4653ca673762065b41f775d6947d55cf38278b,
  0xffffffffdc6240f1254725118dfef95e82576a8d253edda391, 0x1249ad1f44c37ceb7a7479d3398da1034c83c2d9c32b7db92ea42f81eb8, 0x5a464c9355e8d0453af92db6539bfc2f60b02addde2122ce4773c72e8968d73a8,
  0x1aa38f2773f744f1df197dc34131a9efc9938fa747f5841ea724a3f3f3bb6e02c95b388, 0xfff57d716d028f4f979f299cf0895e31ac8d118a1b0e8db047d8c812ae9f37403d138f14fd8, 0x1fcf365d16b53612be1982a887ad66a7e03b6b590fd029eff23b9837c462e2c01bb827b2724a0444,
  0x123d1f233ac2e8425cc2ba8f1e4927dffdc67082b852e340b6422ea2b612e0fdff0a8b8b7ffcee57fb6c, 0x3d13c717363828be902fc053de774dd6af801cfa7e85828c433be7fea29d11fe77a1d60eb72931ebf77530c, 0x58c3579ff4108768c3ade951e946cd5a123ca0be101a0cc750d13092b99f5237c26665f411b9372328afcf49a4,
  0x3fc5ecf1e738f736084556d54c70bcb4fc4a39333b487af1a036bc02b90f531bb8f5cb87dd75a3724d18fa39950e8, 0x190a1d08dfbe7e22071bd31d43545d412e0968f73efdb41c315376bb932bc15909ec8ca854d4b6004df0ba873e0fbdb8, 0x5cfcaf0e60ef9839604226636d2423eeb83266a6ace26974bec86673d0700671449387bef03b863459fb29c77b727e5118,
  0xd94da286caba7df5c132c3a0fbf541bfaadac597b38a43794a76b26c346e7738bb5b8c8a6ef514dad09fe4a8098ff64a0288, 0x1501f282b0951b04f0c901ebfd884e738f87fe026ba5ca5baf776c98158e22dd23baff83d832ef18f2ec0f03b038931b145fc32, 0x166a5d63842ef8ed2f9d080d107e1be2152b61bc938cf8beef63d558a898a632a468844311158ccbe0b01bcd2c0391ac539cb0586,
  0x1112deaad2e4a2ba61f10cb360acc06013c5d781f96790609d1d6f4bf50a1fa342dc5fd6cf874021672e6ba7c355d3ae22f4452fac6, 0x98da994f24aa28074365cf947377b593137221961ed70dc45ea879aa57cdfbc1cb66e14cd1083bf9fb66f1af9878e8d9b112880100f2, 0x405e022d596d5fde08fde942967003667c6d32a47dd0e2080c7ff11886b4dbf7b656037a03851490aed805646d5cd536f4c8a01858b828,
  0x14d3023ca3e8abe5208aefcae2bb4c0c0101a850fb3dfe7dd830dcf596b153593361facba97528d856366db1d65b3c22d9a45ce374472bf8, 0x544b92143639ba9b8da57ea5c4d3a714521188114df56ef4015f657dd011d2e919964b6434c14eaa938083454f13f6f0efc3b5c93aec32318, 0x10ef48d8b702bc87efbe8cd4c3171dabce02cf20beae39d4e22c3cf78611cd74be8e9fbbb125ac8864abc039254e392b2396e25e603616ee808,
  0x2bce1367677ed692394156028e73622793ae1ac89aed2d1ecd00e99ddae3c5fd1d5d012ea773181ac61fd9dba861cdfb9e8c85539665ba29fa94, 0x5c4126a0407ec58d94582a77c5bb614e6d4c3595bf6cb9f0a2b6463f01b657751546d8eca3b82007c44d05ba7e46e20201d742d7d12f50e19a75c, 0x9fd17c48d2116a586d4299e5294e92b3e4da71b1658594be96debe91e9d83d2e6943e35f745c858ee337e111859af1dafa0c7db1401494f1f8fb3c,
  0xe5d093600a473ffc3c96364882c02ea0582dc5591fca9175415f1faf35cfb02f38c2ab89755ec9780bf6e2f4c2cfeaef36673f53ae761bb8e9b65b4, 0x114864d921ed99da3c66df35716bbce7076b7a6c21337c6633e0c08fc86cb235d7cb761745356fbb57ae2dc27c8ca943ae966d7ab666e24764c34d7b8, 0x1186a55a41a516dec735e5331e330514ee6c44db6933bfe361d205262ae6fc7b67228db7ede68da5a6e6416daff39e57f850c1886e3e2763655a58df28,
  0xf1300e6c0b8b7de1107cf6c5e446cd6ce76bc82fe9be2e1329486ebd62130e27d75dd7b346707e2e346e6e264beef20a0513491af303d8206fa1745bc8, 0xb0f5b83a42e6e8fcb54d322bdb7a5419fc14ae3b1eb4b56979ae095d46e98173a052e9d933633d889f7ca626f96b103e99aa5a16c31c0f2ccc76a2f0618, 0x6f529b7a77cee5177014d92dc8e050f6d5e54eebd468a9726bf56260e6a6a221c04001410c16df396f8f5c234c4994ce9bad5848556811c2db7d1d55a6bf,
  0x3c527c29efb9f04842518aced3c077c96dc88e2fb68a0bb2331e89a88a0a2ae7a02cc642b9c65c31a0d860d73a36e1d851dc072e06de391d9a562b570fd65, 0x1c457a99463a1c736320ab5dc585bb8e59247bec49c436b2b41ded1cb4157035bd4192ec90bd0d073beb30d95e55b62f6101ef4e38957f8141493c4873cb15, 0xb80b8156715051b210923a07ea7af037276677e40dbdcbf55edcfc2057059ad27f413cf4613fbdffdc454fedd5baedaec3a2d0648be911d285ac12381b028f,
  0x41398b3521555405bc59f0a53e42f802e638065278f9ef1b3bb806dc095dd4bb5741ca5bd7cc1308657e530c3a8308d6b44fb0c98463c4c53a93fec491fe6b0, 0x1431c2e034ace638c7ac37670b8ee2e0306c2ba614975b1921ace10b18bb7b914c3735fc8f63d2a564a4fe9631c4d263bb1e270c56bb509e67f0b267415d4310, 0x57a198639fec758954512efe6bfb6f078e738dda7a90917c47c3645b7a97f48de72f6dc36d446eda828885ebd7280b6cc1fcf03fb9d41458a35d26c5993151d0,
  0x14de6170d7e14854fc5b22abbc1e037ef7531652dd9948f31c73b5e119bd57bf66371bbc1a164072567297ad737170ed05612e0ac69f27b3b3382868698e801f0, 0x45f7db944c09348bf3ac5fd2ee7aec3b22419121b63e5bff85535a4bc1b6dda5dc6fb6ea8b0340bfc8feb01215837d749ca11aed24ee38615a53081a4dd086308, 0xcecf73e1b5a6743b39a03d4089fab9a67ea35d4973574b9ac41cb09ebaec96b6f74ba20db654ec6952970a1816e39f239acc30bdb904180b65a3bc20f3a190458,
  0x21bcabc5a768673182fb49f39b70b4df2d2fd2df9071f632673092bfd771641642f081f8e65440505f92e184ce1cd466066f141467f615c35a2ba0a12d5a67f298, 0x4dde8b64c81ee8eaf55274733168a1bdd09889b623588ba5dcdb6233662ebae5ae9a4152eaa098fd381839da1b66f5460e5df9463c5e38110755249963b57126c8, 0x9f22b6b93456b91c6164f04b40eb93b5c3468dc71329d36473bae2bd93cc2531334a1350eef3b1376107ba0e4ec4238ce19f01e7146c6967b71db9bd757a20dd90,
  0x1203e8a7384bbc1628912c8b5bec6b14328bd45ed07c02f398c390e86c4d94060d6ab92a57996fbcde2effea1630bc3bce1ea49f2d4268d310058274f7c9307fab0, 0x1cf25413c4b9dfdf279c0dec4a386fabef6372f84cfc117618ae33ac1901d6aba8a310fd4c1bd14654a02cf09b7e282682c7690c89b937988e1db3671192a60b070, 0x29496ae2b48be07158b56c33f5eab2b7604e950fd130540f085f7749ed6dcf7c98c1d5fd4c38f2eb4ce9463886e14ec8bdfdea9c0aa071992e7677a5b31555ef9d0,
  0x344cbd8bc76462b8a9d1abe414c1dde766f19e52b1bc90eb872a136d526c38761e817554a885cf8d7031f4f3d87f38d2d857bdbd174442c6d500a13622c3d927dfc, 0x3adbbcc52a96ec790efa809eac8ce0c7b6aae43066f4a6a03e0fc400e28ece497b21c3b8661b6c04abbedadc9d4227adab3e62ed39657fa1a782e0c765a47e22814, 0x3adbbcc52a96ec790efa809eac8ce0c7b6aae43066f4a6a03e0fc400e28ece497b21c3b8661b6c04abbedadc9d4227adab3e62ed39657fa1a782e0c765a47e22814,
  0x344cbd8bc76462b8a9d1abe414c1dde766f19e52b1bc90eb872a136d526c38761e817554a885cf8d7031f4f3d87f38d2d857bdbd174442c6d500a13622c3d927dfc, 0x29496ae2b48be07158b56c33f5eab2b7604e950fd130540f085f7749ed6dcf7c98c1d5fd4c38f2eb4ce9463886e14ec8bdfdea9c0aa071992e7677a5b31555ef9d0, 0x1cf25413c4b9dfdf279c0dec4a386fabef6372f84cfc117618ae33ac1901d6aba8a310fd4c1bd14654a02cf09b7e282682c7690c89b937988e1db3671192a60b070,
  0x1203e8a7384bbc1628912c8b5bec6b14328bd45ed07c02f398c390e86c4d94060d6ab92a57996fbcde2effea1630bc3bce1ea49f2d4268d310058274f7c9307fab0, 0x9f22b6b93456b91c6164f04b40eb93b5c3468dc71329d36473bae2bd93cc2531334a1350eef3b1376107ba0e4ec4238ce19f01e7146c6967b71db9bd757a20dd90, 0x4dde8b64c81ee8eaf55274733168a1bdd09889b623588ba5dcdb6233662ebae5ae9a4152eaa098fd381839da1b66f5460e5df9463c5e38110755249963b57126c8,
  0x21bcabc5a768673182fb49f39b70b4df2d2fd2df9071f632673092bfd771641642f081f8e65440505f92e184ce1cd466066f141467f615c35a2ba0a12d5a67f298, 0xcecf73e1b5a6743b39a03d4089fab9a67ea35d4973574b9ac41cb09ebaec96b6f74ba20db654ec6952970a1816e39f239acc30bdb904180b65a3bc20f3a190458, 0x45f7db944c09348bf3ac5fd2ee7aec3b22419121b63e5bff85535a4bc1b6dda5dc6fb6ea8b0340bfc8feb01215837d749ca11aed24ee38615a53081a4dd086308,
  0x14de6170d7e14854fc5b22abbc1e037ef7531652dd9948f31c73b5e119bd57bf66371bbc1a164072567297ad737170ed05612e0ac69f27b3b3382868698e801f0, 0x57a198639fec758954512efe6bfb6f078e738dda7a90917c47c3645b7a97f48de72f6dc36d446eda828885ebd7280b6cc1fcf03fb9d41458a35d26c5993151d0, 0x1431c2e034ace638c7ac37670b8ee2e0306c2ba614975b1921ace10b18bb7b914c3735fc8f63d2a564a4fe9631c4d263bb1e270c56bb509e67f0b267415d4310,
  0x41398b3521555405bc59f0a53e42f802e638065278f9ef1b3bb806dc095dd4bb5741ca5bd7cc1308657e530c3a8308d6b44fb0c98463c4c53a93fec491fe6b0, 0xb80b8156715051b210923a07ea7af037276677e40dbdcbf55edcfc2057059ad27f413cf4613fbdffdc454fedd5baedaec3a2d0648be911d285ac12381b028f, 0x1c457a99463a1c736320ab5dc585bb8e59247bec49c436b2b41ded1cb4157035bd4192ec90bd0d073beb30d95e55b62f6101ef4e38957f8141493c4873cb15,
  0x3c527c29efb9f04842518aced3c077c96dc88e2fb68a0bb2331e89a88a0a2ae7a02cc642b9c65c31a0d860d73a36e1d851dc072e06de391d9a562b570fd65, 0x6f529b7a77cee5177014d92dc8e050f6d5e54eebd468a9726bf56260e6a6a221c04001410c16df396f8f5c234c4994ce9bad5848556811c2db7d1d55a6bf, 0xb0f5b83a42e6e8fcb54d322bdb7a5419fc14ae3b1eb4b56979ae095d46e98173a052e9d933633d889f7ca626f96b103e99aa5a16c31c0f2ccc76a2f0618,
  0xf1300e6c0b8b7de1107cf6c5e446cd6ce76bc82fe9be2e1329486ebd62130e27d75dd7b346707e2e346e6e264beef20a0513491af303d8206fa1745bc8, 0x1186a55a41a516dec735e5331e330514ee6c44db6933bfe361d205262ae6fc7b67228db7ede68da5a6e6416daff39e57f850c1886e3e2763655a58df28, 0x114864d921ed99da3c66df35716bbce7076b7a6c21337c6633e0c08fc86cb235d7cb761745356fbb57ae2dc27c8ca943ae966d7ab666e24764c34d7b8,
  0xe5d093600a473ffc3c96364882c02ea0582dc5591fca9175415f1faf35cfb02f38c2ab89755ec9780bf6e2f4c2cfeaef36673f53ae761bb8e9b65b4, 0x9fd17c48d2116a586d4299e5294e92b3e4da71b1658594be96debe91e9d83d2e6943e35f745c858ee337e111859af1dafa0c7db1401494f1f8fb3c, 0x5c4126a0407ec58d94582a77c5bb614e6d4c3595bf6cb9f0a2b6463f01b657751546d8eca3b82007c44d05ba7e46e20201d742d7d12f50e19a75c,
  0x2bce1367677ed692394156028e73622793ae1ac89aed2d1ecd00e99ddae3c5fd1d5d012ea773181ac61fd9dba861cdfb9e8c85539665ba29fa94, 0x10ef48d8b702bc87efbe8cd4c3171dabce02cf20beae39d4e22c3cf78611cd74be8e9fbbb125ac8864abc039254e392b2396e25e603616ee808, 0x544b92143639ba9b8da57ea5c4d3a714521188114df56ef4015f657dd011d2e919964b6434c14eaa938083454f13f6f0efc3b5c93aec32318,
  0x14d3023ca3e8abe5208aefcae2bb4c0c0101a850fb3dfe7dd830dcf596b153593361facba97528d856366db1d65b3c22d9a45ce374472bf8, 0x405e022d596d5fde08fde942967003667c6d32a47dd0e2080c7ff11886b4dbf7b656037a03851490aed805646d5cd536f4c8a01858b828, 0x98da994f24aa28074365cf947377b593137221961ed70dc45ea879aa57cdfbc1cb66e14cd1083bf9fb66f1af9878e8d9b112880100f2,
  0x1112deaad2e4a2ba61f10cb360acc06013c5d781f96790609d1d6f4bf50a1fa342dc5fd6cf874021672e6ba7c355d3ae22f4452fac6, 0x166a5d63842ef8ed2f9d080d107e1be2152b61bc938cf8beef63d558a898a632a468844311158ccbe0b01bcd2c0391ac539cb0586, 0x1501f282b0951b04f0c901ebfd884e738f87fe026ba5ca5baf776c98158e22dd23baff83d832ef18f2ec0f03b038931b145fc32,
  0xd94da286caba7df5c132c3a0fbf541bfaadac597b38a43794a76b26c346e7738bb5b8c8a6ef514dad09fe4a8098ff64a0288, 0x5cfcaf0e60ef9839604226636d2423eeb83266a6ace26974bec86673d0700671449387bef03b863459fb29c77b727e5118, 0x190a1d08dfbe7e22071bd31d43545d412e0968f73efdb41c315376bb932bc15909ec8ca854d4b6004df0ba873e0fbdb8,
  0x3fc5ecf1e738f736084556d54c70bcb4fc4a39333b487af1a036bc02b90f531bb8f5cb87dd75a3724d18fa39950e8, 0x58c3579ff4108768c3ade951e946cd5a123ca0be101a0cc750d13092b99f5237c26665f411b9372328afcf49a4, 0x3d13c717363828be902fc053de774dd6af801cfa7e85828c433be7fea29d11fe77a1d60eb72931ebf77530c,
  0x123d1f233ac2e8425cc2ba8f1e4927dffdc67082b852e340b6422ea2b612e0fdff0a8b8b7ffcee57fb6c, 0x1fcf365d16b53612be1982a887ad66a7e03b6b590fd029eff23b9837c462e2c01bb827b2724a0444, 0xfff57d716d028f4f979f299cf0895e31ac8d118a1b0e8db047d8c812ae9f37403d138f14fd8,
  0x1aa38f2773f744f1df197dc34131a9efc9938fa747f5841ea724a3f3f3bb6e02c95b388, 0x5a464c9355e8d0453af92db6539bfc2f60b02addde2122ce4773c72e8968d73a8, 0x1249ad1f44c37ceb7a7479d3398da1034c83c2d9c32b7db92ea42f81eb8,
  0xffffffffdc6240f1254725118dfef95e82576a8d253edda391, 0x5a4653ca673762065b41f775d6947d55cf38278b, 0xfffffffffffffffffffffff9b,
  0x1]

private theorem eulerianCoefficients_eq : descentCoeffs 100 = eulerianCoefficients := by
  decide +kernel

private theorem upper : upperOK (descentCoeffs 100) first gaps = true := by
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

private theorem lower (i : Fin (lastRepresentative 101 - 2)) :
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

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 101) :
    StrictNegativeInterlacing (originalQuotient 101 k) (eulerian 100) 98 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N101
