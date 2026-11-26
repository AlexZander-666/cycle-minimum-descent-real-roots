import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentPackedData.C127L104.N104

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N104

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L104.N104 LongCycleBounds.DescentNecklace.Packed.C127L104.N104.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L104.N104 LongCycleBounds.DescentNecklace.Packed.C127L104.N104.rows

private theorem actual : RepresentativeChecks 104 previousNodes rows :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L104.N104 LongCycleBounds.DescentNecklace.Packed.C127L104.N104.dataChecks

private def first : LongCycleFinite.Dyadic := ⟨-10141204801825835211973625643008, 0⟩

private def gaps : List Window := [
  ⟨⟨-10140875974002900032838105563136, 0⟩, ⟨-1541312992002441216, 0⟩⟩,
  ⟨⟨-1253082615850729472, 0⟩, ⟨-7383065559040, 0⟩⟩,
  ⟨⟨-7325553262592, 0⟩, ⟨-9689595904, 0⟩⟩,
  ⟨⟨-9351757824, 0⟩, ⟨-137362432, 0⟩⟩,
  ⟨⟨-136901632, 0⟩, ⟨-7233168, 0⟩⟩,
  ⟨⟨-7226592, 0⟩, ⟨-829786, 0⟩⟩,
  ⟨⟨-829450, 0⟩, ⟨-157200, 0⟩⟩,
  ⟨⟨-157164, 0⟩, ⟨-335943, 3⟩⟩,
  ⟨⟨-83973, 1⟩, ⟨-114679, 3⟩⟩,
  ⟨⟨-458667, 5⟩, ⟨-375373, 6⟩⟩,
  ⟨⟨-375343, 6⟩, ⟨-352513, 7⟩⟩,
  ⟨⟨-352489, 7⟩, ⟨-184225, 7⟩⟩,
  ⟨⟨-184215, 7⟩, ⟨-209597, 8⟩⟩,
  ⟨⟨-52397, 6⟩, ⟨-510703, 10⟩⟩,
  ⟨⟨-127671, 8⟩, ⟨-164483, 9⟩⟩,
  ⟨⟨-164477, 9⟩, ⟨-221941, 10⟩⟩,
  ⟨⟨-443869, 11⟩, ⟨-77823, 9⟩⟩,
  ⟨⟨-311283, 11⟩, ⟨-451127, 12⟩⟩,
  ⟨⟨-112779, 10⟩, ⟨-1313, 4⟩⟩,
  ⟨⟨-336121, 12⟩, ⟨-256515, 12⟩⟩,
  ⟨⟨-128255, 11⟩, ⟨-399695, 13⟩⟩,
  ⟨⟨-49961, 10⟩, ⟨-158527, 12⟩⟩,
  ⟨⟨-39631, 10⟩, ⟨-127745, 12⟩⟩,
  ⟨⟨-127743, 12⟩, ⟨-208747, 13⟩⟩,
  ⟨⟨-417487, 14⟩, ⟨-172649, 13⟩⟩,
  ⟨⟨-345293, 14⟩, ⟨-144347, 13⟩⟩,
  ⟨⟨-144345, 13⟩, ⟨-487403, 15⟩⟩,
  ⟨⟨-487397, 15⟩, ⟨-51873, 12⟩⟩,
  ⟨⟨-414979, 15⟩, ⟨-356045, 15⟩⟩,
  ⟨⟨-356041, 15⟩, ⟨-307583, 15⟩⟩,
  ⟨⟨-307579, 15⟩, ⟨-133681, 14⟩⟩,
  ⟨⟨-267359, 15⟩, ⟨-467385, 16⟩⟩,
  ⟨⟨-116845, 14⟩, ⟨-205287, 15⟩⟩,
  ⟨⟨-205285, 15⟩, ⟨-362291, 16⟩⟩,
  ⟨⟨-362287, 16⟩, ⟨-320985, 16⟩⟩,
  ⟨⟨-320981, 16⟩, ⟨-17839, 12⟩⟩,
  ⟨⟨-71355, 14⟩, ⟨-254637, 16⟩⟩,
  ⟨⟨-254635, 16⟩, ⟨-445, 7⟩⟩,
  ⟨⟨-113919, 15⟩, ⟨-408801, 17⟩⟩,
  ⟨⟨-408797, 17⟩, ⟨-45951, 14⟩⟩,
  ⟨⟨-367605, 17⟩, ⟨-331257, 17⟩⟩,
  ⟨⟨-165627, 16⟩, ⟨-149525, 16⟩⟩,
  ⟨⟨-299047, 17⟩, ⟨-135205, 16⟩⟩,
  ⟨⟨-270407, 17⟩, ⟨-489705, 18⟩⟩,
  ⟨⟨-489701, 18⟩, ⟨-221973, 17⟩⟩,
  ⟨⟨-221971, 17⟩, ⟨-25179, 14⟩⟩,
  ⟨⟨-402861, 18⟩, ⟨-182937, 17⟩⟩,
  ⟨⟨-365871, 18⟩, ⟨-332487, 18⟩⟩,
  ⟨⟨-83121, 16⟩, ⟨-302277, 18⟩⟩,
  ⟨⟨-302275, 18⟩, ⟨-274885, 18⟩⟩,
  ⟨⟨-137441, 17⟩, ⟨-499991, 19⟩⟩,
  ⟨⟨-499987, 19⟩, ⟨-227341, 18⟩⟩,
  ⟨⟨-227339, 18⟩, ⟨-413371, 19⟩⟩,
  ⟨⟨-413367, 19⟩, ⟨-375649, 19⟩⟩,
  ⟨⟨-187823, 18⟩, ⟨-170579, 18⟩⟩,
  ⟨⟨-341155, 19⟩, ⟨-309587, 19⟩⟩,
  ⟨⟨-19349, 15⟩, ⟨-280661, 19⟩⟩,
  ⟨⟨-140329, 18⟩, ⟨-508269, 20⟩⟩,
  ⟨⟨-508265, 20⟩, ⟨-229795, 19⟩⟩,
  ⟨⟨-229793, 19⟩, ⟨-414905, 20⟩⟩,
  ⟨⟨-414901, 20⟩, ⟨-93469, 18⟩⟩,
  ⟨⟨-23367, 16⟩, ⟨-336203, 20⟩⟩,
  ⟨⟨-42025, 17⟩, ⟨-18851, 16⟩⟩,
  ⟨⟨-301613, 20⟩, ⟨-269875, 20⟩⟩,
  ⟨⟨-16867, 16⟩, ⟨-60191, 18⟩⟩,
  ⟨⟨-120381, 19⟩, ⟨-428183, 21⟩⟩,
  ⟨⟨-428179, 21⟩, ⟨-94841, 19⟩⟩,
  ⟨⟨-11855, 16⟩, ⟨-10461, 16⟩⟩,
  ⟨⟨-83687, 19⟩, ⟨-147031, 20⟩⟩,
  ⟨⟨-294059, 21⟩, ⟨-128515, 20⟩⟩,
  ⟨⟨-514055, 22⟩, ⟨-446839, 22⟩⟩,
  ⟨⟨-223417, 21⟩, ⟨-386023, 22⟩⟩,
  ⟨⟨-193009, 21⟩, ⟨-82799, 20⟩⟩,
  ⟨⟨-41399, 19⟩, ⟨-70497, 20⟩⟩,
  ⟨⟨-2203, 15⟩, ⟨-119019, 21⟩⟩,
  ⟨⟨-238035, 22⟩, ⟨-398037, 23⟩⟩,
  ⟨⟨-398031, 23⟩, ⟨-329207, 23⟩⟩,
  ⟨⟨-164601, 22⟩, ⟨-16811, 19⟩⟩,
  ⟨⟨-268971, 23⟩, ⟨-216747, 23⟩⟩,
  ⟨⟨-433487, 24⟩, ⟨-171931, 23⟩⟩,
  ⟨⟨-21491, 20⟩, ⟨-66975, 22⟩⟩,
  ⟨⟨-267895, 24⟩, ⟨-408891, 25⟩⟩,
  ⟨⟨-408883, 25⟩, ⟨-38083, 22⟩⟩,
  ⟨⟨-304657, 25⟩, ⟨-220765, 25⟩⟩,
  ⟨⟨-27595, 22⟩, ⟨-38705, 23⟩⟩,
  ⟨⟨-309633, 26⟩, ⟨-417797, 27⟩⟩,
  ⟨⟨-208893, 26⟩, ⟨-134565, 26⟩⟩,
  ⟨⟨-269123, 27⟩, ⟨-81969, 26⟩⟩,
  ⟨⟨-163933, 27⟩, ⟨-373035, 29⟩⟩,
  ⟨⟨-186511, 28⟩, ⟨-24369, 26⟩⟩,
  ⟨⟨-389889, 30⟩, ⟨-366175, 31⟩⟩,
  ⟨⟨-22885, 27⟩, ⟨-74913, 30⟩⟩,
  ⟨⟨-149819, 31⟩, ⟨-204575, 33⟩⟩,
  ⟨⟨-51141, 31⟩, ⟨-437189, 36⟩⟩,
  ⟨⟨-109291, 34⟩, ⟨-331387, 38⟩⟩,
  ⟨⟨-165683, 37⟩, ⟨-304137, 41⟩⟩,
  ⟨⟨-304115, 41⟩, ⟨-514013, 46⟩⟩,
  ⟨⟨-513975, 46⟩, ⟨-119079, 50⟩⟩,
  ⟨⟨-476279, 52⟩, ⟨-156203, 60⟩⟩,
  ⟨⟨-78095, 59⟩, ⟨-220265, 78⟩⟩,
  ⟨⟨-440489, 79⟩, ⟨-262149, 121⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private def eulerianCoefficients : List ℤ := [
  0x1, 0x7fffffffffffffffffffffff98, 0x9856ad658e2d7cd1b9ff5196da1a9380cdaea2bf7,
  0x3ffffffffc21cc98ebe3d84a02c7046dab7653413ac710e3dc30, 0x8edf989b9a373fed0e58147e15675c7fed4ef252a0a035f158a7bbcc013f, 0x4c2b531219b6774e75e02755b125bf184eb3cc085dc320f35a7b063469acc483c58,
  0x23b135949afc0b53dbf98ee62bb7b2aa1d7992b7ef17b0fe57eff1ca6e6b8e978eeb7c8f9, 0x1fff17ffbe314e794113b7a3dff3021c5d52914df8145513f71e59285f758af0b7d63ceefea580, 0x5a9a0b703a98052fdff5997ebf2fae516c65c8df50392dcc3e67aa5bc849e9ab10a930860ad7c2f0cc,
  0x474afb1bb446df3b97019bea529555a8ca3af9b4a057aa4e25f5e4d7e36355263c2cbec8887bfa11e652a0, 0x13e155cdf43b9be2afa2f8092b76725caca09ca23bf88e059d9dd92f265ea0b51950bfb73bb1ab4d7a11443bd4, 0x2594139249b14305ed2ae48ea2125b67facce25dff6644a6f0379818f10e14d7a52d3b6cac2ea938572897b4e97c0,
  0x226e0da7cc5795a3e37b17342a26fe0e55cc9ddd9d6b77a74130540359054fa78a5a5120d9533f027b283501c375b444, 0x10f5b9c66de93702d47891b6db93edf71191e9707a65efd8d5334c4794713daa35f7aac0654a3764fe33659441ad471b120, 0x4df2fae1c54849507a43a28ffbdcfc73318bf1372a442c195f5038b7e53326cee7e516186553af2423fb2c59d886d4d7437dc,
  0xdee52ffc3671ab704d110ea85e37fa74bac3c7f17cccdf1b5a63965bdef04ec1c8261bd6ca5da2ae757562cbd50c1c36d72aa80, 0x1a1d8184628da87c44339e62b01ec00d58d6a4f4bce4f13a5d91060c602cf6a359ff88b134b54de7642a9530630f16fa7239044a0a, 0x217fbe432c1f721b34f6bacba856bf4916cc0282f41544800fb4eacf22a0ff16d8de5bb70a0ca701af3cfd48387d11a6214697af2270,
  0x1e76f0c1f805e170d9fe83c0a64301f2a07547aabb6c38c28e9cd24421d96d78dd708d731760b75fd60f526c6882f58b3b2470a626c9a6, 0x143bd1b0d8670b2b75085054ac81500807d940a019c21d153ec52759486ba80b973a8f169763e363200ef8af74dfb8772938d73d79d33860, 0xa104e03104cd6a6e85cd9c1639b14051404f8241ab80021c7de3bb5318ecdf42d4c0c4bfb611a266b2d75d9c30e0ef6066eb60a231d8d4806,
  0x3d44e5afc797622a77f01e66a857abb023bdc84c032eccd6ac4d561c9fcc652d168387100259ee0cc824cc54d5176537d2bae7bef06a047a370, 0x122a756e7fec9b31bb7009cb70e5fc8fcefd1afbeb085bff3f39abdeba6f864f0223aab3e02af4ebde04315809471f399b133a66f576e30650eaa, 0x443912c0469293ab11b87a5c73d215dd81439627a6f5ed65aecf6a5c20f1e2bc541cff932f28f5ef6c3083d8e583b77bf050f6437d1adfe4073c80,
  0xcda8214f91fd7b9889ff918cc60835738240c68c99fb7e42e3f3f87a500175d282c80374ac87de47d90aae1e53b4d9fe3210adf1784f3a2786a522c, 0x1f7aaa2f6bd0e256b87ed7f970390c193961f472318e055a0a4abf26562b3c2ff324d3ae47ac29f8d42eca869aaf327b10f51fb43ff338117b7a112a0, 0x3f4dc38cecb3f454155b344975bf082519c1be0f0202beb0e36ceab547b2ff14d7bcc0c15d536b2aebbbc821af4afb4b40bd914a7e510a1e00187aeb74,
  0x698479de755370aae940831394d5531c47eb99d8888a3d44f3a9349b289bc8f76e897ea1cd39557f421f3ed4156505c98a8cf45f10e547c3c72b2eb28c0, 0x93012185f810b4da64cf8fe685193860d7fce4850f149db7d4099e025d2d53984acd0cae350ae477589f7d8b510fe08aa503d188afef694f8a3410696c44, 0xac744203d904d0962257b1e86c1c165014c3c2c09aed9027c0162cfe64670638c3a49db1d19903e5d133c8f32d8643d6e2cef62010adca8317fd7771a0220,
  0xab7d2b2b36a4c6e3a39e06d0f059d4f8a4786694ad5fc5bc3a0e5e14b1da042c943d3f7014ddca425f2f95adf11b74418fee7b2230c4286358a95e0903ebdc, 0x916962fe2cdac2ec5113492abc35cb9881d7f59fc59682fd898e5b4eacb99cafceefab7957fed583ea3f3208dfbd3aaa75549c2f813f2ec1cda694da6e33380, 0x69b383d47b7f8083de1478bb9d3913657181b68cd5b7687082ed257302dbbcd5309087bcd4758ba2725af02b2464b562c8bb033f1adf455a667dab0937352d47,
  0x422f72aef4131b08cd9890f9413229ddd3a3ac610754c68132341d92af5cfdec8c5b2bbaf07f95be84f9ad3c51857b08403b7efc3dde6761835822b65f2e89aa8, 0x23da415e87288d6739091a5f0b7bea96657e6b91fc91f7061d23db406a7af93c8a500adccf2b090eabe2dccfcc4f8534a63ff08dc4deedcb3cb97a20a8539cd281, 0x10de058aa2ebbc3eb1dec8b8d5ac2fe749e5b1a2b77882a5ce78fa352e3926739cc291ffca6aa6cc8c3604f8e3bebce2485c75dfb4230e095cd89a04502a4bdb0d0,
  0x6ea82c8225c46d6cff1aac404d117a61a9b394e709421232327fc6a6638f9097d7307e114d5ce4af38ad51e443ef6c2eac5ea72b83e4d3a674fc651bc02145c4de9, 0x27ab4fdee43a4c8fa2bbf737481de1a833946a1538dec8c21605e4e8749737d338fca17368bb9d7b309e5affcbd515cd59842989f70ec7a5e7aecad04216c18c2268, 0xc78012900211927957c22f2d340d1fe9cff966a78eec5fb7d578aaa377ef4d742ce7b331ba1cddd577a0537b96e3cbdbf32257091fc1e1cf6f48162be860df95111f,
  0x371f063ecc8f7ed94fe25160f5c62d851afed430484cb679282382d82a136a3c59be7b274ec6b994571c3a54c98adee19ad94defd93f53e5d87d99af7e1870e449f00, 0xd6b0bdb8b21724b8e74897dba677125c0587f378ef18f1a5d78693e56189b8809916e8fac069ffeb3672f6cf7102288b484498f07eca5e13b35de27ecbe06b52d68d8, 0x2e23ba6e588a6b6830aa1cb2e5309218184ba55cf114565379e9cb9885ec2e01db11198f64bf287e495cee8502eacdeb5c82d8cbfcf89168c945682521150128752740,
  0x8c52cc141179a880a249bf669f202c997657a9c9a2cecb8931b10ebe3dc24df7dc2f753df39d9cea067cbf0fb7a77d02a1b996cae9fbebdb4403a06e78c6ec3f69a668, 0x17a0f15beca7fba72014a0318c0563b2a7ce5f2e60b5045d7b7be26d8be964d61a657b5900113cf1d418d26518449cb9f651109da14f5ed8261602e2a8b62a840d97f80, 0x3879713b8fd8d5f3af53d6f14dbfec889214a9d1de6bfb65cf6042e75d4e0a7f8fdcfe81e0ffee6b7270565f8f74014db65938b875410e8caa61d3a303bf12a2a02d9c8,
  0x77e339cce2157bb66400b1294a04844ccefeea41a4d179d5b307b5ca46096dcad6da0cfa65e8038e1d07a445cedadb8ed3d93c1cf68b426c2a415f8d5a44be5bdf70040, 0xe24940c171eb82bb807cde29b4eae151d1b14fbdb122af89e4f76dbc3f1e550cddb735a6aecefb8dfadff5f8219e9bf32c43ebf6ba96967cefa93a3171a969fd898a878, 0x17c152d7969e3df008cc6ac933fa5b9411f27b7023a55c99a383d9dbf508318baf0c99fb220223a79c3b1b8c9b53b99478ef588b4873e8117a93163b11941b355e5fa100,
  0x23882ad502a9ec0db82affa8b05e49d2713e2a56ffa059e02864a34130d0a36a5ac3f53413552185b7dfa353d62dbf06790bd2b84908b0edf8e741ee3437003949a927ec, 0x2f5a853a398e75be56a8dfe4870673b07a866e972abfab3e0bd1f277c2a602d162fa9a340175e06c3ada5549d8d666ba0c0de20b1cb6867cce55d8c4ee1c19b04bcd0120, 0x38402ae6a8c3cbe3a4c9810bccd076fa22d313497f1ad9b9dec1be2cf2292684fd4ea48b8ce0bd47237f9e9aa5681e58f03fc071b496cc23e38a10c8b2f3b22ae991d8b4,
  0x3b92682b72e367bc8fb35932ac24edc781fcbfcb95d60101e01e21e89cf3698368078bcc384d512aefe948c386b464bb7e3d4195e1d48229216888de58d8fcd41aeff540, 0x38402ae6a8c3cbe3a4c9810bccd076fa22d313497f1ad9b9dec1be2cf2292684fd4ea48b8ce0bd47237f9e9aa5681e58f03fc071b496cc23e38a10c8b2f3b22ae991d8b4, 0x2f5a853a398e75be56a8dfe4870673b07a866e972abfab3e0bd1f277c2a602d162fa9a340175e06c3ada5549d8d666ba0c0de20b1cb6867cce55d8c4ee1c19b04bcd0120,
  0x23882ad502a9ec0db82affa8b05e49d2713e2a56ffa059e02864a34130d0a36a5ac3f53413552185b7dfa353d62dbf06790bd2b84908b0edf8e741ee3437003949a927ec, 0x17c152d7969e3df008cc6ac933fa5b9411f27b7023a55c99a383d9dbf508318baf0c99fb220223a79c3b1b8c9b53b99478ef588b4873e8117a93163b11941b355e5fa100, 0xe24940c171eb82bb807cde29b4eae151d1b14fbdb122af89e4f76dbc3f1e550cddb735a6aecefb8dfadff5f8219e9bf32c43ebf6ba96967cefa93a3171a969fd898a878,
  0x77e339cce2157bb66400b1294a04844ccefeea41a4d179d5b307b5ca46096dcad6da0cfa65e8038e1d07a445cedadb8ed3d93c1cf68b426c2a415f8d5a44be5bdf70040, 0x3879713b8fd8d5f3af53d6f14dbfec889214a9d1de6bfb65cf6042e75d4e0a7f8fdcfe81e0ffee6b7270565f8f74014db65938b875410e8caa61d3a303bf12a2a02d9c8, 0x17a0f15beca7fba72014a0318c0563b2a7ce5f2e60b5045d7b7be26d8be964d61a657b5900113cf1d418d26518449cb9f651109da14f5ed8261602e2a8b62a840d97f80,
  0x8c52cc141179a880a249bf669f202c997657a9c9a2cecb8931b10ebe3dc24df7dc2f753df39d9cea067cbf0fb7a77d02a1b996cae9fbebdb4403a06e78c6ec3f69a668, 0x2e23ba6e588a6b6830aa1cb2e5309218184ba55cf114565379e9cb9885ec2e01db11198f64bf287e495cee8502eacdeb5c82d8cbfcf89168c945682521150128752740, 0xd6b0bdb8b21724b8e74897dba677125c0587f378ef18f1a5d78693e56189b8809916e8fac069ffeb3672f6cf7102288b484498f07eca5e13b35de27ecbe06b52d68d8,
  0x371f063ecc8f7ed94fe25160f5c62d851afed430484cb679282382d82a136a3c59be7b274ec6b994571c3a54c98adee19ad94defd93f53e5d87d99af7e1870e449f00, 0xc78012900211927957c22f2d340d1fe9cff966a78eec5fb7d578aaa377ef4d742ce7b331ba1cddd577a0537b96e3cbdbf32257091fc1e1cf6f48162be860df95111f, 0x27ab4fdee43a4c8fa2bbf737481de1a833946a1538dec8c21605e4e8749737d338fca17368bb9d7b309e5affcbd515cd59842989f70ec7a5e7aecad04216c18c2268,
  0x6ea82c8225c46d6cff1aac404d117a61a9b394e709421232327fc6a6638f9097d7307e114d5ce4af38ad51e443ef6c2eac5ea72b83e4d3a674fc651bc02145c4de9, 0x10de058aa2ebbc3eb1dec8b8d5ac2fe749e5b1a2b77882a5ce78fa352e3926739cc291ffca6aa6cc8c3604f8e3bebce2485c75dfb4230e095cd89a04502a4bdb0d0, 0x23da415e87288d6739091a5f0b7bea96657e6b91fc91f7061d23db406a7af93c8a500adccf2b090eabe2dccfcc4f8534a63ff08dc4deedcb3cb97a20a8539cd281,
  0x422f72aef4131b08cd9890f9413229ddd3a3ac610754c68132341d92af5cfdec8c5b2bbaf07f95be84f9ad3c51857b08403b7efc3dde6761835822b65f2e89aa8, 0x69b383d47b7f8083de1478bb9d3913657181b68cd5b7687082ed257302dbbcd5309087bcd4758ba2725af02b2464b562c8bb033f1adf455a667dab0937352d47, 0x916962fe2cdac2ec5113492abc35cb9881d7f59fc59682fd898e5b4eacb99cafceefab7957fed583ea3f3208dfbd3aaa75549c2f813f2ec1cda694da6e33380,
  0xab7d2b2b36a4c6e3a39e06d0f059d4f8a4786694ad5fc5bc3a0e5e14b1da042c943d3f7014ddca425f2f95adf11b74418fee7b2230c4286358a95e0903ebdc, 0xac744203d904d0962257b1e86c1c165014c3c2c09aed9027c0162cfe64670638c3a49db1d19903e5d133c8f32d8643d6e2cef62010adca8317fd7771a0220, 0x93012185f810b4da64cf8fe685193860d7fce4850f149db7d4099e025d2d53984acd0cae350ae477589f7d8b510fe08aa503d188afef694f8a3410696c44,
  0x698479de755370aae940831394d5531c47eb99d8888a3d44f3a9349b289bc8f76e897ea1cd39557f421f3ed4156505c98a8cf45f10e547c3c72b2eb28c0, 0x3f4dc38cecb3f454155b344975bf082519c1be0f0202beb0e36ceab547b2ff14d7bcc0c15d536b2aebbbc821af4afb4b40bd914a7e510a1e00187aeb74, 0x1f7aaa2f6bd0e256b87ed7f970390c193961f472318e055a0a4abf26562b3c2ff324d3ae47ac29f8d42eca869aaf327b10f51fb43ff338117b7a112a0,
  0xcda8214f91fd7b9889ff918cc60835738240c68c99fb7e42e3f3f87a500175d282c80374ac87de47d90aae1e53b4d9fe3210adf1784f3a2786a522c, 0x443912c0469293ab11b87a5c73d215dd81439627a6f5ed65aecf6a5c20f1e2bc541cff932f28f5ef6c3083d8e583b77bf050f6437d1adfe4073c80, 0x122a756e7fec9b31bb7009cb70e5fc8fcefd1afbeb085bff3f39abdeba6f864f0223aab3e02af4ebde04315809471f399b133a66f576e30650eaa,
  0x3d44e5afc797622a77f01e66a857abb023bdc84c032eccd6ac4d561c9fcc652d168387100259ee0cc824cc54d5176537d2bae7bef06a047a370, 0xa104e03104cd6a6e85cd9c1639b14051404f8241ab80021c7de3bb5318ecdf42d4c0c4bfb611a266b2d75d9c30e0ef6066eb60a231d8d4806, 0x143bd1b0d8670b2b75085054ac81500807d940a019c21d153ec52759486ba80b973a8f169763e363200ef8af74dfb8772938d73d79d33860,
  0x1e76f0c1f805e170d9fe83c0a64301f2a07547aabb6c38c28e9cd24421d96d78dd708d731760b75fd60f526c6882f58b3b2470a626c9a6, 0x217fbe432c1f721b34f6bacba856bf4916cc0282f41544800fb4eacf22a0ff16d8de5bb70a0ca701af3cfd48387d11a6214697af2270, 0x1a1d8184628da87c44339e62b01ec00d58d6a4f4bce4f13a5d91060c602cf6a359ff88b134b54de7642a9530630f16fa7239044a0a,
  0xdee52ffc3671ab704d110ea85e37fa74bac3c7f17cccdf1b5a63965bdef04ec1c8261bd6ca5da2ae757562cbd50c1c36d72aa80, 0x4df2fae1c54849507a43a28ffbdcfc73318bf1372a442c195f5038b7e53326cee7e516186553af2423fb2c59d886d4d7437dc, 0x10f5b9c66de93702d47891b6db93edf71191e9707a65efd8d5334c4794713daa35f7aac0654a3764fe33659441ad471b120,
  0x226e0da7cc5795a3e37b17342a26fe0e55cc9ddd9d6b77a74130540359054fa78a5a5120d9533f027b283501c375b444, 0x2594139249b14305ed2ae48ea2125b67facce25dff6644a6f0379818f10e14d7a52d3b6cac2ea938572897b4e97c0, 0x13e155cdf43b9be2afa2f8092b76725caca09ca23bf88e059d9dd92f265ea0b51950bfb73bb1ab4d7a11443bd4,
  0x474afb1bb446df3b97019bea529555a8ca3af9b4a057aa4e25f5e4d7e36355263c2cbec8887bfa11e652a0, 0x5a9a0b703a98052fdff5997ebf2fae516c65c8df50392dcc3e67aa5bc849e9ab10a930860ad7c2f0cc, 0x1fff17ffbe314e794113b7a3dff3021c5d52914df8145513f71e59285f758af0b7d63ceefea580,
  0x23b135949afc0b53dbf98ee62bb7b2aa1d7992b7ef17b0fe57eff1ca6e6b8e978eeb7c8f9, 0x4c2b531219b6774e75e02755b125bf184eb3cc085dc320f35a7b063469acc483c58, 0x8edf989b9a373fed0e58147e15675c7fed4ef252a0a035f158a7bbcc013f,
  0x3ffffffffc21cc98ebe3d84a02c7046dab7653413ac710e3dc30, 0x9856ad658e2d7cd1b9ff5196da1a9380cdaea2bf7, 0x7fffffffffffffffffffffff98,
  0x1]

private theorem eulerianCoefficients_eq : descentCoeffs 103 = eulerianCoefficients := by
  decide +kernel

private theorem upper : upperOK (descentCoeffs 103) first gaps = true := by
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

private theorem lower (i : Fin (lastRepresentative 104 - 2)) :
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

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 104) :
    StrictNegativeInterlacing (originalQuotient 104 k) (eulerian 103) 101 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N104
