import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentPackedData.C127L120.N119

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N119

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L120.N119 LongCycleBounds.DescentNecklace.Packed.C127L120.N119.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L120.N119 LongCycleBounds.DescentNecklace.Packed.C127L120.N119.rows

private theorem actual : RepresentativeChecks 119 previousNodes rows :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L120.N119 LongCycleBounds.DescentNecklace.Packed.C127L120.N119.dataChecks

private def first : LongCycleFinite.Dyadic := ⟨-332306998946228968225951765070086144, 0⟩

private def gaps : List Window := [
  ⟨⟨-332296223916127028276039043092840448, 0⟩, ⟨-605763423278909620224, 0⟩⟩,
  ⟨⟨-596537799442241159168, 0⟩, ⟨-563166849269760, 0⟩⟩,
  ⟨⟨-539153687117824, 0⟩, ⟨-295200358400, 0⟩⟩,
  ⟨⟨-269633454080, 0⟩, ⟨-2149515264, 0⟩⟩,
  ⟨⟨-2136281088, 0⟩, ⟨-74653952, 0⟩⟩,
  ⟨⟨-74548992, 0⟩, ⟨-6318864, 0⟩⟩,
  ⟨⟨-6315296, 0⟩, ⟨-950032, 0⟩⟩,
  ⟨⟨-949744, 0⟩, ⟨-423311, 1⟩⟩,
  ⟨⟨-211615, 0⟩, ⟨-499375, 3⟩⟩,
  ⟨⟨-499309, 3⟩, ⟨-90607, 2⟩⟩,
  ⟨⟨-45299, 1⟩, ⟨-307945, 5⟩⟩,
  ⟨⟨-307921, 5⟩, ⟨-295761, 6⟩⟩,
  ⟨⟨-147871, 5⟩, ⟨-156523, 6⟩⟩,
  ⟨⟨-156515, 6⟩, ⟨-358347, 8⟩⟩,
  ⟨⟨-358331, 8⟩, ⟨-437325, 9⟩⟩,
  ⟨⟨-109327, 7⟩, ⟨-281395, 9⟩⟩,
  ⟨⟨-281385, 9⟩, ⟨-378571, 10⟩⟩,
  ⟨⟨-5915, 4⟩, ⟨-264391, 10⟩⟩,
  ⟨⟨-264383, 10⟩, ⟨-381317, 11⟩⟩,
  ⟨⟨-95327, 9⟩, ⟨-282649, 11⟩⟩,
  ⟨⟨-141321, 10⟩, ⟨-214561, 11⟩⟩,
  ⟨⟨-214557, 11⟩, ⟨-83143, 10⟩⟩,
  ⟨⟨-166283, 11⟩, ⟨-65619, 10⟩⟩,
  ⟨⟨-262471, 12⟩, ⟨-420983, 13⟩⟩,
  ⟨⟨-26311, 9⟩, ⟨-342421, 13⟩⟩,
  ⟨⟨-21401, 9⟩, ⟨-282041, 13⟩⟩,
  ⟨⟨-70509, 11⟩, ⟨-469847, 14⟩⟩,
  ⟨⟨-29365, 10⟩, ⟨-98825, 12⟩⟩,
  ⟨⟨-395295, 14⟩, ⟨-167797, 13⟩⟩,
  ⟨⟨-335589, 14⟩, ⟨-143611, 13⟩⟩,
  ⟨⟨-143609, 13⟩, ⟨-247627, 14⟩⟩,
  ⟨⟨-30953, 11⟩, ⟨-429819, 15⟩⟩,
  ⟨⟨-429815, 15⟩, ⟨-375273, 15⟩⟩,
  ⟨⟨-93817, 13⟩, ⟨-164721, 14⟩⟩,
  ⟨⟨-164719, 14⟩, ⟨-72661, 13⟩⟩,
  ⟨⟨-290641, 15⟩, ⟨-257577, 15⟩⟩,
  ⟨⟨-515149, 16⟩, ⟨-458425, 16⟩⟩,
  ⟨⟨-458421, 16⟩, ⟨-204739, 15⟩⟩,
  ⟨⟨-204737, 15⟩, ⟨-183505, 15⟩⟩,
  ⟨⟨-183503, 15⟩, ⟨-329979, 16⟩⟩,
  ⟨⟨-41247, 13⟩, ⟨-297531, 16⟩⟩,
  ⟨⟨-37191, 13⟩, ⟨-268971, 16⟩⟩,
  ⟨⟨-268969, 16⟩, ⟨-487457, 17⟩⟩,
  ⟨⟨-487453, 17⟩, ⟨-442663, 17⟩⟩,
  ⟨⟨-110665, 15⟩, ⟨-100693, 15⟩⟩,
  ⟨⟨-402769, 17⟩, ⟨-367121, 17⟩⟩,
  ⟨⟨-183559, 16⟩, ⟨-335161, 17⟩⟩,
  ⟨⟨-167579, 16⟩, ⟨-306419, 17⟩⟩,
  ⟨⟨-19151, 13⟩, ⟨-17531, 13⟩⟩,
  ⟨⟨-140247, 16⟩, ⟨-514115, 18⟩⟩,
  ⟨⟨-514111, 18⟩, ⟨-471615, 18⟩⟩,
  ⟨⟨-471611, 18⟩, ⟨-432995, 18⟩⟩,
  ⟨⟨-13531, 13⟩, ⟨-198913, 17⟩⟩,
  ⟨⟨-397823, 18⟩, ⟨-11429, 13⟩⟩,
  ⟨⟨-365725, 18⟩, ⟨-336377, 18⟩⟩,
  ⟨⟨-336375, 18⟩, ⟨-309491, 18⟩⟩,
  ⟨⟨-19343, 14⟩, ⟨-71205, 16⟩⟩,
  ⟨⟨-142409, 17⟩, ⟨-262145, 18⟩⟩,
  ⟨⟨-262143, 18⟩, ⟨-241275, 18⟩⟩,
  ⟨⟨-482547, 19⟩, ⟨-444085, 19⟩⟩,
  ⟨⟨-222041, 18⟩, ⟨-408589, 19⟩⟩,
  ⟨⟨-204293, 18⟩, ⟨-375799, 19⟩⟩,
  ⟨⟨-93949, 17⟩, ⟨-172739, 18⟩⟩,
  ⟨⟨-345475, 19⟩, ⟨-39677, 16⟩⟩,
  ⟨⟨-158707, 18⟩, ⟨-291425, 19⟩⟩,
  ⟨⟨-145711, 18⟩, ⟨-133667, 18⟩⟩,
  ⟨⟨-66833, 17⟩, ⟨-489987, 20⟩⟩,
  ⟨⟨-489983, 20⟩, ⟨-448537, 20⟩⟩,
  ⟨⟨-224267, 19⟩, ⟨-410073, 20⟩⟩,
  ⟨⟨-205035, 19⟩, ⟨-374371, 20⟩⟩,
  ⟨⟨-11699, 15⟩, ⟨-85309, 18⟩⟩,
  ⟨⟨-341233, 20⟩, ⟨-310485, 20⟩⟩,
  ⟨⟨-155241, 19⟩, ⟨-281953, 20⟩⟩,
  ⟨⟨-281951, 20⟩, ⟨-510987, 21⟩⟩,
  ⟨⟨-510983, 21⟩, ⟨-230969, 20⟩⟩,
  ⟨⟨-230967, 20⟩, ⟨-416513, 21⟩⟩,
  ⟨⟨-416509, 21⟩, ⟨-374485, 21⟩⟩,
  ⟨⟨-187241, 20⟩, ⟨-10489, 16⟩⟩,
  ⟨⟨-335645, 21⟩, ⟨-299809, 21⟩⟩,
  ⟨⟨-149903, 20⟩, ⟨-266795, 21⟩⟩,
  ⟨⟨-33349, 18⟩, ⟨-472881, 22⟩⟩,
  ⟨⟨-118219, 20⟩, ⟨-417191, 22⟩⟩,
  ⟨⟨-417187, 22⟩, ⟨-366239, 22⟩⟩,
  ⟨⟨-366235, 22⟩, ⟨-79941, 20⟩⟩,
  ⟨⟨-19985, 18⟩, ⟨-277515, 22⟩⟩,
  ⟨⟨-34689, 19⟩, ⟨-478517, 23⟩⟩,
  ⟨⟨-29907, 19⟩, ⟨-409547, 23⟩⟩,
  ⟨⟨-204771, 22⟩, ⟨-173843, 22⟩⟩,
  ⟨⟨-173841, 22⟩, ⟨-73131, 21⟩⟩,
  ⟨⟨-36565, 20⟩, ⟨-30457, 20⟩⟩,
  ⟨⟨-487305, 24⟩, ⟨-401383, 24⟩⟩,
  ⟨⟨-401377, 24⟩, ⟨-326475, 24⟩⟩,
  ⟨⟨-163235, 23⟩, ⟨-261815, 24⟩⟩,
  ⟨⟨-261811, 24⟩, ⟨-25829, 21⟩⟩,
  ⟨⟨-413257, 25⟩, ⟨-160143, 24⟩⟩,
  ⟨⟨-320281, 25⟩, ⟨-243131, 25⟩⟩,
  ⟨⟨-486253, 26⟩, ⟨-360443, 26⟩⟩,
  ⟨⟨-90109, 24⟩, ⟨-519847, 27⟩⟩,
  ⟨⟨-129959, 25⟩, ⟨-90765, 25⟩⟩,
  ⟨⟨-90763, 25⟩, ⟨-488433, 28⟩⟩,
  ⟨⟨-488421, 28⟩, ⟨-314283, 28⟩⟩,
  ⟨⟨-314275, 28⟩, ⟨-383555, 29⟩⟩,
  ⟨⟨-383543, 29⟩, ⟨-439053, 30⟩⟩,
  ⟨⟨-219519, 29⟩, ⟨-464715, 31⟩⟩,
  ⟨⟨-232349, 30⟩, ⟨-446349, 32⟩⟩,
  ⟨⟨-446331, 32⟩, ⟨-47407, 30⟩⟩,
  ⟨⟨-379239, 33⟩, ⟨-137629, 33⟩⟩,
  ⟨⟨-68811, 32⟩, ⟨-162363, 35⟩⟩,
  ⟨⟨-81177, 34⟩, ⟨-289357, 38⟩⟩,
  ⟨⟨-289339, 38⟩, ⟨-87029, 39⟩⟩,
  ⟨⟨-348093, 41⟩, ⟨-471649, 45⟩⟩,
  ⟨⟨-471615, 45⟩, ⟨-2055, 42⟩⟩,
  ⟨⟨-65755, 47⟩, ⟨-266477, 56⟩⟩,
  ⟨⟨-33307, 53⟩, ⟨-133493, 66⟩⟩,
  ⟨⟨-266963, 67⟩, ⟨-257553, 87⟩⟩,
  ⟨⟨-257529, 87⟩, ⟨-262165, 136⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private def eulerianCoefficients : List ℤ := [
  0x1, 0x3fffffffffffffffffffffffffff89, 0x824a11449f8c987d51aca7934d6edbe43a8ffa868fe2306,
  0xffffffffffc36f91f919d5a51d4f78be1a870177c8e8c7128b731e64a46, 0x3f72d3e789858a98dd0452154d8949c0a0477cf1c0a94d14ac28f7ffb8fdced5656fd, 0x20928433a982a562fa57bcd61ab635fea3066302d85a4c9a6834005370b0e1bb16ea5874b4195,
  0x9a1ddacd8c5d42b8d3f5b9748a6354a4aee9975d67c5202a25a126013a07e735d67a7db71db80d53bb8, 0x3fffb85c1bbdfd505e49ad6b92f562fa20ecdf68057213a1e0930ed459a8ba3d48a501575fd7effbd0d747938, 0x424d72f8b70d95cf371deebe1646563d89f67f29db50d0e6e912e4c6007ac045252d59a7a4944b21f0a5b22b12526e,
  0xfdac7d3000cba0efe07d5f177975d30a80b7622e98ef5d7f0a6d12b178de88d15f9cd91983461f90def5af08c6d3b8b91e, 0x12840eeb0e0ed46ef328e2889e26d9edc127c602e8e454989696a2f894cc9815e249b87dae2c7dd06a7159ef4d21e161010465c, 0x81c03f716925371468318e50c33d4639ffb70dbda2c75af53ac698d15a4a7dbaeef5a4a1190500368916e954aee82b674000fd835c,
  0x18e748af5ceeae5a84390c90315a88fcd78e4c4f9aff7bbb22f039c2c249e9c5ad8ec7f2f8dcc81dde308698d2dcfc22f0e70a6ccb1eae, 0x25cd5fd10deb12910f5507d20305abc555d9e5c0fd8330c2c66c42e2b50be2ebb34d085bf68f8709b178b458e911675243389aacc01b77e7e, 0x1f2ecacea685b5a6035fcb1bac3a1fae775b391e8ffda7b80c569d995b16b042052469a442ac5fee7eaa88bd6141f7704683506b8ffe5d7b2698,
  0xf13eecc73d71040df325934a4a273458d27735b1be37dbe559f4b6ff7957c1d9a7b8b4996113ce495aef64866708a3deb25a336dbeac67ec99cf18, 0x48b418fdf4871b0f7e712811d5ed70b86c3e62fe876dddef7aba70095222354b1fb647f287765b20640cb82fefe445184b9b5a8936be123b4ed397f1f, 0xe5c4580edbab0158277014e17724ed42824ee2a69ba073ee829cfabee89d750c972f98fca1d7d5365e77f8dbba22781dd48b2718d1f9304c632aa0cd8d7,
  0x1f030076070672867f7d33867e522bd3a093d9770b60499a34532c6ba53871f61c7ad62955e91a838a76b68e59c09221f95057b92d02cdcfe7fcfe0e79ae22, 0x2f6371b1a3a2466658117ab83822e68637899ff18e4558420e8c5ff667e6e1d7dc6c147f8b519a84afcb423037121bc745e0a49b0370093046ec646eade4dd62, 0x34c616a34d3be12d64d77001c27738ddd0c5d3117925717b1c39c0f945ee9d4c7713178a46ce2afca2d12098e1e08af0e39506f55c1ad911c4d8420b9af7607f4b,
  0x2bebec45a9781951d343ae92bde49685d7a8515eb33fec6ae56fa4870a3360fa869e310113fe7f4ad8b75451f5b01f7ea117b26b5fcff4f43339f6b09181729657b3, 0x1be9fe58f30c70d2ac50a9dc15feb09e94296ac1e6fe5b0a92e01ce981d8886fc38d60c964f0eaa80cc6b611d591145bac7eef915201fcf1ff1cd9b466300a9c4024d0, 0xdcd6ad1ae3174a11dc2fbb0fc5830bda622d41a0fd459d0e4d48fe662470b9f71f3958f0463169bfe86d5daf3f949086dbebf39225cd619e33688ad5a528e1610f649d0,
  0x5658c0579f68fda32d45fbc714a5d87934521012cb6de48c07c33855f8ad8e92da0e120948c923fed5be7fcba89140b0ab83264f8b33812c8206c4b69634c89a78647789c, 0x1b1422156d81ead1dec7dcaffaa187c7f6fcb18b426057c31b3f5aa736dc461ef5f100c23684cc64e90df987ccf80346dfa3045c683bb66ef8671f07d111cb26ed3bda504fc, 0x6e598172c6dbe3e48ee104662472f1e66783deeea426611aab7eec6bffe0920020b8c791cb7ab587a47e4133da562772682eca0a76f17618ba6ff2b15d8ebf38958315f605d8,
  0x1714912542da3207dcf3e691f0a2d56dd240c49cc08fd2b53d79e093ae63e7b225ce8259bc5a15d1aa422fe731f3efe0eaf7188b139f6b0e0d114f064b8870ebcff39ebabd91d8, 0x400df330342a5fbbbbfc3a1c93ad9106c8f286ff12aa469c5e3b21f1b3f5fa3f75d4607c8b19affc9658efa29ca5407f8e89b971f0996ed74d44a0a68c6c44eb4b2d015c78e8abc, 0x94b95e983458a378b49aef10d78f46f531aa2bdfda433a3ef561afcc62b67735dfbf0e4d1edcefac82b990b74941144e4fa758be6078c2d1d29c9b803a1351ffb531400bed45c45c,
  0x1232baec518a9ab56ae5ab80e98b633bb3955a0530dd9e58c7b366112b07738db55bfd967388459109dda83f90289ae3df99679ea82f86e5a8b324f0c1c533f9ca06b335686a633c50, 0x1e4130d146fb876f388aa89e3c228714bf6f77e77f81f77a48a39f6e9b628aded0c60bebbeed23497b83c211ccc6bd2dd830a723e64821757e7ba23e5aa267a61cf64622c36e14d7f50, 0x2afc23e16e707e91b423711415c5cbf09bc50c503b03d6ebfc1d5d9b17284b18a8bed81777ceb3b30e513b7eff17b1e1ff9a53caf84c80cc11107adb1a4adb5a6f97e4c5e6c9fc563a81,
  0x347dff3ce459848c0737eaec0d479e381c8d5f540e880a44444c50aaa034fa3e65c08e3ef48344f9521703783dfda8b7ad6f325d048e5787182670360176059e194c11c0d77d0db1fdd89, 0x376266f10b4f6deb4848fdb435987de0e55ee3410ea30b5b2b7389ebcabacab9c0f6f94e7ea68e417b2e258fa569b16f6544ac20dae55699630abcf86298f7f8b095e5f541483221a29db6, 0x32ba4dc83dccd05f8c1b5335e3ecc59b5e69ed1ef771e94943aade596f3f365b26ff4c17c9644601cedb99286ac686d2b241925bc0d38b9f786182386202c7aca9d027e988ba929d741cbf6,
  0x2881e592decb2c6cb4646adb0376081710ae51b79b2d8ca3f6ce93fd0c46e9f80e9a1e79b62e1f5bb7a43f3341a2b8ffe39415c91bb66bedb547afbc1c531931644cd1ef91c8f326d2b8d0ed, 0x1c4f91377dd294c0db22473d2372754f00c8abc6ef4eb777e0a5b07a2fd9de362c6a798c8daa8a8eb86690859d8e259e4caf5d108807c2e1e0518ffb672014d0479ca81b84549b8dc9a2ac585, 0x11614161dc7fbd13b2f59f470f932c2040b2c1ea01fdb0310ce8189685d97d9816d30ae00363d70c2a1cace1c9306241fb4134632594ae543bc39b3c4266c82507c2c3670d266e392fab6976a8,
  0x966fac96490e389b3db469f10c413c899d05a4e4afee4bd0a47f543997ea5f6207efd1c2e2c86a98b056f15820f173c2837097a2f2fcb53e718cd23ca30699b4098f9dc8c1d297005205dd5328, 0x47ee621dcf99df2d20f6c1908dc87b533268bd65c4fda97232911e663a8ba6d71e088438414abf7ec2d305d7ec1cb6c6686862b7e03526a768e7d6d4f00622af2529032b5d4d001ca2caeb0e5c2, 0x1e7b511f96930ef7a10116bd42d52c59a5d6f3a93a0b291f514ab4143696f6c4fcd741f92f7fa213b8f98f91f4b55956e85367b1e9e6208d9110fb895e1331c39fd72f982de287a3eac1e2576192,
  0xb79e07c24b5a5324dc899ac15c5c7b52d62dfcb9710d6085b0228cfeb60e491e37f2cb70a75f3c9601870d38bbb579f21fbe32b6ba661397bfd2af7f8198e1b98905774d69cd20cd6d28016d6864, 0x3d8eb87208f26255422ad42d4bac7df0c89442176449aafcdbf381b8ac82e8ae6e957bcf9c6f425abab78a9b7747830359a838b4b74eee675b25ea1631f1c8d486e6a54ff7182fc23d3a34f8d9964, 0x126a0f74eeb8cf0d47882b1ebb5ae63b5e2a9ffb4c707d35273168583115419927d40927b37436c7cbf11d5f3dddb17e521ab77e253ff8019ff25e3392c25c80e67f7baa39c8bd6bf03ed44de45562,
  0x4eca2917005e24da93569033cca9784fc5f56160a046bc07b5d171a06911e6b73f67369b5e6f2fa26683d460ce19fdbf1202d4fc16e5d521d00fed9713de1349bc87356e8109c8095a9fab9d237a12, 0x12de2a1e351a8a6cbafb59c6d192eee5438ee0a203092b81e0f381409f7e70862cd5c652433522f84404cbd0702fc9fd0edfbf2aedb4debedba6a7b0568c0e896444743d19492b2ee615a96e69e8608, 0x40d634551af2869768ecd55a1a45643751815b7e7651547481083726cb17467cc130ad39e3bc5cc18445568a9bfee1416adf0600ea30535bb08696e664de3291b11cc907a24cb3dff6dac0630022788,
  0xc819e4e487473744d236773d0a78384d56f0ab5dffd304c94ac4daa640e7ff5992a419fe7fce460a1bac9b640e000dcc2d7fab254a408b9040dbf94521655dbf641e57864d6ea6f0d307077812b6747, 0x22b5374ff3c8dab2bae9feb4a7b533ed349c57a183094f81110eb0c9fd00ce7384c5e9e315f1a9ccabb8811afc3ba45b7f7619ad219a0474ee8c38d0f31d6bac031ce50fee941987dd571081f8b9b0bf, 0x56b63de33de5ac63ee74b84bd82201eaabc913211eb71b2f913f0f109a4959e4ab3966340baa0cffee68d4a76eb9f3a568c0e99958b628b0d1035d3beb4771ac7d0f51f1e7a4a4730411fadeae9533a2,
  0xc3366c621e9e963e4a9d81e7c5be11d192ee41a8eb5484094e7d2d1749be0dc9714bb0d1690496148be286aa4f51fe45f5e994fae5999976a9e08e2b1fe57776372bf380c68432bf2fd76704dd58a9e2, 0x18c5bf51c65177114c606999de015180c3a354d5dbca830fe6c85448125a1a0cc9d1ebe42c983090c00b7ac2a7562d7134d0ba496e16d4525026a94bf366b0ab5f208527ebe2723c52fb1acf408c1d223, 0x2d658dc67135cc305561642486e89d260f2c7ea7da455285f02e2b1a723800082a06a02097ac9813f785fb72986c24d38973d168c9f6c2799fd5a48f3e06ab8f1cf3cd5cfb47ad61463d7e29c4511604b,
  0x4b21dd99b1a6eaeda9d7778a8f215620a1f2d539ea94a6ed5d18a6b8ae48d935fdda091f153d021476a4afdde2ae252278e376c6ce4273d13b9793eed8ff68614a5c9d19d51c39a60b406d9229e3bb2e0, 0x705b7940724c5e374faaa90c72a9971679b48445ba45372ddf0d2aa302c5bdad9c6b04f7c4942d460cd6dee909fa3e8284032e5fd7edb7435c282349f4f0bcc1489c887d68f314f94a272260dd89700e0, 0x97e3ab0523e771d46f991e5005ce2e9e4d05e8fc255eff284fab31ed7521ebbea5fdcbd8170110a3b17aea68e287cd7cd6a9aba09de79c3c6ca2fa2f642d3830a68f8b27c125029acb4ae5ce38ffbb248,
  0xb9ab0f6372485018c99c5f630e9e05577e8c26e021ba297096834ac221d6a2e1c1be1927923e6d75028fcf0714757becda634e95d936004a55131e666fd1682effe1e0bd993456c104ce726130bf50188, 0xcd448830445e113b80202714f2d46b8c64ecacbf8e37b0e122adf4c284777ceb4af8296b7334b07425c6e1c2749f5ce3a82665f6b69db05e0952e8348f922939328fce3b8347421e8b1c3c6a2e12e5cd0, 0xcd448830445e113b80202714f2d46b8c64ecacbf8e37b0e122adf4c284777ceb4af8296b7334b07425c6e1c2749f5ce3a82665f6b69db05e0952e8348f922939328fce3b8347421e8b1c3c6a2e12e5cd0,
  0xb9ab0f6372485018c99c5f630e9e05577e8c26e021ba297096834ac221d6a2e1c1be1927923e6d75028fcf0714757becda634e95d936004a55131e666fd1682effe1e0bd993456c104ce726130bf50188, 0x97e3ab0523e771d46f991e5005ce2e9e4d05e8fc255eff284fab31ed7521ebbea5fdcbd8170110a3b17aea68e287cd7cd6a9aba09de79c3c6ca2fa2f642d3830a68f8b27c125029acb4ae5ce38ffbb248, 0x705b7940724c5e374faaa90c72a9971679b48445ba45372ddf0d2aa302c5bdad9c6b04f7c4942d460cd6dee909fa3e8284032e5fd7edb7435c282349f4f0bcc1489c887d68f314f94a272260dd89700e0,
  0x4b21dd99b1a6eaeda9d7778a8f215620a1f2d539ea94a6ed5d18a6b8ae48d935fdda091f153d021476a4afdde2ae252278e376c6ce4273d13b9793eed8ff68614a5c9d19d51c39a60b406d9229e3bb2e0, 0x2d658dc67135cc305561642486e89d260f2c7ea7da455285f02e2b1a723800082a06a02097ac9813f785fb72986c24d38973d168c9f6c2799fd5a48f3e06ab8f1cf3cd5cfb47ad61463d7e29c4511604b, 0x18c5bf51c65177114c606999de015180c3a354d5dbca830fe6c85448125a1a0cc9d1ebe42c983090c00b7ac2a7562d7134d0ba496e16d4525026a94bf366b0ab5f208527ebe2723c52fb1acf408c1d223,
  0xc3366c621e9e963e4a9d81e7c5be11d192ee41a8eb5484094e7d2d1749be0dc9714bb0d1690496148be286aa4f51fe45f5e994fae5999976a9e08e2b1fe57776372bf380c68432bf2fd76704dd58a9e2, 0x56b63de33de5ac63ee74b84bd82201eaabc913211eb71b2f913f0f109a4959e4ab3966340baa0cffee68d4a76eb9f3a568c0e99958b628b0d1035d3beb4771ac7d0f51f1e7a4a4730411fadeae9533a2, 0x22b5374ff3c8dab2bae9feb4a7b533ed349c57a183094f81110eb0c9fd00ce7384c5e9e315f1a9ccabb8811afc3ba45b7f7619ad219a0474ee8c38d0f31d6bac031ce50fee941987dd571081f8b9b0bf,
  0xc819e4e487473744d236773d0a78384d56f0ab5dffd304c94ac4daa640e7ff5992a419fe7fce460a1bac9b640e000dcc2d7fab254a408b9040dbf94521655dbf641e57864d6ea6f0d307077812b6747, 0x40d634551af2869768ecd55a1a45643751815b7e7651547481083726cb17467cc130ad39e3bc5cc18445568a9bfee1416adf0600ea30535bb08696e664de3291b11cc907a24cb3dff6dac0630022788, 0x12de2a1e351a8a6cbafb59c6d192eee5438ee0a203092b81e0f381409f7e70862cd5c652433522f84404cbd0702fc9fd0edfbf2aedb4debedba6a7b0568c0e896444743d19492b2ee615a96e69e8608,
  0x4eca2917005e24da93569033cca9784fc5f56160a046bc07b5d171a06911e6b73f67369b5e6f2fa26683d460ce19fdbf1202d4fc16e5d521d00fed9713de1349bc87356e8109c8095a9fab9d237a12, 0x126a0f74eeb8cf0d47882b1ebb5ae63b5e2a9ffb4c707d35273168583115419927d40927b37436c7cbf11d5f3dddb17e521ab77e253ff8019ff25e3392c25c80e67f7baa39c8bd6bf03ed44de45562, 0x3d8eb87208f26255422ad42d4bac7df0c89442176449aafcdbf381b8ac82e8ae6e957bcf9c6f425abab78a9b7747830359a838b4b74eee675b25ea1631f1c8d486e6a54ff7182fc23d3a34f8d9964,
  0xb79e07c24b5a5324dc899ac15c5c7b52d62dfcb9710d6085b0228cfeb60e491e37f2cb70a75f3c9601870d38bbb579f21fbe32b6ba661397bfd2af7f8198e1b98905774d69cd20cd6d28016d6864, 0x1e7b511f96930ef7a10116bd42d52c59a5d6f3a93a0b291f514ab4143696f6c4fcd741f92f7fa213b8f98f91f4b55956e85367b1e9e6208d9110fb895e1331c39fd72f982de287a3eac1e2576192, 0x47ee621dcf99df2d20f6c1908dc87b533268bd65c4fda97232911e663a8ba6d71e088438414abf7ec2d305d7ec1cb6c6686862b7e03526a768e7d6d4f00622af2529032b5d4d001ca2caeb0e5c2,
  0x966fac96490e389b3db469f10c413c899d05a4e4afee4bd0a47f543997ea5f6207efd1c2e2c86a98b056f15820f173c2837097a2f2fcb53e718cd23ca30699b4098f9dc8c1d297005205dd5328, 0x11614161dc7fbd13b2f59f470f932c2040b2c1ea01fdb0310ce8189685d97d9816d30ae00363d70c2a1cace1c9306241fb4134632594ae543bc39b3c4266c82507c2c3670d266e392fab6976a8, 0x1c4f91377dd294c0db22473d2372754f00c8abc6ef4eb777e0a5b07a2fd9de362c6a798c8daa8a8eb86690859d8e259e4caf5d108807c2e1e0518ffb672014d0479ca81b84549b8dc9a2ac585,
  0x2881e592decb2c6cb4646adb0376081710ae51b79b2d8ca3f6ce93fd0c46e9f80e9a1e79b62e1f5bb7a43f3341a2b8ffe39415c91bb66bedb547afbc1c531931644cd1ef91c8f326d2b8d0ed, 0x32ba4dc83dccd05f8c1b5335e3ecc59b5e69ed1ef771e94943aade596f3f365b26ff4c17c9644601cedb99286ac686d2b241925bc0d38b9f786182386202c7aca9d027e988ba929d741cbf6, 0x376266f10b4f6deb4848fdb435987de0e55ee3410ea30b5b2b7389ebcabacab9c0f6f94e7ea68e417b2e258fa569b16f6544ac20dae55699630abcf86298f7f8b095e5f541483221a29db6,
  0x347dff3ce459848c0737eaec0d479e381c8d5f540e880a44444c50aaa034fa3e65c08e3ef48344f9521703783dfda8b7ad6f325d048e5787182670360176059e194c11c0d77d0db1fdd89, 0x2afc23e16e707e91b423711415c5cbf09bc50c503b03d6ebfc1d5d9b17284b18a8bed81777ceb3b30e513b7eff17b1e1ff9a53caf84c80cc11107adb1a4adb5a6f97e4c5e6c9fc563a81, 0x1e4130d146fb876f388aa89e3c228714bf6f77e77f81f77a48a39f6e9b628aded0c60bebbeed23497b83c211ccc6bd2dd830a723e64821757e7ba23e5aa267a61cf64622c36e14d7f50,
  0x1232baec518a9ab56ae5ab80e98b633bb3955a0530dd9e58c7b366112b07738db55bfd967388459109dda83f90289ae3df99679ea82f86e5a8b324f0c1c533f9ca06b335686a633c50, 0x94b95e983458a378b49aef10d78f46f531aa2bdfda433a3ef561afcc62b67735dfbf0e4d1edcefac82b990b74941144e4fa758be6078c2d1d29c9b803a1351ffb531400bed45c45c, 0x400df330342a5fbbbbfc3a1c93ad9106c8f286ff12aa469c5e3b21f1b3f5fa3f75d4607c8b19affc9658efa29ca5407f8e89b971f0996ed74d44a0a68c6c44eb4b2d015c78e8abc,
  0x1714912542da3207dcf3e691f0a2d56dd240c49cc08fd2b53d79e093ae63e7b225ce8259bc5a15d1aa422fe731f3efe0eaf7188b139f6b0e0d114f064b8870ebcff39ebabd91d8, 0x6e598172c6dbe3e48ee104662472f1e66783deeea426611aab7eec6bffe0920020b8c791cb7ab587a47e4133da562772682eca0a76f17618ba6ff2b15d8ebf38958315f605d8, 0x1b1422156d81ead1dec7dcaffaa187c7f6fcb18b426057c31b3f5aa736dc461ef5f100c23684cc64e90df987ccf80346dfa3045c683bb66ef8671f07d111cb26ed3bda504fc,
  0x5658c0579f68fda32d45fbc714a5d87934521012cb6de48c07c33855f8ad8e92da0e120948c923fed5be7fcba89140b0ab83264f8b33812c8206c4b69634c89a78647789c, 0xdcd6ad1ae3174a11dc2fbb0fc5830bda622d41a0fd459d0e4d48fe662470b9f71f3958f0463169bfe86d5daf3f949086dbebf39225cd619e33688ad5a528e1610f649d0, 0x1be9fe58f30c70d2ac50a9dc15feb09e94296ac1e6fe5b0a92e01ce981d8886fc38d60c964f0eaa80cc6b611d591145bac7eef915201fcf1ff1cd9b466300a9c4024d0,
  0x2bebec45a9781951d343ae92bde49685d7a8515eb33fec6ae56fa4870a3360fa869e310113fe7f4ad8b75451f5b01f7ea117b26b5fcff4f43339f6b09181729657b3, 0x34c616a34d3be12d64d77001c27738ddd0c5d3117925717b1c39c0f945ee9d4c7713178a46ce2afca2d12098e1e08af0e39506f55c1ad911c4d8420b9af7607f4b, 0x2f6371b1a3a2466658117ab83822e68637899ff18e4558420e8c5ff667e6e1d7dc6c147f8b519a84afcb423037121bc745e0a49b0370093046ec646eade4dd62,
  0x1f030076070672867f7d33867e522bd3a093d9770b60499a34532c6ba53871f61c7ad62955e91a838a76b68e59c09221f95057b92d02cdcfe7fcfe0e79ae22, 0xe5c4580edbab0158277014e17724ed42824ee2a69ba073ee829cfabee89d750c972f98fca1d7d5365e77f8dbba22781dd48b2718d1f9304c632aa0cd8d7, 0x48b418fdf4871b0f7e712811d5ed70b86c3e62fe876dddef7aba70095222354b1fb647f287765b20640cb82fefe445184b9b5a8936be123b4ed397f1f,
  0xf13eecc73d71040df325934a4a273458d27735b1be37dbe559f4b6ff7957c1d9a7b8b4996113ce495aef64866708a3deb25a336dbeac67ec99cf18, 0x1f2ecacea685b5a6035fcb1bac3a1fae775b391e8ffda7b80c569d995b16b042052469a442ac5fee7eaa88bd6141f7704683506b8ffe5d7b2698, 0x25cd5fd10deb12910f5507d20305abc555d9e5c0fd8330c2c66c42e2b50be2ebb34d085bf68f8709b178b458e911675243389aacc01b77e7e,
  0x18e748af5ceeae5a84390c90315a88fcd78e4c4f9aff7bbb22f039c2c249e9c5ad8ec7f2f8dcc81dde308698d2dcfc22f0e70a6ccb1eae, 0x81c03f716925371468318e50c33d4639ffb70dbda2c75af53ac698d15a4a7dbaeef5a4a1190500368916e954aee82b674000fd835c, 0x12840eeb0e0ed46ef328e2889e26d9edc127c602e8e454989696a2f894cc9815e249b87dae2c7dd06a7159ef4d21e161010465c,
  0xfdac7d3000cba0efe07d5f177975d30a80b7622e98ef5d7f0a6d12b178de88d15f9cd91983461f90def5af08c6d3b8b91e, 0x424d72f8b70d95cf371deebe1646563d89f67f29db50d0e6e912e4c6007ac045252d59a7a4944b21f0a5b22b12526e, 0x3fffb85c1bbdfd505e49ad6b92f562fa20ecdf68057213a1e0930ed459a8ba3d48a501575fd7effbd0d747938,
  0x9a1ddacd8c5d42b8d3f5b9748a6354a4aee9975d67c5202a25a126013a07e735d67a7db71db80d53bb8, 0x20928433a982a562fa57bcd61ab635fea3066302d85a4c9a6834005370b0e1bb16ea5874b4195, 0x3f72d3e789858a98dd0452154d8949c0a0477cf1c0a94d14ac28f7ffb8fdced5656fd,
  0xffffffffffc36f91f919d5a51d4f78be1a870177c8e8c7128b731e64a46, 0x824a11449f8c987d51aca7934d6edbe43a8ffa868fe2306, 0x3fffffffffffffffffffffffffff89,
  0x1]

private theorem eulerianCoefficients_eq : descentCoeffs 118 = eulerianCoefficients := by
  decide +kernel

private theorem upper : upperOK (descentCoeffs 118) first gaps = true := by
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

private theorem lower (i : Fin (lastRepresentative 119 - 2)) :
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

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 119) :
    StrictNegativeInterlacing (originalQuotient 119 k) (eulerian 118) 116 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N119
