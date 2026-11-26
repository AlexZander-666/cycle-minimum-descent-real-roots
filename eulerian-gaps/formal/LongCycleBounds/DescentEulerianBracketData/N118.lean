import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentPackedData.C127L120.N118

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N118

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L120.N118 LongCycleBounds.DescentNecklace.Packed.C127L120.N118.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L120.N118 LongCycleBounds.DescentNecklace.Packed.C127L120.N118.rows

private theorem actual : RepresentativeChecks 118 previousNodes rows :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L120.N118 LongCycleBounds.DescentNecklace.Packed.C127L120.N118.dataChecks

private def first : LongCycleFinite.Dyadic := ⟨-166153499473114484112975882535043072, 0⟩

private def gaps : List Window := [
  ⟨⟨-166148111958063514138019521546420224, 0⟩, ⟨-405157333277131931648, 0⟩⟩,
  ⟨⟨-400544521358797701120, 0⟩, ⟨-427047524499456, 0⟩⟩,
  ⟨⟨-411143260602368, 0⟩, ⟨-228131340288, 0⟩⟩,
  ⟨⟨-208871096320, 0⟩, ⟨-1784291328, 0⟩⟩,
  ⟨⟨-1773977600, 0⟩, ⟨-63914368, 0⟩⟩,
  ⟨⟨-63826816, 0⟩, ⟨-5519040, 0⟩⟩,
  ⟨⟨-5515984, 0⟩, ⟨-842874, 0⟩⟩,
  ⟨⟨-842624, 0⟩, ⟨-380163, 1⟩⟩,
  ⟨⟨-190046, 0⟩, ⟨-113219, 1⟩⟩,
  ⟨⟨-452817, 3⟩, ⟨-20707, 0⟩⟩,
  ⟨⟨-331279, 4⟩, ⟨-8857, 0⟩⟩,
  ⟨⟨-141701, 4⟩, ⟨-68437, 4⟩⟩,
  ⟨⟨-136865, 5⟩, ⟨-291167, 7⟩⟩,
  ⟨⟨-18197, 3⟩, ⟨-334701, 8⟩⟩,
  ⟨⟨-167343, 7⟩, ⟨-204977, 8⟩⟩,
  ⟨⟨-204969, 8⟩, ⟨-132313, 8⟩⟩,
  ⟨⟨-264617, 9⟩, ⟨-357015, 10⟩⟩,
  ⟨⟨-357005, 10⟩, ⟨-499935, 11⟩⟩,
  ⟨⟨-249961, 10⟩, ⟨-11291, 6⟩⟩,
  ⟨⟨-361303, 11⟩, ⟨-134177, 10⟩⟩,
  ⟨⟨-268347, 11⟩, ⟨-25509, 8⟩⟩,
  ⟨⟨-408135, 12⟩, ⟨-39603, 9⟩⟩,
  ⟨⟨-316817, 12⟩, ⟨-250405, 12⟩⟩,
  ⟨⟨-250401, 12⟩, ⟨-201075, 12⟩⟩,
  ⟨⟨-402143, 13⟩, ⟨-40935, 10⟩⟩,
  ⟨⟨-163737, 12⟩, ⟨-67505, 11⟩⟩,
  ⟨⟨-4219, 7⟩, ⟨-112563, 12⟩⟩,
  ⟨⟨-225123, 13⟩, ⟨-379139, 14⟩⟩,
  ⟨⟨-189567, 13⟩, ⟨-322121, 14⟩⟩,
  ⟨⟨-80529, 12⟩, ⟨-34485, 11⟩⟩,
  ⟨⟨-275877, 14⟩, ⟨-118999, 13⟩⟩,
  ⟨⟨-475991, 15⟩, ⟨-413333, 15⟩⟩,
  ⟨⟨-413329, 15⟩, ⟨-11283, 10⟩⟩,
  ⟨⟨-90263, 13⟩, ⟨-317095, 15⟩⟩,
  ⟨⟨-79273, 13⟩, ⟨-17491, 11⟩⟩,
  ⟨⟨-279853, 15⟩, ⟨-496189, 16⟩⟩,
  ⟨⟨-496185, 16⟩, ⟨-441669, 16⟩⟩,
  ⟨⟨-441665, 16⟩, ⟨-394597, 16⟩⟩,
  ⟨⟨-197297, 15⟩, ⟨-44217, 13⟩⟩,
  ⟨⟨-88433, 14⟩, ⟨-79521, 14⟩⟩,
  ⟨⟨-318081, 16⟩, ⟨-71707, 14⟩⟩,
  ⟨⟨-286825, 16⟩, ⟨-518613, 17⟩⟩,
  ⟨⟨-518609, 17⟩, ⟨-58743, 14⟩⟩,
  ⟨⟨-117485, 15⟩, ⟨-106685, 15⟩⟩,
  ⟨⟨-426737, 17⟩, ⟨-194125, 16⟩⟩,
  ⟨⟨-388247, 17⟩, ⟨-353841, 17⟩⟩,
  ⟨⟨-176919, 16⟩, ⟨-322981, 17⟩⟩,
  ⟨⟨-161489, 16⟩, ⟨-147611, 16⟩⟩,
  ⟨⟨-73805, 15⟩, ⟨-67545, 15⟩⟩,
  ⟨⟨-135089, 16⟩, ⟨-495057, 18⟩⟩,
  ⟨⟨-495053, 18⟩, ⟨-453981, 18⟩⟩,
  ⟨⟨-226989, 17⟩, ⟨-416647, 18⟩⟩,
  ⟨⟨-416643, 18⟩, ⟨-23915, 14⟩⟩,
  ⟨⟨-382637, 18⟩, ⟨-351599, 18⟩⟩,
  ⟨⟨-87899, 16⟩, ⟨-80803, 16⟩⟩,
  ⟨⟨-161605, 17⟩, ⟨-148603, 17⟩⟩,
  ⟨⟨-74301, 16⟩, ⟨-273341, 18⟩⟩,
  ⟨⟨-273339, 18⟩, ⟨-15713, 14⟩⟩,
  ⟨⟨-125703, 17⟩, ⟨-57805, 16⟩⟩,
  ⟨⟨-462437, 19⟩, ⟨-26577, 15⟩⟩,
  ⟨⟨-425229, 19⟩, ⟨-97725, 17⟩⟩,
  ⟨⟨-390897, 19⟩, ⟨-359189, 19⟩⟩,
  ⟨⟨-359187, 19⟩, ⟨-20617, 15⟩⟩,
  ⟨⟨-329869, 19⟩, ⟨-37843, 16⟩⟩,
  ⟨⟨-302741, 19⟩, ⟨-34703, 16⟩⟩,
  ⟨⟨-277621, 19⟩, ⟨-254349, 19⟩⟩,
  ⟨⟨-254347, 19⟩, ⟨-465547, 20⟩⟩,
  ⟨⟨-58193, 17⟩, ⟨-6649, 14⟩⟩,
  ⟨⟨-425533, 20⟩, ⟨-48553, 17⟩⟩,
  ⟨⟨-388421, 20⟩, ⟨-22125, 16⟩⟩,
  ⟨⟨-353997, 20⟩, ⟨-161035, 19⟩⟩,
  ⟨⟨-322067, 20⟩, ⟨-292461, 20⟩⟩,
  ⟨⟨-146229, 19⟩, ⟨-132507, 19⟩⟩,
  ⟨⟨-66253, 18⟩, ⟨-119793, 19⟩⟩,
  ⟨⟨-7487, 15⟩, ⟨-216045, 20⟩⟩,
  ⟨⟨-432087, 21⟩, ⟨-388541, 21⟩⟩,
  ⟨⟨-388537, 21⟩, ⟨-174153, 20⟩⟩,
  ⟨⟨-348303, 21⟩, ⟨-19449, 17⟩⟩,
  ⟨⟨-311181, 21⟩, ⟨-541, 12⟩⟩,
  ⟨⟨-276989, 21⟩, ⟨-245555, 21⟩⟩,
  ⟨⟨-491105, 22⟩, ⟨-108359, 20⟩⟩,
  ⟨⟨-54179, 19⟩, ⟨-380663, 22⟩⟩,
  ⟨⟨-380659, 22⟩, ⟨-166259, 21⟩⟩,
  ⟨⟨-166257, 21⟩, ⟨-288743, 22⟩⟩,
  ⟨⟨-288739, 22⟩, ⟨-249093, 22⟩⟩,
  ⟨⟨-498181, 23⟩, ⟨-106669, 21⟩⟩,
  ⟨⟨-426671, 23⟩, ⟨-90627, 21⟩⟩,
  ⟨⟨-362503, 23⟩, ⟨-152627, 22⟩⟩,
  ⟨⟨-152625, 22⟩, ⟨-509005, 24⟩⟩,
  ⟨⟨-254499, 23⟩, ⟨-419691, 24⟩⟩,
  ⟨⟨-419685, 24⟩, ⟨-341769, 24⟩⟩,
  ⟨⟨-85441, 22⟩, ⟨-137219, 23⟩⟩,
  ⟨⟨-274433, 24⟩, ⟨-433805, 25⟩⟩,
  ⟨⟨-216899, 24⟩, ⟨-84187, 23⟩⟩,
  ⟨⟨-168371, 24⟩, ⟨-512163, 26⟩⟩,
  ⟨⟨-256077, 25⟩, ⟨-95099, 24⟩⟩,
  ⟨⟨-380389, 26⟩, ⟨-137463, 25⟩⟩,
  ⟨⟨-274919, 26⟩, ⟨-96243, 25⟩⟩,
  ⟨⟨-384963, 27⟩, ⟨-519375, 28⟩⟩,
  ⟨⟨-259681, 27⟩, ⟨-10477, 23⟩⟩,
  ⟨⟨-335255, 28⟩, ⟨-205327, 28⟩⟩,
  ⟨⟨-410641, 29⟩, ⟨-59007, 27⟩⟩,
  ⟨⟨-472041, 30⟩, ⟨-502067, 31⟩⟩,
  ⟨⟨-502049, 31⟩, ⟨-484963, 32⟩⟩,
  ⟨⟨-30309, 28⟩, ⟨-3241, 26⟩⟩,
  ⟨⟨-207415, 32⟩, ⟨-303517, 34⟩⟩,
  ⟨⟨-151751, 33⟩, ⟨-361587, 36⟩⟩,
  ⟨⟨-11299, 31⟩, ⟨-81533, 36⟩⟩,
  ⟨⟨-10191, 33⟩, ⟨-99619, 39⟩⟩,
  ⟨⟨-199225, 40⟩, ⟨-68867, 42⟩⟩,
  ⟨⟨-34431, 41⟩, ⟨-617, 40⟩⟩,
  ⟨⟨-39485, 46⟩, ⟨-333197, 56⟩⟩,
  ⟨⟨-333171, 56⟩, ⟨-355967, 67⟩⟩,
  ⟨⟨-355937, 67⟩, ⟨-12073, 82⟩⟩,
  ⟨⟨-386299, 87⟩, ⟨-262149, 135⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private def eulerianCoefficients : List ℤ := [
  0x1, 0x1fffffffffffffffffffffffffff8a, 0x2b6e05c18a8432d423398d3119cf9ea168daa8d7854c82a,
  0x3fffffffffebfb4958ca27109200e978eb5e1a4ce199ab362ca88f417da, 0xcb090c7e29ab551c5cf726fba6640df0ca70431fb2b7aac7cbd4ec051d226353f195, 0x56dc0b257edca3153579df4f7061dc78f50a017b5c59317170079b2badada792986947df9a78,
  0x1604437d5c9476526636e0b699e5bca724d72ef3bbacf6f2d0c101b4b78a87a327d7a3ef7664b496108, 0x7fff5da084f54457fdf7e6338f0c6c7f0840ccdd702cca83c2ff8ca153d6bd506faa8621bf86374c4d146cd8, 0x75dea381c1766bdfb1558d89e5f936b5b09c49fc779f685bd8fceff93c89a78c3896bbdd1a9168995e052c87a2c2e,
  0x195dbc3853e3f77f5028f24cdd52a3a279335cb3c9b0be41b525efa56f0142d72904f58f105862a83a3ce30d5a58c530f4, 0x1aeda849398f71b49de51f34b25d1d172f7305aedbdb4a73bd9bcbf51be89b594487d6b4a9acd0b41802a41d8c685c6b5a25c4, 0xacf152d018b8357fd79a14bba048f713c95da0e303974866d088764423ca6f5800dd552324ad714f126bd5a2c8bdfa60d42dbfa34,
  0x1ea0feb1f684f95650f8bb52f626c8bcdbe66a2b77893fed667eddd2171bad1e36098c947c18902861de5e3921e0aa1df3df722490a3e, 0x2b257fc0ac7c86e3310fcb33a247ab45b74d604881ecc1ad34a1658b1d92c0a6822eb513c6779362eec0a4bbbb02dde9b35af2511144bc38, 0x213048140043e1214bd0eb6798cd02bcade734ff691a8809fdd6a66f0b471e8c8a21a0b613e1dd2d75d6fa1c3886648f109c36e79898e80faa8,
  0xf06945f73caf4f14accd825edf3f8c9733d7b54c9203411999a2a1300e7f2804feff7c1eccf3d0498648cc9c515cc2b7595f45cc4bc60f96b4f58, 0x44131d388b4fee50ed5e67b49a78ee7e7fffbf1aa0ddd36cbe9d630c53c0681f3a173a7f211ec5a151a6ca86090b27a833583ae515f85b979ed9e01f, 0xcabec693e98a4eea79689d499f2fd700e6e9ae7203246dea91ec32e17b60b06d9e47e934c68602a283aeb552ee413a66a9947acb98c5c7974c7fe4db5e,
  0x19dac85eb3938de4c6a68c587735e2a4c0308bf199f878bc03f45b1404546bf38822887b2624ad9d0ffc0550704d0e0607c1c4d1dc31ca927a029e65f5e2e, 0x25692cc7e155b786b39d1029770107497ce9f60c85e3b8ac028feccf167012c987a7cbdc0dde12db8ff9e23f777c3266cd4084875a57aa7be3adf695459c5ae, 0x2786d119285b33eeb3a716da7d540e2578e213da3a3dfefffefb797901288537eb33f6b20243fc06f554c7a9fdd2d0f0e60908fb23dc925fa928ee1c68224b4b3,
  0x1f431f3ba399c61c5a47a9e30c94ef3a3d711090402db1ddc9ca0b9c14cece0dbccebe86e669481967a8bbe28afe0cab94d52b60ac9065a096c050668f7bbc215d0, 0x12e8a3e809314714e02377913a39e0b45296cb632535c363bd51a766d9fcffba0bea1c0caefc23747d7565553c0a859b95920b838425fc37d06731f641f70e0d8b1b0, 0x8e8c3ada851eab20be01b675eb450ba4fa5a32c4cc4f1bb2dc0520d9fbb28f60b888fb050b813b0fc93f336314331b4c14f1d632e52cdb58fe0c2a322c74221c05d910,
  0x352b0facb581dd183139677f708f2088300c50bdc731a6436474dd928a41d0575d532737634b3b5e9f5c456f34c954c2c0571a92a3f676cf420bac51141e79ce2120121c, 0xfebbfdef7292c4cc6411317a129674b9d2ab75c46f2c95695dd334e5a85536ec1505708c7bd5324d0a731f8bf20bbb7823e2d94e4da439b510e4bcdad6a5ec6ba86f61808, 0x3e0076cfcab00e34b8aba218ae898533b13474c33f33a1a0eba337b1af052131f871b90fc94d6f33350ac44af0629a10dd42a22b3bac75370eff4b86c9076b5ac3d6dd58868,
  0xc66d16e9529f2b1c0a0e83b7025cd4dd949aa7061327e512147d271ab528f27a0e9fd75417787a9d64bb86196b4ff798650632e2346def8cb624ae06bf77ab2fd8ebbd231308, 0x20ef56edf93a46d8f636fbd81984910531f66a8661604a0af30d2d38220ededa38f856d4973817557350b9d40789b8a71496e051801bdf256d1cbaa9bcf25a5ce46eccdf36f5dc, 0x49367c772f4e9a0c6a231a67d8e68049ce8eab1d67af559a36defd5fee54f5311219fbcb5027b2f75c9aeefe2c123d6462ee57def4c3c5764ca0dd1f9501a271d20396d692c1390,
  0x894ad082213d3d1a0518141e6645a919bb025dade85dbdffb9fcc31587810a9e2d2cdc4f23981a9aa002b69dbfaf2e01ca1b1ed17b44b6f49516331d8cf4ffe1ce9187fe54bfe330, 0xdab5501c1b365397d877ad86b6b3626a1c34d850ef13ce095102884eb28de9a8a5833fee84dcc1c695ed9a869823a51d73ad9d6299cede956487cc434f9f9bb60918767a640a0ba50, 0x129d5fac0b54797c4f7ff72e3ee0dcf810350fa597453c59793b1f070013aad1d09dade0e3c4275610ee3d4605a5caceca53a9fe8eb34a1ee009c2656cd8ab5fc08f08617e840313381,
  0x15cb2c751137c0194bae51cfdb7bbe849632b53d3642d90c7f8d073af724ea99c1a3dc018bb62f0495de135a597758a6201ec8e74ae7e95f749817d7af35af65520d72cf47c18414fe3a, 0x160cade049e6eb6072f31ae83b3c4aae59a3c5632fec64a251301ee11e01397c06234b7b6c4144f330759ce57c5e6a3743137609952c742007ac442e73b4bb9ed4dfc3c9b5d29ae05767a, 0x135e4ed91f0a32b174d11d1aee8ac42cd17d41d53f83acbcba601e5f4f5779354eab7d9be5e87e831810a6cb8fc1bd813c39e4ed9edf2b8b262cbc7ecf54f860130528a32be6cbbbdfe64a,
  0xed57cad8b9c8014b29560a9ae4b101bfb7e5b1551a860911619daec5521407eb1e76ece9b0b17b65e3dcce005e049a489a342cacf0f1baadeb9aaf721b13efa3693882e66cc8ced406f285, 0x9f1b12a59894a337f6c376eed2dc59010169b59c391071f255400ee113a4056c5f2a17813a0036437d2f3a99265f88dfecb3eb5346d77363c912f881682f27a92abc7963f1352170a35af68, 0x5daf6fb558bd477a21bd1365101ff56a8e3f9ff29629cb43b961718aadb9addeffc65ea0c00c0d0c1ea27afea6fcd5e32b87d0ae14fc8a573371235392d1233fd8215c1ae8a01dffe8e35998,
  0x309c36d88777ec9e9eead39524e959857e0ccdd054a2f5a2b2841a7984ec077daf9a3dd2e968476d945ab88e37c3c5809067127ee4344f6bd04529bbf0499fee225887582e6a124c23a97b788, 0x164a740f8bd597d62a5bc9cb5c4e96a73a89b17081400104258824d0144f81c75866d664ae1e0a0aaeae967b8c2519358e3574b71b94c41482e81a94f2449127410d488f05ea69934ae5f66a02, 0x90ed3e4283236f87632167e218cc67d7753a203f50427ee1f3d3d55f3fe1d3b707a076c88cf77427ad4f87f8a7f4f86c7d4509afc6b92e2d16810964fb280cd4388741a58cd579348165e2e48c,
  0x3450390863e0abeb6957b292b17cf2c9ffc4bcb513ce010fdab27aa91779c3d1d0ffafb1880225fdda13240a03a9f42a632ec5e4aaf0c82499ba2fe44a0f40b6860ae81dddc3a10c975877d6e7c, 0x10cfb72d4cfa05ce4990c6dbc09bf562c3df2279942d349c13f4ce77af80d01d13c3d87c94f0f4cf0a1e8578ebb61489cb208d5b2c153b8d5238dc624bb9eedcbf236fbfb6f4514ced69ec5052cc, 0x4d1c8b6b2a80355356d9fdf0204e9b4e9cb6c183b97f8e39192b7b3c46446337781edb75b2a27d3e4a0d0a2f264a4d1f3b1880c03bc626a3b16052785ff81f0be4f5fc5f9eb6b597e712443cb852,
  0x13c1bf1296b1f144cdc39e301d06a0b44c449d4910d3f3a4abb37e6dfd939e0f7439e218a0de35899d02202a36530fea24ecd0ca2e8eb91543a560b89c001cac4b36a18da5d62659678f1df797468, 0x4880f1b914440dfc9e8f6e7ed6a93a4462a11d648f4467651ed48bf36871f57c57f25b22828635fd9d3219f830850daf6a26e7315fee2f567b3cb0f1eddf74f4bf41d8caf32b3e1472285c9cc09b8, 0xee8d06e421be23cc8510491a43ed1af736239728631c9427c7e6c1cc30a8e77c1997ca670830bed648ed072422dfe27417a13f612dc6c139172eb466ea1bdb5f005d74d1d9e91e2c3bb2f912ce7c8,
  0x2c0a3b1ad2f4a50e01e73014da16a823d598782cb8664550763d4ee8a085d0ff3aa8af3b89004ef94f962314f4657f4e824c452a07c01090895010f5dfcc5383ba20e9019b60f32a08b8316cb64947, 0x74edde1d4c6b158f20c60e0f89dca6f370d84e07777993914dc36910d5b1dcc6477d2c521ecfc53081617916350bb36d3f30dc5607beb8478cfe2a36ad06e73aeb3d90b0a24ca3ca6b77e75a78cc7e, 0x1175aa516626085d76828b7861baca8828b99b1b5644a5a4b2619dda64dec74b4b5e2a2c9f359a8c40036e95d08366e5c5027d32fa8ee6d222fff415c56eefc40715025b4a34cb96fad4bf30848c32e,
  0x2591c0fa3bf5f238481bf444d29d808733d05146e8067a960aeda9df0107be8946acbb247a900982d8900c2e732127326670f8d55c6d4abd24b6627b105a210f2f3c4ccf89c71cfd37d78bd1c0b568e, 0x48df02bda38c59f07c8d11830368dff5e45eca4b3ea84aaa1ccff8b0ae4dca845501e14c2b7430d9701ea263e159fccbe4f93f712311a47b68bf784e5cab3f7fca9f45541ebceb8771ea6df25b1ea4b, 0x7f7fab0add515bbeebe1880ab917a287b50b81625bc9eafa0d94af36ecdb40876a64420132723758ed4cd19d8f30cee27344e4fb8e8153f7e4af898b1eccbfb2909e2987b1a949d9863d7c6e220aee0,
  0xc958327442aa412045383efac77b024dc2091b5e9c8c708f98356f538bf6db2139092cc7237fc946e58de192990db2cc259168df079a2913d369a0cd1d50275b75541f4564fae4f07795355b5edac20, 0x11f1ef18864146e93f9bf2ba7ebc174aab2138b98e3678fe702b6eecfc6123edd6ae37b3131910c8753dfcaf6af23fdc14381d04d84d5d78fe9bc158fe7e4a051435f3a7cf2bcf9c0834f9c8f732be60, 0x171dcd9ee853c9d69fc03adfd19a32a0d4be15a9db978e1efaab7a694d3d0d9e9a6a4d79dfb81f53e82feb9487e43c14383a736b2f15486dea1d0821462dfe2314476edfdb9bdb8ab6dfe475bfbfbf48,
  0x1ae81ebf5751e520b2e9cabd2c009742d93b6f86c5aa079d5fada9f2f17affb65e14168f26fbb6a04eb77ab99a08a534e6a020b432203cbb6373fb6c0596a31d0989408f7cacb9dcbc9419350a66b270, 0x1c4d94d9b10ffd4a00535f2297460582a2407c58733f7aaa078fec53626ae9c318744b1211a1d59681c97250ef74dda87b78ed6043f89fa05c4e183c9abe2ce4f6ff375b8219e871915703c424a106b0, 0x1ae81ebf5751e520b2e9cabd2c009742d93b6f86c5aa079d5fada9f2f17affb65e14168f26fbb6a04eb77ab99a08a534e6a020b432203cbb6373fb6c0596a31d0989408f7cacb9dcbc9419350a66b270,
  0x171dcd9ee853c9d69fc03adfd19a32a0d4be15a9db978e1efaab7a694d3d0d9e9a6a4d79dfb81f53e82feb9487e43c14383a736b2f15486dea1d0821462dfe2314476edfdb9bdb8ab6dfe475bfbfbf48, 0x11f1ef18864146e93f9bf2ba7ebc174aab2138b98e3678fe702b6eecfc6123edd6ae37b3131910c8753dfcaf6af23fdc14381d04d84d5d78fe9bc158fe7e4a051435f3a7cf2bcf9c0834f9c8f732be60, 0xc958327442aa412045383efac77b024dc2091b5e9c8c708f98356f538bf6db2139092cc7237fc946e58de192990db2cc259168df079a2913d369a0cd1d50275b75541f4564fae4f07795355b5edac20,
  0x7f7fab0add515bbeebe1880ab917a287b50b81625bc9eafa0d94af36ecdb40876a64420132723758ed4cd19d8f30cee27344e4fb8e8153f7e4af898b1eccbfb2909e2987b1a949d9863d7c6e220aee0, 0x48df02bda38c59f07c8d11830368dff5e45eca4b3ea84aaa1ccff8b0ae4dca845501e14c2b7430d9701ea263e159fccbe4f93f712311a47b68bf784e5cab3f7fca9f45541ebceb8771ea6df25b1ea4b, 0x2591c0fa3bf5f238481bf444d29d808733d05146e8067a960aeda9df0107be8946acbb247a900982d8900c2e732127326670f8d55c6d4abd24b6627b105a210f2f3c4ccf89c71cfd37d78bd1c0b568e,
  0x1175aa516626085d76828b7861baca8828b99b1b5644a5a4b2619dda64dec74b4b5e2a2c9f359a8c40036e95d08366e5c5027d32fa8ee6d222fff415c56eefc40715025b4a34cb96fad4bf30848c32e, 0x74edde1d4c6b158f20c60e0f89dca6f370d84e07777993914dc36910d5b1dcc6477d2c521ecfc53081617916350bb36d3f30dc5607beb8478cfe2a36ad06e73aeb3d90b0a24ca3ca6b77e75a78cc7e, 0x2c0a3b1ad2f4a50e01e73014da16a823d598782cb8664550763d4ee8a085d0ff3aa8af3b89004ef94f962314f4657f4e824c452a07c01090895010f5dfcc5383ba20e9019b60f32a08b8316cb64947,
  0xee8d06e421be23cc8510491a43ed1af736239728631c9427c7e6c1cc30a8e77c1997ca670830bed648ed072422dfe27417a13f612dc6c139172eb466ea1bdb5f005d74d1d9e91e2c3bb2f912ce7c8, 0x4880f1b914440dfc9e8f6e7ed6a93a4462a11d648f4467651ed48bf36871f57c57f25b22828635fd9d3219f830850daf6a26e7315fee2f567b3cb0f1eddf74f4bf41d8caf32b3e1472285c9cc09b8, 0x13c1bf1296b1f144cdc39e301d06a0b44c449d4910d3f3a4abb37e6dfd939e0f7439e218a0de35899d02202a36530fea24ecd0ca2e8eb91543a560b89c001cac4b36a18da5d62659678f1df797468,
  0x4d1c8b6b2a80355356d9fdf0204e9b4e9cb6c183b97f8e39192b7b3c46446337781edb75b2a27d3e4a0d0a2f264a4d1f3b1880c03bc626a3b16052785ff81f0be4f5fc5f9eb6b597e712443cb852, 0x10cfb72d4cfa05ce4990c6dbc09bf562c3df2279942d349c13f4ce77af80d01d13c3d87c94f0f4cf0a1e8578ebb61489cb208d5b2c153b8d5238dc624bb9eedcbf236fbfb6f4514ced69ec5052cc, 0x3450390863e0abeb6957b292b17cf2c9ffc4bcb513ce010fdab27aa91779c3d1d0ffafb1880225fdda13240a03a9f42a632ec5e4aaf0c82499ba2fe44a0f40b6860ae81dddc3a10c975877d6e7c,
  0x90ed3e4283236f87632167e218cc67d7753a203f50427ee1f3d3d55f3fe1d3b707a076c88cf77427ad4f87f8a7f4f86c7d4509afc6b92e2d16810964fb280cd4388741a58cd579348165e2e48c, 0x164a740f8bd597d62a5bc9cb5c4e96a73a89b17081400104258824d0144f81c75866d664ae1e0a0aaeae967b8c2519358e3574b71b94c41482e81a94f2449127410d488f05ea69934ae5f66a02, 0x309c36d88777ec9e9eead39524e959857e0ccdd054a2f5a2b2841a7984ec077daf9a3dd2e968476d945ab88e37c3c5809067127ee4344f6bd04529bbf0499fee225887582e6a124c23a97b788,
  0x5daf6fb558bd477a21bd1365101ff56a8e3f9ff29629cb43b961718aadb9addeffc65ea0c00c0d0c1ea27afea6fcd5e32b87d0ae14fc8a573371235392d1233fd8215c1ae8a01dffe8e35998, 0x9f1b12a59894a337f6c376eed2dc59010169b59c391071f255400ee113a4056c5f2a17813a0036437d2f3a99265f88dfecb3eb5346d77363c912f881682f27a92abc7963f1352170a35af68, 0xed57cad8b9c8014b29560a9ae4b101bfb7e5b1551a860911619daec5521407eb1e76ece9b0b17b65e3dcce005e049a489a342cacf0f1baadeb9aaf721b13efa3693882e66cc8ced406f285,
  0x135e4ed91f0a32b174d11d1aee8ac42cd17d41d53f83acbcba601e5f4f5779354eab7d9be5e87e831810a6cb8fc1bd813c39e4ed9edf2b8b262cbc7ecf54f860130528a32be6cbbbdfe64a, 0x160cade049e6eb6072f31ae83b3c4aae59a3c5632fec64a251301ee11e01397c06234b7b6c4144f330759ce57c5e6a3743137609952c742007ac442e73b4bb9ed4dfc3c9b5d29ae05767a, 0x15cb2c751137c0194bae51cfdb7bbe849632b53d3642d90c7f8d073af724ea99c1a3dc018bb62f0495de135a597758a6201ec8e74ae7e95f749817d7af35af65520d72cf47c18414fe3a,
  0x129d5fac0b54797c4f7ff72e3ee0dcf810350fa597453c59793b1f070013aad1d09dade0e3c4275610ee3d4605a5caceca53a9fe8eb34a1ee009c2656cd8ab5fc08f08617e840313381, 0xdab5501c1b365397d877ad86b6b3626a1c34d850ef13ce095102884eb28de9a8a5833fee84dcc1c695ed9a869823a51d73ad9d6299cede956487cc434f9f9bb60918767a640a0ba50, 0x894ad082213d3d1a0518141e6645a919bb025dade85dbdffb9fcc31587810a9e2d2cdc4f23981a9aa002b69dbfaf2e01ca1b1ed17b44b6f49516331d8cf4ffe1ce9187fe54bfe330,
  0x49367c772f4e9a0c6a231a67d8e68049ce8eab1d67af559a36defd5fee54f5311219fbcb5027b2f75c9aeefe2c123d6462ee57def4c3c5764ca0dd1f9501a271d20396d692c1390, 0x20ef56edf93a46d8f636fbd81984910531f66a8661604a0af30d2d38220ededa38f856d4973817557350b9d40789b8a71496e051801bdf256d1cbaa9bcf25a5ce46eccdf36f5dc, 0xc66d16e9529f2b1c0a0e83b7025cd4dd949aa7061327e512147d271ab528f27a0e9fd75417787a9d64bb86196b4ff798650632e2346def8cb624ae06bf77ab2fd8ebbd231308,
  0x3e0076cfcab00e34b8aba218ae898533b13474c33f33a1a0eba337b1af052131f871b90fc94d6f33350ac44af0629a10dd42a22b3bac75370eff4b86c9076b5ac3d6dd58868, 0xfebbfdef7292c4cc6411317a129674b9d2ab75c46f2c95695dd334e5a85536ec1505708c7bd5324d0a731f8bf20bbb7823e2d94e4da439b510e4bcdad6a5ec6ba86f61808, 0x352b0facb581dd183139677f708f2088300c50bdc731a6436474dd928a41d0575d532737634b3b5e9f5c456f34c954c2c0571a92a3f676cf420bac51141e79ce2120121c,
  0x8e8c3ada851eab20be01b675eb450ba4fa5a32c4cc4f1bb2dc0520d9fbb28f60b888fb050b813b0fc93f336314331b4c14f1d632e52cdb58fe0c2a322c74221c05d910, 0x12e8a3e809314714e02377913a39e0b45296cb632535c363bd51a766d9fcffba0bea1c0caefc23747d7565553c0a859b95920b838425fc37d06731f641f70e0d8b1b0, 0x1f431f3ba399c61c5a47a9e30c94ef3a3d711090402db1ddc9ca0b9c14cece0dbccebe86e669481967a8bbe28afe0cab94d52b60ac9065a096c050668f7bbc215d0,
  0x2786d119285b33eeb3a716da7d540e2578e213da3a3dfefffefb797901288537eb33f6b20243fc06f554c7a9fdd2d0f0e60908fb23dc925fa928ee1c68224b4b3, 0x25692cc7e155b786b39d1029770107497ce9f60c85e3b8ac028feccf167012c987a7cbdc0dde12db8ff9e23f777c3266cd4084875a57aa7be3adf695459c5ae, 0x19dac85eb3938de4c6a68c587735e2a4c0308bf199f878bc03f45b1404546bf38822887b2624ad9d0ffc0550704d0e0607c1c4d1dc31ca927a029e65f5e2e,
  0xcabec693e98a4eea79689d499f2fd700e6e9ae7203246dea91ec32e17b60b06d9e47e934c68602a283aeb552ee413a66a9947acb98c5c7974c7fe4db5e, 0x44131d388b4fee50ed5e67b49a78ee7e7fffbf1aa0ddd36cbe9d630c53c0681f3a173a7f211ec5a151a6ca86090b27a833583ae515f85b979ed9e01f, 0xf06945f73caf4f14accd825edf3f8c9733d7b54c9203411999a2a1300e7f2804feff7c1eccf3d0498648cc9c515cc2b7595f45cc4bc60f96b4f58,
  0x213048140043e1214bd0eb6798cd02bcade734ff691a8809fdd6a66f0b471e8c8a21a0b613e1dd2d75d6fa1c3886648f109c36e79898e80faa8, 0x2b257fc0ac7c86e3310fcb33a247ab45b74d604881ecc1ad34a1658b1d92c0a6822eb513c6779362eec0a4bbbb02dde9b35af2511144bc38, 0x1ea0feb1f684f95650f8bb52f626c8bcdbe66a2b77893fed667eddd2171bad1e36098c947c18902861de5e3921e0aa1df3df722490a3e,
  0xacf152d018b8357fd79a14bba048f713c95da0e303974866d088764423ca6f5800dd552324ad714f126bd5a2c8bdfa60d42dbfa34, 0x1aeda849398f71b49de51f34b25d1d172f7305aedbdb4a73bd9bcbf51be89b594487d6b4a9acd0b41802a41d8c685c6b5a25c4, 0x195dbc3853e3f77f5028f24cdd52a3a279335cb3c9b0be41b525efa56f0142d72904f58f105862a83a3ce30d5a58c530f4,
  0x75dea381c1766bdfb1558d89e5f936b5b09c49fc779f685bd8fceff93c89a78c3896bbdd1a9168995e052c87a2c2e, 0x7fff5da084f54457fdf7e6338f0c6c7f0840ccdd702cca83c2ff8ca153d6bd506faa8621bf86374c4d146cd8, 0x1604437d5c9476526636e0b699e5bca724d72ef3bbacf6f2d0c101b4b78a87a327d7a3ef7664b496108,
  0x56dc0b257edca3153579df4f7061dc78f50a017b5c59317170079b2badada792986947df9a78, 0xcb090c7e29ab551c5cf726fba6640df0ca70431fb2b7aac7cbd4ec051d226353f195, 0x3fffffffffebfb4958ca27109200e978eb5e1a4ce199ab362ca88f417da,
  0x2b6e05c18a8432d423398d3119cf9ea168daa8d7854c82a, 0x1fffffffffffffffffffffffffff8a, 0x1]

private theorem eulerianCoefficients_eq : descentCoeffs 117 = eulerianCoefficients := by
  decide +kernel

private theorem upper : upperOK (descentCoeffs 117) first gaps = true := by
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

private theorem lower (i : Fin (lastRepresentative 118 - 2)) :
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

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 118) :
    StrictNegativeInterlacing (originalQuotient 118 k) (eulerian 117) 115 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N118
