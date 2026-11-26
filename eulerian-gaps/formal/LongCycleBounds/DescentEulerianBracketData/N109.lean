import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentPackedData.C127L112.N109

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N109

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L112.N109 LongCycleBounds.DescentNecklace.Packed.C127L112.N109.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L112.N109 LongCycleBounds.DescentNecklace.Packed.C127L112.N109.rows

private theorem actual : RepresentativeChecks 109 previousNodes rows :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L112.N109 LongCycleBounds.DescentNecklace.Packed.C127L112.N109.dataChecks

private def first : LongCycleFinite.Dyadic := ⟨-324518553658426726783156020576256, 0⟩

private def gaps : List Window := [
  ⟨⟨-324508031168092801050819378020352, 0⟩, ⟨-15520283925220950016, 0⟩⟩,
  ⟨⟨-6297035033668485120, 0⟩, ⟨-31138512896000, 0⟩⟩,
  ⟨⟨-30763105910784, 0⟩, ⟨-30147608576, 0⟩⟩,
  ⟨⟨-28729475072, 0⟩, ⟨-343485440, 0⟩⟩,
  ⟨⟨-342094848, 0⟩, ⟨-15757408, 0⟩⟩,
  ⟨⟨-15740800, 0⟩, ⟨-1634252, 0⟩⟩,
  ⟨⟨-1633512, 0⟩, ⟨-286683, 0⟩⟩,
  ⟨⟨-286610, 0⟩, ⟨-288325, 2⟩⟩,
  ⟨⟨-144139, 1⟩, ⟨-375009, 4⟩⟩,
  ⟨⟨-374965, 4⟩, ⟨-147443, 4⟩⟩,
  ⟨⟨-73715, 3⟩, ⟨-267897, 6⟩⟩,
  ⟨⟨-133939, 5⟩, ⟨-136125, 6⟩⟩,
  ⟨⟨-272235, 7⟩, ⟨-151217, 7⟩⟩,
  ⟨⟨-302419, 8⟩, ⟨-180463, 8⟩⟩,
  ⟨⟨-360911, 9⟩, ⟨-456739, 10⟩⟩,
  ⟨⟨-456723, 10⟩, ⟨-151683, 9⟩⟩,
  ⟨⟨-75839, 8⟩, ⟨-419691, 11⟩⟩,
  ⟨⟨-13115, 6⟩, ⟨-300451, 11⟩⟩,
  ⟨⟨-75111, 9⟩, ⟨-110739, 10⟩⟩,
  ⟨⟨-221473, 11⟩, ⟨-334831, 12⟩⟩,
  ⟨⟨-41853, 9⟩, ⟨-32333, 9⟩⟩,
  ⟨⟨-258659, 12⟩, ⟨-101819, 11⟩⟩,
  ⟨⟨-407269, 13⟩, ⟨-325991, 13⟩⟩,
  ⟨⟨-162993, 12⟩, ⟨-264755, 13⟩⟩,
  ⟨⟨-132375, 12⟩, ⟨-108903, 12⟩⟩,
  ⟨⟨-217803, 13⟩, ⟨-362475, 14⟩⟩,
  ⟨⟨-362469, 14⟩, ⟨-152349, 13⟩⟩,
  ⟨⟨-152347, 13⟩, ⟨-8077, 9⟩⟩,
  ⟨⟨-516921, 15⟩, ⟨-110517, 13⟩⟩,
  ⟨⟨-221031, 14⟩, ⟨-190409, 14⟩⟩,
  ⟨⟨-380813, 15⟩, ⟨-330215, 15⟩⟩,
  ⟨⟨-330211, 15⟩, ⟨-288037, 15⟩⟩,
  ⟨⟨-144017, 14⟩, ⟨-505183, 16⟩⟩,
  ⟨⟨-252589, 15⟩, ⟨-445167, 16⟩⟩,
  ⟨⟨-445163, 16⟩, ⟨-98499, 14⟩⟩,
  ⟨⟨-49249, 13⟩, ⟨-43761, 13⟩⟩,
  ⟨⟨-87521, 14⟩, ⟨-312189, 16⟩⟩,
  ⟨⟨-156093, 15⟩, ⟨-1091, 8⟩⟩,
  ⟨⟨-279293, 16⟩, ⟨-31325, 13⟩⟩,
  ⟨⟨-125299, 15⟩, ⟨-225445, 16⟩⟩,
  ⟨⟨-225443, 16⟩, ⟨-203297, 16⟩⟩,
  ⟨⟨-203295, 16⟩, ⟨-45929, 14⟩⟩,
  ⟨⟨-367429, 17⟩, ⟨-332671, 17⟩⟩,
  ⟨⟨-83167, 15⟩, ⟨-150853, 16⟩⟩,
  ⟨⟨-301703, 17⟩, ⟨-17127, 13⟩⟩,
  ⟨⟨-274029, 17⟩, ⟨-1947, 10⟩⟩,
  ⟨⟨-124607, 16⟩, ⟨-226901, 17⟩⟩,
  ⟨⟨-226899, 17⟩, ⟨-413555, 18⟩⟩,
  ⟨⟨-25847, 14⟩, ⟨-94293, 16⟩⟩,
  ⟨⟨-377169, 18⟩, ⟨-344197, 18⟩⟩,
  ⟨⟨-344195, 18⟩, ⟨-78563, 16⟩⟩,
  ⟨⟨-314249, 18⟩, ⟨-286997, 18⟩⟩,
  ⟨⟨-286995, 18⟩, ⟨-131073, 17⟩⟩,
  ⟨⟨-524287, 19⟩, ⟨-239445, 18⟩⟩,
  ⟨⟨-478887, 19⟩, ⟨-109339, 17⟩⟩,
  ⟨⟨-437353, 19⟩, ⟨-199653, 18⟩⟩,
  ⟨⟨-399303, 19⟩, ⟨-364397, 19⟩⟩,
  ⟨⟨-182197, 18⟩, ⟨-166169, 18⟩⟩,
  ⟨⟨-332335, 19⟩, ⟨-302863, 19⟩⟩,
  ⟨⟨-75715, 17⟩, ⟨-8617, 14⟩⟩,
  ⟨⟨-275741, 19⟩, ⟨-250775, 19⟩⟩,
  ⟨⟨-250773, 19⟩, ⟨-227771, 19⟩⟩,
  ⟨⟨-227769, 19⟩, ⟨-206571, 19⟩⟩,
  ⟨⟨-413139, 20⟩, ⟨-374057, 20⟩⟩,
  ⟨⟨-374053, 20⟩, ⟨-84507, 18⟩⟩,
  ⟨⟨-338025, 20⟩, ⟨-304819, 20⟩⟩,
  ⟨⟨-19051, 16⟩, ⟨-274223, 20⟩⟩,
  ⟨⟨-68555, 18⟩, ⟨-246047, 20⟩⟩,
  ⟨⟨-246045, 20⟩, ⟨-220123, 20⟩⟩,
  ⟨⟨-220121, 20⟩, ⟨-98147, 19⟩⟩,
  ⟨⟨-49073, 18⟩, ⟨-348839, 21⟩⟩,
  ⟨⟨-87209, 19⟩, ⟨-308741, 21⟩⟩,
  ⟨⟨-308737, 21⟩, ⟨-68015, 19⟩⟩,
  ⟨⟨-272057, 21⟩, ⟨-119291, 20⟩⟩,
  ⟨⟨-477159, 22⟩, ⟨-416215, 22⟩⟩,
  ⟨⟨-208105, 21⟩, ⟨-360909, 22⟩⟩,
  ⟨⟨-360905, 22⟩, ⟨-155453, 21⟩⟩,
  ⟨⟨-155451, 21⟩, ⟨-33235, 19⟩⟩,
  ⟨⟨-265877, 22⟩, ⟨-881, 14⟩⟩,
  ⟨⟨-451067, 23⟩, ⟨-379173, 23⟩⟩,
  ⟨⟨-11849, 18⟩, ⟨-157757, 22⟩⟩,
  ⟨⟨-157755, 22⟩, ⟨-64891, 21⟩⟩,
  ⟨⟨-519121, 24⟩, ⟨-52701, 21⟩⟩,
  ⟨⟨-421601, 24⟩, ⟨-337461, 24⟩⟩,
  ⟨⟨-21091, 20⟩, ⟨-66419, 22⟩⟩,
  ⟨⟨-265671, 24⟩, ⟨-410483, 25⟩⟩,
  ⟨⟨-410475, 25⟩, ⟨-19393, 21⟩⟩,
  ⟨⟨-155141, 24⟩, ⟨-228727, 25⟩⟩,
  ⟨⟨-457445, 26⟩, ⟨-327487, 26⟩⟩,
  ⟨⟨-327479, 26⟩, ⟨-453061, 27⟩⟩,
  ⟨⟨-226525, 26⟩, ⟨-300921, 27⟩⟩,
  ⟨⟨-300913, 27⟩, ⟨-190405, 27⟩⟩,
  ⟨⟨-380799, 28⟩, ⟨-227233, 28⟩⟩,
  ⟨⟨-113613, 27⟩, ⟨-504839, 30⟩⟩,
  ⟨⟨-252411, 29⟩, ⟨-128267, 29⟩⟩,
  ⟨⟨-64131, 28⟩, ⟨-29131, 28⟩⟩,
  ⟨⟨-116519, 30⟩, ⟨-366521, 33⟩⟩,
  ⟨⟨-366503, 33⟩, ⟨-476719, 35⟩⟩,
  ⟨⟨-238347, 34⟩, ⟨-119875, 35⟩⟩,
  ⟨⟨-29967, 33⟩, ⟨-336563, 39⟩⟩,
  ⟨⟨-336541, 39⟩, ⟨-139589, 41⟩⟩,
  ⟨⟨-139579, 41⟩, ⟨-205439, 46⟩⟩,
  ⟨⟨-410847, 47⟩, ⟨-19461, 49⟩⟩,
  ⟨⟨-311351, 53⟩, ⟨-296435, 63⟩⟩,
  ⟨⟨-148205, 62⟩, ⟨-464105, 82⟩⟩,
  ⟨⟨-464061, 82⟩, ⟨-262165, 126⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private def eulerianCoefficients : List ℤ := [
  0x1, 0xfffffffffffffffffffffffff93, 0x909a469765f53023d38d5a7231073a03433cc33f66f,
  0xfffffffffc26e4ff189969a6953ecd07d611fec4c9c5f20de6a8d5, 0x6d00f72b3d3846f50103f2c71d6085ba5977e16dab643091c7036b8a3b2ac62, 0x909a43b0cf614294c429f596cc7b03869c937a9dfbbcb3a8ff182ad30abb1b3089f266,
  0x9274b4b1c29b580c4901939f432272a6c42921da48152be4c7eb12ba4cfd63c887475aa218c6, 0xfffc1a441d6037d9efb60b6ba361ab4aeac754a532838921d6cbe84be031748904b9bd1475c93d982, 0x51a71c707bacb1e18aa7acf9d94d50b9fb70d2008165754a8b8b08b431d006e4798101a6346f8e549e4a79,
  0x6cde3194451839c66efa701395d94f7cef63adc7bae2b8592fdc299e912864df154f2d2f2d2bd6a462df72f89b, 0x30f39daf28896c4d8d04d030f64040a7b873a5bcca450b9cde2cbce2cb59335c74e475c55423637e7c1a7d8a7318ef, 0x8f4c2b8c714d637339a07334800eeffdb9a35959a70fc59db67e8a94ef05cf174f0c770a9254441171204c702d0977c35,
  0xc4ac68dcab6377be10907a0db3216706289d825e79a50a5d8498b97e6374db0aba1099d0a1cdccb84a9fb69bdab683c984a8, 0x8d2bf59ee020857556272d52c5def7cba0b1ad85d4e65cbb5442bda741ad87af7fe619e1f8da9a2be96fc8d35394f14fb9ab3f8, 0x39be642288f5a3d125b07c9d9f5a60ad19293f259a0e1f6b041e848c6cad8cdac882a1f4ab2c847c1ee7d0365798f1e7081944af38,
  0xe698b319380a274a414e97771c09a63f870db9427f1bf65c94dda76a7466ed170fe6312c3c8c2edf8202814cd835d8722164c7c20268, 0x251e2da28ed1613b747332b82345d1893fec623090733c2d5a3c2f67b30103dd15547aebdd98bb91ce377079185b6cb6d9f2ff3339d6496, 0x4082259e1e430b55a07e3a377e08bd2b96cb83aeb262938ce0868c4721658f17d932501af1a081f0d2aae108c3b052e42377306fbbd5cbda2,
  0x4e8c235c31ae80e6a4253598b7fbcb58e88f4632f43882c7cfb20564ef212756c9b09296b8f2f6d59866c4b718a2239f8bfa4c761d6d4d24a2a, 0x45258ea3117713cf069dfb80407e366e4af8b112f75a5b3abbab53cc83eaef6d5702867e08529c4cbecd9a27fcbdda11ce5af66aa783b709a5dae, 0x2d3112ca00ad2248409f97c85c762b7fc65cb7f16a2e3a977e7370edb71e7538652c058280d6cfea1cc3a672f7686256578d50437e69a2736fa04e4,
  0x166dd89aaaf666c966a478f6e5f12f6da85044b5d6ae0a7f409fd58944c3b42c3add9af60a8a19a75240dd6c95bbbef0cace5acf26990a03153c98e2c, 0x89e7c7d5073f5bc3d07025bf56ede9c2b9eecc57103efdfa990966e1a0391686fe99866b84d22d85f8f7c1d0fda830389c4b615f9f049e7bbecd00ceac, 0x29ba24a40a1f1b71ce9670070dcec713768174543a6a2212441ced00fed9534ae5bd365db7793c9eed41bfee44ac832b027fe816306efebe5df57a393e64,
  0xa166e12eb0b17c8dd193eeeae1ca04ca762deb6ea3d6017c7ab4a0ebee9582b20e3e4ce83a5041ca18a8e686b19d7b8501a9a94eecac2040899c6c5b11f1e, 0x1f93a26c1736c9a641d5faa4996d0631417ad3c36ceefe8968e4eb04413c8c7f823c8935e8c9c2f51ae970ca08e1527946e5d4f1741a8af93face7bb7eb497a, 0x50e51b16680ea5dca85c1fced8174abcfc9e000d3048de2215afae441a2bdef36cae229465fd782280bd39d783433c04c44e434dd369e2a03e010573f3015c32,
  0xab4e9aa4467a09b67fb9d8686d3605befb28b24d34ffa0738aa4a3f20b1fa303cd7dec1136a8200e641ba62edc63b4041511920717d3254f4349b1170c980efc6, 0x12e875d1b58eb9f1a4788f4e2f441282542f73de7a267ff5e56049ef6468db7d3d84ae8334189d7763be96fc8da5b8911154fab45993ffd09a44c4c1bcae2a131c8, 0x1c112c04b7df19b7bb59e01ffd7762b8cde1f909de6aaaf59eec51afaeb138daf8230915d0cc69a4bf36ebc39779114c2392297ce034127d5ff121407c6eaa421558,
  0x2344514634d692f28a3cd96395c4d5b4419b7461bd6116b47e41a2e308736a6a3e2d2b3e236eb204c549479ad24a7204669c7b367482bc84a90a51e988ca4c2709118, 0x25bfa2f16b2a9e03437c50c4834cfd92f69975519b5193a7ad3d6af71819f0b1c03e3bbea36994307a7d10402ba63c9db5a1d2462804009c188670a591823df05da908, 0x229d7edce946c4755a324d9b16b22d52fca6e72815fd8433a6baf4be45d3b2dd19ecbec3b2da09a998bee18c0ef328c58114060aa38b2a14c2cce6c60ee92d56111fad3,
  0x1b554ea0cc1793be99e6cbe34a591e6bce14abe50212ad1ece69e9e4b3457271ab53941aee4270959af9ee7bd08f6bcc0078c3c7380a386edcf0ca6ee519408bb9ab99a9, 0x12abec72789a3bf350a0b2f91de5302c1a4002c616ea0a6135fa5b5b08d6bae2d3e7bc66510c552616cae3fb4285ce2d745f1b0bc57ebc96e6d0d0c3640ba616dd2c40a9d, 0xb14911d142224ac3186af366c14cec6d4b82e9e6e3d1f530cd47f49b9ee24e33247ae9bc001514df87d34f1bcf7bdd752bd013a166736e5e46cf358a0fbaae0aab4c1046f,
  0x5bbe12c169a2f2c5989a17f5c501529a97733f7ca55e92fd5c22c365deb0d579ff0c889dec320fed29af44a3ad83de6617fdb920f1dbce3731a9e3eb57f8e6e92fc5e4b61e, 0x298a9884ff2359428ec49d83cb55e7975b33a2f64014e25389d307947b43a2d52f8ac0ee4b6fb40069597e85f5aea43edcb0495f7cde4b71eac9ae0c8b35214fabb3da11c1a, 0x10829b6d10053f4750654b58700414e09ec06f3e5abc1345f848f6f52aabd6c8c73a1b5d007c36e56585ec346fd9fad27e3a9ba6228ae00a5f33c5b01fa1f2cc8281c6c9c7fa,
  0x5c692497ac801c7d9489007bdfe797fe48d0584958988c599804553f298d0cdc9c47baa1974561726c00dbc20483cdd2cae231648faa53c835273d89e7c62b58e229f8279bbe, 0x1c86e302422526468129927049d26c75c6222862187ce1c3d4cf49b0e5f408b8cd873e64d3843e9950abacdb86b886e045d6ebb7a304232372e7ae09903be150157f3bd5808a3, 0x7c9e6b2ca0bca899c21042b5319d7d25108c7f729e76b337bf6e8692b067e42e15f90e1c9a07d0bceccbe65f970f9240d15effd7ded21e9e9a0c251185455e99851db61330979,
  0x1e27c9820e24d1ca971dca5d6e274db17991084d786aea480783eb9781584b152d76b9c519110141269000a34fc127f3b5171434577f5604a230c8264521b757d496cb09bda475, 0x67aaf1c212f33d7934cc411a7c6621ba081cbcb482b7c1da052d42ae2f9cc9c6d6f279e607c36ed5b98fd9d7b121c00dba1be3536b512e6e3433e0077ad9f5b9810f0d21e28bd7, 0x13cf81614ed6fedabb837f398178686c0b0e5f264cb83cf94ef40ed0fc97adf8f77aeb19de530dab9a8f7c78079b0c0f23fc9cb31b08c527cc369b8eeb76e265025f9fc7a19b450,
  0x35f391d65a003574d9fd953371215b301677895895455ee0ad1bd7d99eb23859651917b93da42623d9b1cf040ad7ca7e899718f44798d0a92b175f0bf69b0f28ccb545627e090f0, 0x830a49ba774af9878257ac656882d93b5d13f7d70a7129fc5937896177248565b0f828d6f5569660f2cf7e3ed499128ddac0a9b15f487e40239fdb5da8542786f88c0c0c043f570, 0x11c2dd161eb7f1bcc7c38eb2ade01ceae0c592decc79fa96ca47a3e61e81b4cfc86ca32f7d0beb2034c01b6c30f73ad072b56afc1941825463184cf8b3e61846362c28a5614019d0,
  0x226cad4db243a9df28b2505322ce0a7c11750b7e586327ae3ff3031933fcf6d1e6b48c19781fb85b63c9f926b8c76d0bf4272fe46dfc955a53569f483b21a5187a7d1e23303b08c4, 0x3bae19b061c0ff46a7bd5e26aaf5776012f2b22446cf3cde636efd2f0e4bb9d7ba91673f2a85d7497235e1e00efddbe0918479a6bd95bb1bd3a93f1cdadc4cc2ffe723fc2872af8c, 0x5c9bc2ff0489a5e0814f910fe423036a03acaf0624b15059aef18d680687ef9deaed310441feb1c8e30217dc1e482a9e3e88d1d5e8aa2d24c6ca5d6c87dc7f2f42e38d4db6f7493c,
  0x80b2229bea12a9afad2f9383186bb61b4f3f49be9b8c0ae0b169df47cddf3c23d1127cca2ad422b57d0e08ac2dec8f9556458212b72ef282de8099a082a479e5f1de0c51c23122d4, 0xa03af4fc64d631c46ad545dfe58c928b6850f6f3829ccb62916214794452777ca3d5fe9fcf3e7096068589580d5e2c878d80f819ae9f54651bdfbc50b3cd00f32b9a22e44895b4f8, 0xb2c65266b48b2a8d399c8c41cf23dd15df695c6677e117fef942bd95cd8d0841cf4cb06c5a69c7b32a1783d3888cbe2c509e85422341e94e31b289b03187fbf67e5f64689be823e8,
  0xb2c65266b48b2a8d399c8c41cf23dd15df695c6677e117fef942bd95cd8d0841cf4cb06c5a69c7b32a1783d3888cbe2c509e85422341e94e31b289b03187fbf67e5f64689be823e8, 0xa03af4fc64d631c46ad545dfe58c928b6850f6f3829ccb62916214794452777ca3d5fe9fcf3e7096068589580d5e2c878d80f819ae9f54651bdfbc50b3cd00f32b9a22e44895b4f8, 0x80b2229bea12a9afad2f9383186bb61b4f3f49be9b8c0ae0b169df47cddf3c23d1127cca2ad422b57d0e08ac2dec8f9556458212b72ef282de8099a082a479e5f1de0c51c23122d4,
  0x5c9bc2ff0489a5e0814f910fe423036a03acaf0624b15059aef18d680687ef9deaed310441feb1c8e30217dc1e482a9e3e88d1d5e8aa2d24c6ca5d6c87dc7f2f42e38d4db6f7493c, 0x3bae19b061c0ff46a7bd5e26aaf5776012f2b22446cf3cde636efd2f0e4bb9d7ba91673f2a85d7497235e1e00efddbe0918479a6bd95bb1bd3a93f1cdadc4cc2ffe723fc2872af8c, 0x226cad4db243a9df28b2505322ce0a7c11750b7e586327ae3ff3031933fcf6d1e6b48c19781fb85b63c9f926b8c76d0bf4272fe46dfc955a53569f483b21a5187a7d1e23303b08c4,
  0x11c2dd161eb7f1bcc7c38eb2ade01ceae0c592decc79fa96ca47a3e61e81b4cfc86ca32f7d0beb2034c01b6c30f73ad072b56afc1941825463184cf8b3e61846362c28a5614019d0, 0x830a49ba774af9878257ac656882d93b5d13f7d70a7129fc5937896177248565b0f828d6f5569660f2cf7e3ed499128ddac0a9b15f487e40239fdb5da8542786f88c0c0c043f570, 0x35f391d65a003574d9fd953371215b301677895895455ee0ad1bd7d99eb23859651917b93da42623d9b1cf040ad7ca7e899718f44798d0a92b175f0bf69b0f28ccb545627e090f0,
  0x13cf81614ed6fedabb837f398178686c0b0e5f264cb83cf94ef40ed0fc97adf8f77aeb19de530dab9a8f7c78079b0c0f23fc9cb31b08c527cc369b8eeb76e265025f9fc7a19b450, 0x67aaf1c212f33d7934cc411a7c6621ba081cbcb482b7c1da052d42ae2f9cc9c6d6f279e607c36ed5b98fd9d7b121c00dba1be3536b512e6e3433e0077ad9f5b9810f0d21e28bd7, 0x1e27c9820e24d1ca971dca5d6e274db17991084d786aea480783eb9781584b152d76b9c519110141269000a34fc127f3b5171434577f5604a230c8264521b757d496cb09bda475,
  0x7c9e6b2ca0bca899c21042b5319d7d25108c7f729e76b337bf6e8692b067e42e15f90e1c9a07d0bceccbe65f970f9240d15effd7ded21e9e9a0c251185455e99851db61330979, 0x1c86e302422526468129927049d26c75c6222862187ce1c3d4cf49b0e5f408b8cd873e64d3843e9950abacdb86b886e045d6ebb7a304232372e7ae09903be150157f3bd5808a3, 0x5c692497ac801c7d9489007bdfe797fe48d0584958988c599804553f298d0cdc9c47baa1974561726c00dbc20483cdd2cae231648faa53c835273d89e7c62b58e229f8279bbe,
  0x10829b6d10053f4750654b58700414e09ec06f3e5abc1345f848f6f52aabd6c8c73a1b5d007c36e56585ec346fd9fad27e3a9ba6228ae00a5f33c5b01fa1f2cc8281c6c9c7fa, 0x298a9884ff2359428ec49d83cb55e7975b33a2f64014e25389d307947b43a2d52f8ac0ee4b6fb40069597e85f5aea43edcb0495f7cde4b71eac9ae0c8b35214fabb3da11c1a, 0x5bbe12c169a2f2c5989a17f5c501529a97733f7ca55e92fd5c22c365deb0d579ff0c889dec320fed29af44a3ad83de6617fdb920f1dbce3731a9e3eb57f8e6e92fc5e4b61e,
  0xb14911d142224ac3186af366c14cec6d4b82e9e6e3d1f530cd47f49b9ee24e33247ae9bc001514df87d34f1bcf7bdd752bd013a166736e5e46cf358a0fbaae0aab4c1046f, 0x12abec72789a3bf350a0b2f91de5302c1a4002c616ea0a6135fa5b5b08d6bae2d3e7bc66510c552616cae3fb4285ce2d745f1b0bc57ebc96e6d0d0c3640ba616dd2c40a9d, 0x1b554ea0cc1793be99e6cbe34a591e6bce14abe50212ad1ece69e9e4b3457271ab53941aee4270959af9ee7bd08f6bcc0078c3c7380a386edcf0ca6ee519408bb9ab99a9,
  0x229d7edce946c4755a324d9b16b22d52fca6e72815fd8433a6baf4be45d3b2dd19ecbec3b2da09a998bee18c0ef328c58114060aa38b2a14c2cce6c60ee92d56111fad3, 0x25bfa2f16b2a9e03437c50c4834cfd92f69975519b5193a7ad3d6af71819f0b1c03e3bbea36994307a7d10402ba63c9db5a1d2462804009c188670a591823df05da908, 0x2344514634d692f28a3cd96395c4d5b4419b7461bd6116b47e41a2e308736a6a3e2d2b3e236eb204c549479ad24a7204669c7b367482bc84a90a51e988ca4c2709118,
  0x1c112c04b7df19b7bb59e01ffd7762b8cde1f909de6aaaf59eec51afaeb138daf8230915d0cc69a4bf36ebc39779114c2392297ce034127d5ff121407c6eaa421558, 0x12e875d1b58eb9f1a4788f4e2f441282542f73de7a267ff5e56049ef6468db7d3d84ae8334189d7763be96fc8da5b8911154fab45993ffd09a44c4c1bcae2a131c8, 0xab4e9aa4467a09b67fb9d8686d3605befb28b24d34ffa0738aa4a3f20b1fa303cd7dec1136a8200e641ba62edc63b4041511920717d3254f4349b1170c980efc6,
  0x50e51b16680ea5dca85c1fced8174abcfc9e000d3048de2215afae441a2bdef36cae229465fd782280bd39d783433c04c44e434dd369e2a03e010573f3015c32, 0x1f93a26c1736c9a641d5faa4996d0631417ad3c36ceefe8968e4eb04413c8c7f823c8935e8c9c2f51ae970ca08e1527946e5d4f1741a8af93face7bb7eb497a, 0xa166e12eb0b17c8dd193eeeae1ca04ca762deb6ea3d6017c7ab4a0ebee9582b20e3e4ce83a5041ca18a8e686b19d7b8501a9a94eecac2040899c6c5b11f1e,
  0x29ba24a40a1f1b71ce9670070dcec713768174543a6a2212441ced00fed9534ae5bd365db7793c9eed41bfee44ac832b027fe816306efebe5df57a393e64, 0x89e7c7d5073f5bc3d07025bf56ede9c2b9eecc57103efdfa990966e1a0391686fe99866b84d22d85f8f7c1d0fda830389c4b615f9f049e7bbecd00ceac, 0x166dd89aaaf666c966a478f6e5f12f6da85044b5d6ae0a7f409fd58944c3b42c3add9af60a8a19a75240dd6c95bbbef0cace5acf26990a03153c98e2c,
  0x2d3112ca00ad2248409f97c85c762b7fc65cb7f16a2e3a977e7370edb71e7538652c058280d6cfea1cc3a672f7686256578d50437e69a2736fa04e4, 0x45258ea3117713cf069dfb80407e366e4af8b112f75a5b3abbab53cc83eaef6d5702867e08529c4cbecd9a27fcbdda11ce5af66aa783b709a5dae, 0x4e8c235c31ae80e6a4253598b7fbcb58e88f4632f43882c7cfb20564ef212756c9b09296b8f2f6d59866c4b718a2239f8bfa4c761d6d4d24a2a,
  0x4082259e1e430b55a07e3a377e08bd2b96cb83aeb262938ce0868c4721658f17d932501af1a081f0d2aae108c3b052e42377306fbbd5cbda2, 0x251e2da28ed1613b747332b82345d1893fec623090733c2d5a3c2f67b30103dd15547aebdd98bb91ce377079185b6cb6d9f2ff3339d6496, 0xe698b319380a274a414e97771c09a63f870db9427f1bf65c94dda76a7466ed170fe6312c3c8c2edf8202814cd835d8722164c7c20268,
  0x39be642288f5a3d125b07c9d9f5a60ad19293f259a0e1f6b041e848c6cad8cdac882a1f4ab2c847c1ee7d0365798f1e7081944af38, 0x8d2bf59ee020857556272d52c5def7cba0b1ad85d4e65cbb5442bda741ad87af7fe619e1f8da9a2be96fc8d35394f14fb9ab3f8, 0xc4ac68dcab6377be10907a0db3216706289d825e79a50a5d8498b97e6374db0aba1099d0a1cdccb84a9fb69bdab683c984a8,
  0x8f4c2b8c714d637339a07334800eeffdb9a35959a70fc59db67e8a94ef05cf174f0c770a9254441171204c702d0977c35, 0x30f39daf28896c4d8d04d030f64040a7b873a5bcca450b9cde2cbce2cb59335c74e475c55423637e7c1a7d8a7318ef, 0x6cde3194451839c66efa701395d94f7cef63adc7bae2b8592fdc299e912864df154f2d2f2d2bd6a462df72f89b,
  0x51a71c707bacb1e18aa7acf9d94d50b9fb70d2008165754a8b8b08b431d006e4798101a6346f8e549e4a79, 0xfffc1a441d6037d9efb60b6ba361ab4aeac754a532838921d6cbe84be031748904b9bd1475c93d982, 0x9274b4b1c29b580c4901939f432272a6c42921da48152be4c7eb12ba4cfd63c887475aa218c6,
  0x909a43b0cf614294c429f596cc7b03869c937a9dfbbcb3a8ff182ad30abb1b3089f266, 0x6d00f72b3d3846f50103f2c71d6085ba5977e16dab643091c7036b8a3b2ac62, 0xfffffffffc26e4ff189969a6953ecd07d611fec4c9c5f20de6a8d5,
  0x909a469765f53023d38d5a7231073a03433cc33f66f, 0xfffffffffffffffffffffffff93, 0x1]

private theorem eulerianCoefficients_eq : descentCoeffs 108 = eulerianCoefficients := by
  decide +kernel

private theorem upper : upperOK (descentCoeffs 108) first gaps = true := by
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

private theorem lower (i : Fin (lastRepresentative 109 - 2)) :
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

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 109) :
    StrictNegativeInterlacing (originalQuotient 109 k) (eulerian 108) 106 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N109
