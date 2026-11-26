import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentPackedData.C127L120.N117

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N117

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L120.N117 LongCycleBounds.DescentNecklace.Packed.C127L120.N117.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L120.N117 LongCycleBounds.DescentNecklace.Packed.C127L120.N117.rows

private theorem actual : RepresentativeChecks 117 previousNodes rows :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L120.N117 LongCycleBounds.DescentNecklace.Packed.C127L120.N117.dataChecks

private def first : LongCycleFinite.Dyadic := ⟨-83076749736557242056487941267521536, 0⟩

private def gaps : List Window := [
  ⟨⟨-83074055979031757069009760773210112, 0⟩, ⟨-267961363078777405440, 0⟩⟩,
  ⟨⟨-265654957119610290176, 0⟩, ⟨-321032699248640, 0⟩⟩,
  ⟨⟨-310419835060224, 0⟩, ⟨-177553801216, 0⟩⟩,
  ⟨⟨-163148988416, 0⟩, ⟨-1489457152, 0⟩⟩,
  ⟨⟨-1481326592, 0⟩, ⟨-54694144, 0⟩⟩,
  ⟨⟨-54621440, 0⟩, ⟨-4823776, 0⟩⟩,
  ⟨⟨-4821168, 0⟩, ⟨-747980, 0⟩⟩,
  ⟨⟨-747762, 0⟩, ⟨-170686, 0⟩⟩,
  ⟨⟨-170654, 0⟩, ⟨-410655, 3⟩⟩,
  ⟨⟨-205301, 2⟩, ⟨-151441, 3⟩⟩,
  ⟨⟨-75713, 2⟩, ⟨-260823, 5⟩⟩,
  ⟨⟨-521607, 6⟩, ⟨-126685, 5⟩⟩,
  ⟨⟨-506709, 7⟩, ⟨-270797, 7⟩⟩,
  ⟨⟨-270783, 7⟩, ⟨-312581, 8⟩⟩,
  ⟨⟨-312567, 8⟩, ⟨-96069, 7⟩⟩,
  ⟨⟨-384261, 9⟩, ⟨-124421, 8⟩⟩,
  ⟨⟨-497667, 10⟩, ⟨-336667, 10⟩⟩,
  ⟨⟨-336657, 10⟩, ⟨-472609, 11⟩⟩,
  ⟨⟨-118149, 9⟩, ⟨-342327, 11⟩⟩,
  ⟨⟨-171159, 10⟩, ⟨-254759, 11⟩⟩,
  ⟨⟨-509507, 12⟩, ⟨-388155, 12⟩⟩,
  ⟨⟨-388147, 12⟩, ⟨-301787, 12⟩⟩,
  ⟨⟨-301781, 12⟩, ⟨-477725, 13⟩⟩,
  ⟨⟨-119429, 11⟩, ⟨-96027, 11⟩⟩,
  ⟨⟨-192051, 12⟩, ⟨-313151, 13⟩⟩,
  ⟨⟨-156573, 12⟩, ⟨-258475, 13⟩⟩,
  ⟨⟨-516943, 14⟩, ⟨-431407, 14⟩⟩,
  ⟨⟨-431401, 14⟩, ⟨-5681, 8⟩⟩,
  ⟨⟨-363579, 14⟩, ⟨-309139, 14⟩⟩,
  ⟨⟨-309135, 14⟩, ⟨-264943, 14⟩⟩,
  ⟨⟨-66235, 12⟩, ⟨-457405, 15⟩⟩,
  ⟨⟨-457399, 15⟩, ⟨-397405, 15⟩⟩,
  ⟨⟨-397401, 15⟩, ⟨-347307, 15⟩⟩,
  ⟨⟨-347303, 15⟩, ⟨-152575, 14⟩⟩,
  ⟨⟨-152573, 14⟩, ⟨-134705, 14⟩⟩,
  ⟨⟨-269407, 15⟩, ⟨-59727, 13⟩⟩,
  ⟨⟨-119453, 14⟩, ⟨-212711, 15⟩⟩,
  ⟨⟨-212709, 15⟩, ⟨-190081, 15⟩⟩,
  ⟨⟨-380159, 16⟩, ⟨-340849, 16⟩⟩,
  ⟨⟨-170423, 15⟩, ⟨-306531, 16⟩⟩,
  ⟨⟨-9579, 11⟩, ⟨-138215, 15⟩⟩,
  ⟨⟨-276427, 16⟩, ⟨-499825, 17⟩⟩,
  ⟨⟨-124955, 15⟩, ⟨-452911, 17⟩⟩,
  ⟨⟨-452907, 17⟩, ⟨-411247, 17⟩⟩,
  ⟨⟨-102811, 15⟩, ⟨-374117, 17⟩⟩,
  ⟨⟨-187057, 16⟩, ⟨-340911, 17⟩⟩,
  ⟨⟨-85227, 15⟩, ⟨-155561, 16⟩⟩,
  ⟨⟨-311119, 17⟩, ⟨-284315, 17⟩⟩,
  ⟨⟨-35539, 14⟩, ⟨-260127, 17⟩⟩,
  ⟨⟨-260125, 17⟩, ⟨-476487, 18⟩⟩,
  ⟨⟨-119121, 16⟩, ⟨-436793, 18⟩⟩,
  ⟨⟨-436789, 18⟩, ⟨-400705, 18⟩⟩,
  ⟨⟨-200351, 17⟩, ⟨-367831, 18⟩⟩,
  ⟨⟨-91957, 16⟩, ⟨-84455, 16⟩⟩,
  ⟨⟨-337817, 18⟩, ⟨-77593, 16⟩⟩,
  ⟨⟨-155185, 17⟩, ⟨-35653, 15⟩⟩,
  ⟨⟨-285221, 18⟩, ⟨-262145, 18⟩⟩,
  ⟨⟨-262143, 18⟩, ⟨-120467, 17⟩⟩,
  ⟨⟨-60233, 16⟩, ⟨-55353, 16⟩⟩,
  ⟨⟨-442821, 19⟩, ⟨-406843, 19⟩⟩,
  ⟨⟨-50855, 16⟩, ⟨-186825, 18⟩⟩,
  ⟨⟨-373647, 19⟩, ⟨-171497, 18⟩⟩,
  ⟨⟨-21437, 15⟩, ⟨-157329, 18⟩⟩,
  ⟨⟨-314655, 19⟩, ⟨-72111, 17⟩⟩,
  ⟨⟨-288441, 19⟩, ⟨-132089, 18⟩⟩,
  ⟨⟨-16511, 15⟩, ⟨-483407, 20⟩⟩,
  ⟨⟨-120851, 18⟩, ⟨-441757, 20⟩⟩,
  ⟨⟨-441753, 20⟩, ⟨-201577, 19⟩⟩,
  ⟨⟨-403151, 20⟩, ⟨-367371, 20⟩⟩,
  ⟨⟨-45921, 17⟩, ⟨-334201, 20⟩⟩,
  ⟨⟨-334199, 20⟩, ⟨-75865, 18⟩⟩,
  ⟨⟨-303457, 20⟩, ⟨-8593, 15⟩⟩,
  ⟨⟨-274973, 20⟩, ⟨-124299, 19⟩⟩,
  ⟨⟨-62149, 18⟩, ⟨-448373, 21⟩⟩,
  ⟨⟨-448369, 21⟩, ⟨-201615, 20⟩⟩,
  ⟨⟨-201613, 20⟩, ⟨-361531, 21⟩⟩,
  ⟨⟨-45191, 18⟩, ⟨-80767, 19⟩⟩,
  ⟨⟨-323065, 21⟩, ⟨-287643, 21⟩⟩,
  ⟨⟨-35955, 18⟩, ⟨-510151, 22⟩⟩,
  ⟨⟨-255073, 21⟩, ⟨-450403, 22⟩⟩,
  ⟨⟨-450399, 22⟩, ⟨-197865, 21⟩⟩,
  ⟨⟨-197863, 21⟩, ⟨-172923, 21⟩⟩,
  ⟨⟨-172921, 21⟩, ⟨-4695, 16⟩⟩,
  ⟨⟨-300477, 22⟩, ⟨-518751, 23⟩⟩,
  ⟨⟨-518745, 23⟩, ⟨-222297, 22⟩⟩,
  ⟨⟨-444589, 23⟩, ⟨-378017, 23⟩⟩,
  ⟨⟨-94503, 21⟩, ⟨-159293, 22⟩⟩,
  ⟨⟨-159291, 22⟩, ⟨-265869, 23⟩⟩,
  ⟨⟨-265865, 23⟩, ⟨-438893, 24⟩⟩,
  ⟨⟨-438887, 24⟩, ⟨-178911, 23⟩⟩,
  ⟨⟨-44727, 21⟩, ⟨-17981, 20⟩⟩,
  ⟨⟨-287691, 24⟩, ⟨-227713, 24⟩⟩,
  ⟨⟨-227709, 24⟩, ⟨-354087, 25⟩⟩,
  ⟨⟨-354081, 25⟩, ⟨-269751, 25⟩⟩,
  ⟨⟨-134873, 24⟩, ⟨-401489, 26⟩⟩,
  ⟨⟨-401481, 26⟩, ⟨-290813, 26⟩⟩,
  ⟨⟨-145403, 25⟩, ⟨-408241, 27⟩⟩,
  ⟨⟨-51029, 24⟩, ⟨-69041, 25⟩⟩,
  ⟨⟨-69039, 25⟩, ⟨-357669, 28⟩⟩,
  ⟨⟨-357659, 28⟩, ⟨-439697, 29⟩⟩,
  ⟨⟨-109921, 27⟩, ⟨-253781, 29⟩⟩,
  ⟨⟨-253773, 29⟩, ⟨-271233, 30⟩⟩,
  ⟨⟨-135611, 29⟩, ⟨-65871, 29⟩⟩,
  ⟨⟨-131737, 30⟩, ⟨-453791, 33⟩⟩,
  ⟨⟨-453771, 33⟩, ⟨-83677, 32⟩⟩,
  ⟨⟨-334691, 34⟩, ⟨-402661, 36⟩⟩,
  ⟨⟨-402639, 36⟩, ⟨-367599, 38⟩⟩,
  ⟨⟨-367577, 38⟩, ⟨-114035, 39⟩⟩,
  ⟨⟨-228055, 40⟩, ⟨-321785, 44⟩⟩,
  ⟨⟨-160881, 43⟩, ⟨-379393, 49⟩⟩,
  ⟨⟨-379365, 49⟩, ⟨-104155, 54⟩⟩,
  ⟨⟨-416587, 56⟩, ⟨-474641, 67⟩⟩,
  ⟨⟨-237301, 66⟩, ⟨-72439, 84⟩⟩,
  ⟨⟨-289729, 86⟩, ⟨-262165, 134⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private def eulerianCoefficients : List ℤ := [
  0x1, 0xfffffffffffffffffffffffffff8b, 0xe7a01eb2e2c10f13abdd9bb089a8a35cd9e3847d71a993,
  0xffffffffff9623d1f83e5dc41a5303b7d85115ed56906b0472ab15a519, 0x289b68e5f1bbddd27907936f31901ae90bc38618b5a59338681fd5c1a14dc6279d1c, 0xe7a01d89f251fbf3de17889bf82e4a3365509ebb3cd167053ee886a5aa005cf5665c3c1cfb4,
  0x3252e282205aa3730aaa96cc1f4c94a1389dbcf41f5bbf7596c30eb34ac97afc7190c3802ea176e724, 0xfffe9001cf42b4e21778ef3c84816e1840c70d1351f7ca14ad760bb3070b665bb9a41aab170a4685d7fa36c, 0xd18b0b926e7bd2e412579f30b916208496a37d2a28fcc45ed53cae6e2d6efba435585175be99e32e35521bae6622,
  0x28956c82ab36b49e851ac419704355ae9f2be1d7b49e54be83afe2b2ef113f7a2492b1afaff789fee3d56db124451cf76, 0x2729988e7a0823f2945e930278a74364321bfbf6652403bb7e5f9c12b9fa2994400a31a264f1515841b18c54b87f99fbddb96, 0xe6817a1e924ce82bf18b876e5704026d2d2bd710ea1734a706882e3cb00c92590ca3c138c9ea31d9da80d828e78cc76417da9682,
  0x25ab2ec5415df7ae4b806eff242aae65989615d3679675cb3757175430d56e8490c65a9fcedd66444845ca35a68f0d0292ea90bda39c, 0x313df03d574240d0a725da509e6ed47eb49abaa42930c533d4a7e70b03da2fef8e16bbfecf7ae638712852b8aa883b32c2a3ba504df9734, 0x2351913c19284a1ae641c7a735b8d138ba95e95389a87d3e8eeac312396f8a69deaa170077da02e96bdf697a99d73b76a9ccb22a46b4d61384,
  0xef881df95d8eee3c41519f06154912616a32399d1d75aefb2ad388947a5100f29c13ffcc29f7c276f6391c5be3c8069c44e4ccdc7e434ec1f88c, 0x3fb90bc834a3c86687263e9766a80827c35b26dc23a6c786507da3615b74d89fdc964273f62f42b635618d2b2664092ae91f1af12ffadd3629b75b3, 0xb2d5c8ecb03a0d9387a70cacd29ae0b70ccb4b5491216dd15ea10175a620f73c3104a8f69e02fbc880c8117255d679ef6f74dcc9f688cdf26c6d7b731,
  0x158b7901af320644a73d8c6a94871b941563df6eb61e9ba075e25336469891dae1907c5c783a964829a38d6d36cf0a2c86dfb81b59571e091f609442b639, 0x1d842b9bc59d50e6a5b0928abb5c3c9a0e525b766639ca8f0964b541219956a3559b5f1b79315668de6246ca953d31d396d1ee995bdd2a4fefd7d26dbd99cb, 0x1d953ccfd5532c58904506631ba1a9e00e6a18cf097b9ef6d83ee0b57283ad69a85f376ecbf7cff0137a5846b8200aa0a0f8e7d2c4aa65c264fc19ab2fdf1da8,
  0x163b5cf377b5b0c779617ce658adec8ae69ef74278b208d45d9d81b43d2e5743d389199ec418582a053cfe695f09abf15239b2de5a261c8a34a4a894c32c010b38, 0xccb93165b8cded02c5af8297c3469c2add1ba1b28b870e9430f2caa3fdfd118fb4441675942a8fb2425c4ff125d6184a4adcbc698ff1d2b6141d3b036bd5f268058, 0x5be651e58a55f63589258a39ca713334ff04caf48ce796d378ee5ef7a57eeb11082e9cab65d1d6026150e35e47a3365395a6ae3ffb54c9c20ae3fefa503c661d41d08,
  0x20b1365c99278b29aa4545f3339db7657853365343ad35db56932b8bddf5ad33dda6240598fd0f2aaf0e7a6a008099a84e6734508529fc257726a341eed48bfdd152e54, 0x958792b50718f56841c51b4907687a5973571c753cd5214406979475c7bba5570aafd5e8e7e8c5724719cc08861229ffc9aaedd974ca8bbfc146ada6db94a3c2bbd2359c, 0x22c5ef40d39c4285506b9853d9975719f928915fa3ccd3d2cc4a80f0301603880f0c68e310fa574bfd16be8fb417bf438d506260467445790757b9cdb6889ffae3ba72d51c,
  0x6a6692be04b38fd786bbd260dfec5b91664a823cd4535cea44f3fa282700b0b4b30c45f94b24d6d0634a040f5edb35eaa79ff7070fce51c93c52318bac2b388a15101bddcd4, 0x10e53bc9c6c246a3c6430cbc9e272b3077d2709722c3fce00f689ef31bfa7001d18fa922f541290ea59ab856ddd098fd55b1e91c5d257d8394d250412e5ad9599878137514848, 0x23f3087cb4ca92023220077b348d5a5e7a5471494ecaa5b1b40a25b9cb0c32803cd5a7482873e4b8b52977446ed6af5c6d95f753d7dd458091d9e7381809d0ec47413bd02ca418,
  0x408e0cb58c4876712c6af04c24dbad1aa4decbf6b4f30818f27a7c01bfbde1c890c652d159ba2d5ac3536ae1cd6d8878740f0c441f6fc02c5465c0cb171dc3090978f605767dff8, 0x6282cbeb8f0afde6e9c5e0669128cb219468ffe6072514a877c6b1530e120fe7a270500e185c1b450c27ca4f5e906ca27e5847a1db9faa034016cebf8aedce187ff4e9ea471ddbe8, 0x808be74b6442658f2cca0f37363bc3e82d1c2d46d35f40d7192d132e44a244c46d0d5ec69281e1208c8906e2e8b5aef5ab495d26dfa716892cc42893fa61d1b929eac415e04f2a459,
  0x903e87420aa10b6a3c5425a5759e41e272ff18ed3f72074bf3157ce3e3aa1441b7bec25a2734db7d7fe3e1981084abc0a856d0e3badfe317a8dae1f5d5451cf2ff91f31cd9a4d65353, 0x8be5c1e768adf11056b0a3cc5e761b3765ebb75e34aa340367dc5376da2d767bebb7b64371ff2a12e5e41434c964664b4e0179ffc433818ae24b904b3677eac2fb0746c24a54adf53bb, 0x75d097c295d34ff1ceccfec34f4bbf25eebf620a934574f2ea1b416e9e0956d5e08a397e9001dafc334a62c72527dc23659d4290e40ba7a549ea7a8946296222fe2f343cabd44557c091,
  0x5683cd54d3307eb3bdcbc0dd03b83bcab02769373f1a67611727607631545b6f5412ad48ed760235a95aed4bd46ffef9b005cd3d03ccfdae1b56449db21c0a332c73b5599cb87ea776ed4, 0x379bbdad16fb925e3ab77dc0bd58bf4ace782a69aaabdf01ae526c19529f03b9edd95ee2b5cee0a990f3b614d285473d6e300b729d53f442439795800db1d97663b9655aebe325d605f99c, 0x1f6513c3aa1c929695ff5d5e994f6a01038038f7c93a9100e7a000e547117af668c50acf17c56b5f182a5e477a43fb728c862636db417d860d5e18b1aa16ab2296b5cde0c2648577541ee6c,
  0xf9e2abac3dae32eb216020dba7adc7d45fe4b61eeee0bc82b2d5747dd4eae690b127b69867740490acbecbb60346c5b10a27abdabc28adec9adcc1585c91650a35edaa57adfc70d83366d44, 0x6dd9c91b4a751c1ff877afeeb66e1b0fea0dc657b7792869c4f6ac15a0c0919a89cfc982bf84301d6cdc1ab63fbd618426bef87d3deed63b52b4013b25a2dd4aecb9c684ae9042d5b7c541de, 0x2ac95ded1bd28a5aa0854902c1016a97e5ff40850e6588b7d45346f72c40402fad39705d9cfe8e6d4f9dc928974048f13da0217df0e3ea1fccef15b9af3b506e77b6e59aba4a269d5afcb208a,
  0xecd1bba04bc467822598b3b1edcd982ca30ba58980848305f1125887030b8ef92534bd2a4d7a78a5ab292a4e1fdcfec8b35e6ba55588fd550a0cc1a60a40bf66297ef332d17c757ff23e21d2a, 0x48eb354eb7e66571cf56a678385dc8cb65633217189bfe808e67dade863e6c8a9fd01a957be0b0c0453f6f0753b2b113e23fd54d70f23a09a83c6526d03d2b1483b7609ca2712108ac94a873be, 0x1406367a3610e4687e2019c43620a99e159e63a33fd0bcacf4d2710100b4d4b771f9127228a4c546eb7c6d577cf352b63e6d9e322fd88fad2246ca88a479d761cb2a33d93a735c268d760012634,
  0x4e9bd217779753a3b3b55e47f3c53d36be43286a95979f0b477c24fe60b64f36df8fc245aef421b03bfb2940974646691dde873806205ccb8598dd43c6e8df25c8c174b5292ae1032020ffb46bc, 0x1142a1844785d0f3234f05e7ca3b127b4d91de5c41494fc1b310b867c80ab02cfa88ad05d988575e8c72318aa5a398906de99867c634d6551e5c5b17319a2b41cb1736f3fc2bb19758983dda74ac, 0x3658816b22f1908c43878516ba638e0940ec78c6ec7e9d12c829de5761d3619270809c79d0296add8b7dcf772f66b7a967966c33b8dfdd2c3b738ca07b0874b50d47f6ccce38a71208084e27b004,
  0x998f0662fd9515645208ad812e3dc5c84edf41f0dedc2ee7f70fcba793194cca7f24acb54dd1bcf8ac5a00da8b13ea141c18b1a26d4cf012e22963904c7868cb60e88f99a0e434f13c5dcda209a3, 0x185d6688a42dea335a8dfffdd4fc3ceecb7c7b0b5af807650529fd1c4366201ee08c9e38f29ae613fc082e5aee1cee7ad9834be37bbf735cf89d2cb9b5fd1820497092bc1abd727911bd1dac9e281, 0x37a1bc26563c50aac7d4bc18d7c7a894e43c5ee3b703ae3882a8cbd7d3fb3babbcbb8b5df487d9829bde5296aba4cb354bb557073d1812363be5fce2b8bd397b5ead692d798394bb3324668437fe9,
  0x7258e4c6a60bcbed8cc088bd226298f0538d8dd997d64d24cb0a90557804ca989d9f686d9153c22350a121ea5cef97aaa214c6dff97b8036f28f378cdc2e012e2b7425e18c0fb4672a9e559be3cdb, 0xd3be80bd58d16b0a7caec5099dd8965b2764b40e79430a088d53829f4c76b31621be55e4b565112dbf81124099615854dd51fae9254ea8b4ed7470115f76aa05297c85d8a512feaa44146b475d1f0, 0x1617b75d7d5ded543ca7a7ef807bb33de6df814b7a82b6a845683d33e1b36e267bd6b7dc7349c3465e0d334657f449b811c27d1cd2207e2915b99bb627fafccc3abd57b957d1f00de9d7d111dd4350,
  0x21444f425e8e15b6dc9f728a65b204cfb6f9534764b3b5eb5a72e83e9f34771a17afa0d25c60f9211cdda5248b4499c0fb3d8f327c9343958b044ddf61b6a8b7a6fe6cc2367470caf6596f2b5aa810, 0x2d3411d4587ad0b21c3cf23b52c4776f5f28671ca3c4568fb81079f6085444f4a8e31edc03505d78dc93b0de05909e4621b33867652c5755d6958b5f83c960b99a5cf3ba647e3831b9584d146a4030, 0x37720f2551f0634d2d032d9bc513afeadc605ebcc82be2c8e8b1a341eaaf09d4758c0e0681ede9ca9707c314c82768f051bb7da8a192f0d0aa95ffa3ff0009622629b2bea02beeb789ed5ebc1ce298,
  0x3d673a406a70ca63cca384a1d308b9838b64d9b2dffedebaa3ee7a32bb7b78f9b2e2436848f6f66d931027bc9b0637aa44476f75ba8385b2ae389cb78c758872e82102f1ea864f106b0ae11eaeec88, 0x3d673a406a70ca63cca384a1d308b9838b64d9b2dffedebaa3ee7a32bb7b78f9b2e2436848f6f66d931027bc9b0637aa44476f75ba8385b2ae389cb78c758872e82102f1ea864f106b0ae11eaeec88, 0x37720f2551f0634d2d032d9bc513afeadc605ebcc82be2c8e8b1a341eaaf09d4758c0e0681ede9ca9707c314c82768f051bb7da8a192f0d0aa95ffa3ff0009622629b2bea02beeb789ed5ebc1ce298,
  0x2d3411d4587ad0b21c3cf23b52c4776f5f28671ca3c4568fb81079f6085444f4a8e31edc03505d78dc93b0de05909e4621b33867652c5755d6958b5f83c960b99a5cf3ba647e3831b9584d146a4030, 0x21444f425e8e15b6dc9f728a65b204cfb6f9534764b3b5eb5a72e83e9f34771a17afa0d25c60f9211cdda5248b4499c0fb3d8f327c9343958b044ddf61b6a8b7a6fe6cc2367470caf6596f2b5aa810, 0x1617b75d7d5ded543ca7a7ef807bb33de6df814b7a82b6a845683d33e1b36e267bd6b7dc7349c3465e0d334657f449b811c27d1cd2207e2915b99bb627fafccc3abd57b957d1f00de9d7d111dd4350,
  0xd3be80bd58d16b0a7caec5099dd8965b2764b40e79430a088d53829f4c76b31621be55e4b565112dbf81124099615854dd51fae9254ea8b4ed7470115f76aa05297c85d8a512feaa44146b475d1f0, 0x7258e4c6a60bcbed8cc088bd226298f0538d8dd997d64d24cb0a90557804ca989d9f686d9153c22350a121ea5cef97aaa214c6dff97b8036f28f378cdc2e012e2b7425e18c0fb4672a9e559be3cdb, 0x37a1bc26563c50aac7d4bc18d7c7a894e43c5ee3b703ae3882a8cbd7d3fb3babbcbb8b5df487d9829bde5296aba4cb354bb557073d1812363be5fce2b8bd397b5ead692d798394bb3324668437fe9,
  0x185d6688a42dea335a8dfffdd4fc3ceecb7c7b0b5af807650529fd1c4366201ee08c9e38f29ae613fc082e5aee1cee7ad9834be37bbf735cf89d2cb9b5fd1820497092bc1abd727911bd1dac9e281, 0x998f0662fd9515645208ad812e3dc5c84edf41f0dedc2ee7f70fcba793194cca7f24acb54dd1bcf8ac5a00da8b13ea141c18b1a26d4cf012e22963904c7868cb60e88f99a0e434f13c5dcda209a3, 0x3658816b22f1908c43878516ba638e0940ec78c6ec7e9d12c829de5761d3619270809c79d0296add8b7dcf772f66b7a967966c33b8dfdd2c3b738ca07b0874b50d47f6ccce38a71208084e27b004,
  0x1142a1844785d0f3234f05e7ca3b127b4d91de5c41494fc1b310b867c80ab02cfa88ad05d988575e8c72318aa5a398906de99867c634d6551e5c5b17319a2b41cb1736f3fc2bb19758983dda74ac, 0x4e9bd217779753a3b3b55e47f3c53d36be43286a95979f0b477c24fe60b64f36df8fc245aef421b03bfb2940974646691dde873806205ccb8598dd43c6e8df25c8c174b5292ae1032020ffb46bc, 0x1406367a3610e4687e2019c43620a99e159e63a33fd0bcacf4d2710100b4d4b771f9127228a4c546eb7c6d577cf352b63e6d9e322fd88fad2246ca88a479d761cb2a33d93a735c268d760012634,
  0x48eb354eb7e66571cf56a678385dc8cb65633217189bfe808e67dade863e6c8a9fd01a957be0b0c0453f6f0753b2b113e23fd54d70f23a09a83c6526d03d2b1483b7609ca2712108ac94a873be, 0xecd1bba04bc467822598b3b1edcd982ca30ba58980848305f1125887030b8ef92534bd2a4d7a78a5ab292a4e1fdcfec8b35e6ba55588fd550a0cc1a60a40bf66297ef332d17c757ff23e21d2a, 0x2ac95ded1bd28a5aa0854902c1016a97e5ff40850e6588b7d45346f72c40402fad39705d9cfe8e6d4f9dc928974048f13da0217df0e3ea1fccef15b9af3b506e77b6e59aba4a269d5afcb208a,
  0x6dd9c91b4a751c1ff877afeeb66e1b0fea0dc657b7792869c4f6ac15a0c0919a89cfc982bf84301d6cdc1ab63fbd618426bef87d3deed63b52b4013b25a2dd4aecb9c684ae9042d5b7c541de, 0xf9e2abac3dae32eb216020dba7adc7d45fe4b61eeee0bc82b2d5747dd4eae690b127b69867740490acbecbb60346c5b10a27abdabc28adec9adcc1585c91650a35edaa57adfc70d83366d44, 0x1f6513c3aa1c929695ff5d5e994f6a01038038f7c93a9100e7a000e547117af668c50acf17c56b5f182a5e477a43fb728c862636db417d860d5e18b1aa16ab2296b5cde0c2648577541ee6c,
  0x379bbdad16fb925e3ab77dc0bd58bf4ace782a69aaabdf01ae526c19529f03b9edd95ee2b5cee0a990f3b614d285473d6e300b729d53f442439795800db1d97663b9655aebe325d605f99c, 0x5683cd54d3307eb3bdcbc0dd03b83bcab02769373f1a67611727607631545b6f5412ad48ed760235a95aed4bd46ffef9b005cd3d03ccfdae1b56449db21c0a332c73b5599cb87ea776ed4, 0x75d097c295d34ff1ceccfec34f4bbf25eebf620a934574f2ea1b416e9e0956d5e08a397e9001dafc334a62c72527dc23659d4290e40ba7a549ea7a8946296222fe2f343cabd44557c091,
  0x8be5c1e768adf11056b0a3cc5e761b3765ebb75e34aa340367dc5376da2d767bebb7b64371ff2a12e5e41434c964664b4e0179ffc433818ae24b904b3677eac2fb0746c24a54adf53bb, 0x903e87420aa10b6a3c5425a5759e41e272ff18ed3f72074bf3157ce3e3aa1441b7bec25a2734db7d7fe3e1981084abc0a856d0e3badfe317a8dae1f5d5451cf2ff91f31cd9a4d65353, 0x808be74b6442658f2cca0f37363bc3e82d1c2d46d35f40d7192d132e44a244c46d0d5ec69281e1208c8906e2e8b5aef5ab495d26dfa716892cc42893fa61d1b929eac415e04f2a459,
  0x6282cbeb8f0afde6e9c5e0669128cb219468ffe6072514a877c6b1530e120fe7a270500e185c1b450c27ca4f5e906ca27e5847a1db9faa034016cebf8aedce187ff4e9ea471ddbe8, 0x408e0cb58c4876712c6af04c24dbad1aa4decbf6b4f30818f27a7c01bfbde1c890c652d159ba2d5ac3536ae1cd6d8878740f0c441f6fc02c5465c0cb171dc3090978f605767dff8, 0x23f3087cb4ca92023220077b348d5a5e7a5471494ecaa5b1b40a25b9cb0c32803cd5a7482873e4b8b52977446ed6af5c6d95f753d7dd458091d9e7381809d0ec47413bd02ca418,
  0x10e53bc9c6c246a3c6430cbc9e272b3077d2709722c3fce00f689ef31bfa7001d18fa922f541290ea59ab856ddd098fd55b1e91c5d257d8394d250412e5ad9599878137514848, 0x6a6692be04b38fd786bbd260dfec5b91664a823cd4535cea44f3fa282700b0b4b30c45f94b24d6d0634a040f5edb35eaa79ff7070fce51c93c52318bac2b388a15101bddcd4, 0x22c5ef40d39c4285506b9853d9975719f928915fa3ccd3d2cc4a80f0301603880f0c68e310fa574bfd16be8fb417bf438d506260467445790757b9cdb6889ffae3ba72d51c,
  0x958792b50718f56841c51b4907687a5973571c753cd5214406979475c7bba5570aafd5e8e7e8c5724719cc08861229ffc9aaedd974ca8bbfc146ada6db94a3c2bbd2359c, 0x20b1365c99278b29aa4545f3339db7657853365343ad35db56932b8bddf5ad33dda6240598fd0f2aaf0e7a6a008099a84e6734508529fc257726a341eed48bfdd152e54, 0x5be651e58a55f63589258a39ca713334ff04caf48ce796d378ee5ef7a57eeb11082e9cab65d1d6026150e35e47a3365395a6ae3ffb54c9c20ae3fefa503c661d41d08,
  0xccb93165b8cded02c5af8297c3469c2add1ba1b28b870e9430f2caa3fdfd118fb4441675942a8fb2425c4ff125d6184a4adcbc698ff1d2b6141d3b036bd5f268058, 0x163b5cf377b5b0c779617ce658adec8ae69ef74278b208d45d9d81b43d2e5743d389199ec418582a053cfe695f09abf15239b2de5a261c8a34a4a894c32c010b38, 0x1d953ccfd5532c58904506631ba1a9e00e6a18cf097b9ef6d83ee0b57283ad69a85f376ecbf7cff0137a5846b8200aa0a0f8e7d2c4aa65c264fc19ab2fdf1da8,
  0x1d842b9bc59d50e6a5b0928abb5c3c9a0e525b766639ca8f0964b541219956a3559b5f1b79315668de6246ca953d31d396d1ee995bdd2a4fefd7d26dbd99cb, 0x158b7901af320644a73d8c6a94871b941563df6eb61e9ba075e25336469891dae1907c5c783a964829a38d6d36cf0a2c86dfb81b59571e091f609442b639, 0xb2d5c8ecb03a0d9387a70cacd29ae0b70ccb4b5491216dd15ea10175a620f73c3104a8f69e02fbc880c8117255d679ef6f74dcc9f688cdf26c6d7b731,
  0x3fb90bc834a3c86687263e9766a80827c35b26dc23a6c786507da3615b74d89fdc964273f62f42b635618d2b2664092ae91f1af12ffadd3629b75b3, 0xef881df95d8eee3c41519f06154912616a32399d1d75aefb2ad388947a5100f29c13ffcc29f7c276f6391c5be3c8069c44e4ccdc7e434ec1f88c, 0x2351913c19284a1ae641c7a735b8d138ba95e95389a87d3e8eeac312396f8a69deaa170077da02e96bdf697a99d73b76a9ccb22a46b4d61384,
  0x313df03d574240d0a725da509e6ed47eb49abaa42930c533d4a7e70b03da2fef8e16bbfecf7ae638712852b8aa883b32c2a3ba504df9734, 0x25ab2ec5415df7ae4b806eff242aae65989615d3679675cb3757175430d56e8490c65a9fcedd66444845ca35a68f0d0292ea90bda39c, 0xe6817a1e924ce82bf18b876e5704026d2d2bd710ea1734a706882e3cb00c92590ca3c138c9ea31d9da80d828e78cc76417da9682,
  0x2729988e7a0823f2945e930278a74364321bfbf6652403bb7e5f9c12b9fa2994400a31a264f1515841b18c54b87f99fbddb96, 0x28956c82ab36b49e851ac419704355ae9f2be1d7b49e54be83afe2b2ef113f7a2492b1afaff789fee3d56db124451cf76, 0xd18b0b926e7bd2e412579f30b916208496a37d2a28fcc45ed53cae6e2d6efba435585175be99e32e35521bae6622,
  0xfffe9001cf42b4e21778ef3c84816e1840c70d1351f7ca14ad760bb3070b665bb9a41aab170a4685d7fa36c, 0x3252e282205aa3730aaa96cc1f4c94a1389dbcf41f5bbf7596c30eb34ac97afc7190c3802ea176e724, 0xe7a01d89f251fbf3de17889bf82e4a3365509ebb3cd167053ee886a5aa005cf5665c3c1cfb4,
  0x289b68e5f1bbddd27907936f31901ae90bc38618b5a59338681fd5c1a14dc6279d1c, 0xffffffffff9623d1f83e5dc41a5303b7d85115ed56906b0472ab15a519, 0xe7a01eb2e2c10f13abdd9bb089a8a35cd9e3847d71a993,
  0xfffffffffffffffffffffffffff8b, 0x1]

private theorem eulerianCoefficients_eq : descentCoeffs 116 = eulerianCoefficients := by
  decide +kernel

private theorem upper : upperOK (descentCoeffs 116) first gaps = true := by
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

private theorem lower (i : Fin (lastRepresentative 117 - 2)) :
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

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 117) :
    StrictNegativeInterlacing (originalQuotient 117 k) (eulerian 116) 114 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N117
