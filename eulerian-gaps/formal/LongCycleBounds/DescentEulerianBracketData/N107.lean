import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentPackedData.C127L112.N107

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N107

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L112.N107 LongCycleBounds.DescentNecklace.Packed.C127L112.N107.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L112.N107 LongCycleBounds.DescentNecklace.Packed.C127L112.N107.rows

private theorem actual : RepresentativeChecks 107 previousNodes rows :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L112.N107 LongCycleBounds.DescentNecklace.Packed.C127L112.N107.dataChecks

private def first : LongCycleFinite.Dyadic := ⟨-81129638414606681695789005144064, 0⟩

private def gaps : List Window := [
  ⟨⟨-81127007792023200262704844505088, 0⟩, ⟨-5144148713433726976, 0⟩⟩,
  ⟨⟨-2838323296406077440, 0⟩, ⟨-17512662040576, 0⟩⟩,
  ⟨⟨-17343480594432, 0⟩, ⟨-18675335168, 0⟩⟩,
  ⟨⟨-17875730432, 0⟩, ⟨-237659136, 0⟩⟩,
  ⟨⟨-236774400, 0⟩, ⟨-11542816, 0⟩⟩,
  ⟨⟨-11531296, 0⟩, ⟨-1246372, 0⟩⟩,
  ⟨⟨-1245832, 0⟩, ⟨-450941, 1⟩⟩,
  ⟨⟨-450831, 1⟩, ⟨-116165, 1⟩⟩,
  ⟨⟨-232293, 2⟩, ⟨-77025, 2⟩⟩,
  ⟨⟨-154033, 3⟩, ⟨-492351, 6⟩⟩,
  ⟨⟨-492309, 6⟩, ⟨-226635, 6⟩⟩,
  ⟨⟨-56655, 4⟩, ⟨-232927, 7⟩⟩,
  ⟨⟨-116457, 6⟩, ⟨-522495, 9⟩⟩,
  ⟨⟨-522471, 9⟩, ⟨-157179, 8⟩⟩,
  ⟨⟨-314345, 9⟩, ⟨-200339, 9⟩⟩,
  ⟨⟨-400665, 10⟩, ⟨-267799, 10⟩⟩,
  ⟨⟨-133895, 9⟩, ⟨-372539, 11⟩⟩,
  ⟨⟨-372529, 11⟩, ⟨-66999, 9⟩⟩,
  ⟨⟨-267989, 11⟩, ⟨-396811, 12⟩⟩,
  ⟨⟨-198401, 11⟩, ⟨-301107, 12⟩⟩,
  ⟨⟨-301101, 12⟩, ⟨-466815, 13⟩⟩,
  ⟨⟨-233403, 12⟩, ⟨-368629, 13⟩⟩,
  ⟨⟨-184311, 12⟩, ⟨-73965, 11⟩⟩,
  ⟨⟨-295855, 13⟩, ⟨-481735, 14⟩⟩,
  ⟨⟨-7527, 8⟩, ⟨-397169, 14⟩⟩,
  ⟨⟨-397163, 14⟩, ⟨-331127, 14⟩⟩,
  ⟨⟨-331123, 14⟩, ⟨-278825, 14⟩⟩,
  ⟨⟨-278821, 14⟩, ⟨-236877, 14⟩⟩,
  ⟨⟨-118437, 13⟩, ⟨-405691, 15⟩⟩,
  ⟨⟨-202843, 14⟩, ⟨-174945, 14⟩⟩,
  ⟨⟨-174943, 14⟩, ⟨-303707, 15⟩⟩,
  ⟨⟨-303703, 15⟩, ⟨-265145, 15⟩⟩,
  ⟨⟨-132571, 14⟩, ⟨-232687, 15⟩⟩,
  ⟨⟨-465369, 16⟩, ⟨-51291, 13⟩⟩,
  ⟨⟨-102581, 14⟩, ⟨-181667, 15⟩⟩,
  ⟨⟨-181665, 15⟩, ⟨-322957, 16⟩⟩,
  ⟨⟨-322953, 16⟩, ⟨-144031, 15⟩⟩,
  ⟨⟨-288059, 16⟩, ⟨-128871, 15⟩⟩,
  ⟨⟨-515479, 17⟩, ⟨-231263, 16⟩⟩,
  ⟨⟨-231261, 16⟩, ⟨-208027, 16⟩⟩,
  ⟨⟨-208025, 16⟩, ⟨-375103, 17⟩⟩,
  ⟨⟨-93775, 15⟩, ⟨-21179, 13⟩⟩,
  ⟨⟨-338861, 17⟩, ⟨-306673, 17⟩⟩,
  ⟨⟨-153335, 16⟩, ⟨-138989, 16⟩⟩,
  ⟨⟨-277975, 17⟩, ⟨-504627, 18⟩⟩,
  ⟨⟨-504623, 18⟩, ⟨-458577, 18⟩⟩,
  ⟨⟨-458573, 18⟩, ⟨-417145, 18⟩⟩,
  ⟨⟨-208571, 17⟩, ⟨-47471, 15⟩⟩,
  ⟨⟨-379765, 18⟩, ⟨-345963, 18⟩⟩,
  ⟨⟨-43245, 15⟩, ⟨-39415, 15⟩⟩,
  ⟨⟨-315317, 18⟩, ⟨-287483, 18⟩⟩,
  ⟨⟨-35935, 15⟩, ⟨-262145, 18⟩⟩,
  ⟨⟨-262143, 18⟩, ⟨-478079, 19⟩⟩,
  ⟨⟨-119519, 17⟩, ⟨-435875, 19⟩⟩,
  ⟨⟨-13621, 14⟩, ⟨-99317, 17⟩⟩,
  ⟨⟨-24829, 15⟩, ⟨-361905, 19⟩⟩,
  ⟨⟨-180951, 18⟩, ⟨-82369, 17⟩⟩,
  ⟨⟨-329473, 19⟩, ⟨-299709, 19⟩⟩,
  ⟨⟨-149853, 18⟩, ⟨-34045, 16⟩⟩,
  ⟨⟨-136179, 18⟩, ⟨-123607, 18⟩⟩,
  ⟨⟨-61803, 17⟩, ⟨-224083, 19⟩⟩,
  ⟨⟨-224081, 19⟩, ⟨-50699, 17⟩⟩,
  ⟨⟨-405589, 20⟩, ⟨-366407, 20⟩⟩,
  ⟨⟨-91601, 18⟩, ⟨-165171, 19⟩⟩,
  ⟨⟨-330339, 20⟩, ⟨-297153, 20⟩⟩,
  ⟨⟨-148575, 19⟩, ⟨-266623, 20⟩⟩,
  ⟨⟨-66655, 18⟩, ⟨-238559, 20⟩⟩,
  ⟨⟨-477113, 21⟩, ⟨-425567, 21⟩⟩,
  ⟨⟨-425563, 21⟩, ⟨-189137, 20⟩⟩,
  ⟨⟨-378271, 21⟩, ⟨-167475, 20⟩⟩,
  ⟨⟨-334947, 21⟩, ⟨-295333, 21⟩⟩,
  ⟨⟨-147665, 20⟩, ⟨-518359, 22⟩⟩,
  ⟨⟨-259177, 21⟩, ⟨-226271, 21⟩⟩,
  ⟨⟨-226269, 21⟩, ⟨-196405, 21⟩⟩,
  ⟨⟨-196403, 21⟩, ⟨-338781, 22⟩⟩,
  ⟨⟨-338777, 22⟩, ⟨-290109, 22⟩⟩,
  ⟨⟨-145053, 21⟩, ⟨-492929, 23⟩⟩,
  ⟨⟨-492923, 23⟩, ⟨-415069, 23⟩⟩,
  ⟨⟨-51883, 20⟩, ⟨-346051, 23⟩⟩,
  ⟨⟨-173023, 22⟩, ⟨-285303, 23⟩⟩,
  ⟨⟨-285299, 23⟩, ⟨-116137, 22⟩⟩,
  ⟨⟨-464541, 24⟩, ⟨-372841, 24⟩⟩,
  ⟨⟨-372835, 24⟩, ⟨-147213, 23⟩⟩,
  ⟨⟨-294421, 24⟩, ⟨-228227, 24⟩⟩,
  ⟨⟨-228223, 24⟩, ⟨-86591, 23⟩⟩,
  ⟨⟨-346357, 25⟩, ⟨-512853, 26⟩⟩,
  ⟨⟨-512843, 26⟩, ⟨-368937, 26⟩⟩,
  ⟨⟨-368929, 26⟩, ⟨-32077, 23⟩⟩,
  ⟨⟨-128305, 25⟩, ⟨-343033, 27⟩⟩,
  ⟨⟨-21439, 23⟩, ⟨-437221, 28⟩⟩,
  ⟨⟨-437209, 28⟩, ⟨-263059, 28⟩⟩,
  ⟨⟨-263051, 28⟩, ⟨-295033, 29⟩⟩,
  ⟨⟨-147511, 28⟩, ⟨-151617, 29⟩⟩,
  ⟨⟨-151611, 29⟩, ⟨-279163, 31⟩⟩,
  ⟨⟨-279151, 31⟩, ⟨-446099, 33⟩⟩,
  ⟨⟨-223039, 32⟩, ⟨-295809, 34⟩⟩,
  ⟨⟨-295793, 34⟩, ⟨-76211, 34⟩⟩,
  ⟨⟨-152413, 35⟩, ⟨-441289, 39⟩⟩,
  ⟨⟨-110315, 37⟩, ⟨-381183, 42⟩⟩,
  ⟨⟨-95289, 40⟩, ⟨-296455, 46⟩⟩,
  ⟨⟨-296433, 46⟩, ⟨-486995, 53⟩⟩,
  ⟨⟨-486957, 53⟩, ⟨-65885, 60⟩⟩,
  ⟨⟨-131759, 61⟩, ⟨-261067, 80⟩⟩,
  ⟨⟨-522085, 81⟩, ⟨-262165, 124⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private def eulerianCoefficients : List ℤ := [
  0x1, 0x3ffffffffffffffffffffffff95, 0x10112449b5fecc671e9ded9ae900cd8e95b16b08450,
  0xfffffffff948d5d530ee808b41b3fdb0409caa15676ed843eed88, 0x45c32d89fc4cfa3674fbac16ce2b6d7321bde9d651933d80bd3789aec2aa5a, 0x40448f544eba90ae37ae6aa16b40ebd6312db3975df6ab7b580d6400d04f8980c57fa,
  0x2fd27d63295b9c5438eaa9c41f4e0460f50801ce1b93f260cda4bbd9f9fc84d5d1ef890c488, 0x3ffec02ffed023dc13ff460bc3f6d87aeb357110617565ac281734e0ff196716679596384d720510, 0x1020aef4fe4ec50e890cb366eb311fc478b4083a082a36bd9b9447563c56a4fb5c18fd74c24bd267cc379,
  0x116a0d60c3d6e6ffa54b868d10de68f6682b6735f60f4b80bf43e4f6e903289217657ad8fb5861971b21d0675, 0x677ec1cbb496e6ed6240bd33f7be623fd9a79ef0f05f6a5dff06fb604bb38a5bcdb2e4c1b343af9792c33a14b000, 0xfe5c9bac10c087ecad276f9c0586041e023261aad6876123c487d9d358b9b42cc267b4e7bfc097d5ed0e7f39aaf14a0,
  0x1290ac908e5f213ea3c5dd2478f9565b7148acb05787fa46bd1f6059f49184e46e15ca0af518a9b3574906113230806e388, 0xb771671a3021a541efa8ed8cc1825dcd8a4f3f3b849e01580388a203782e07993fcc15f5b11c4312186387171cee87d1b0448, 0x4128c16225e433ada44a02c9bd192b380c646a08263234a3bee436fb2c43dba5c97ccee3fce4a8852627718b31f280dc98afaaa0,
  0xe3bd7451149690597423a3fabe9e5e04ab289d560fe314e12b5468a082dbbdad7c4b27a4d8245e48f9784ff09564bb918e381aaa80, 0x204bff5e7d849c167ae34b7b5f5833c2467748b61fddf3362c11010914015d0f7f3d6dc5b1d6dc49938da9de7cfb495cc8096d95c4656, 0x31bb1a164a253244bdc59ff9330536867f8f602cf0c33137bdfd90664e7825a93fdafe1328c35837c85bb63c0bf85c93d4b29c371b5eaee,
  0x35e88fa611fb9b8cdc165557e36219a52d9e7970a358ae6a1861a9eaf1f12036492da34c92011ca29b3b26e92efacac1d3277e4c25d6931e0, 0x2a6c0dfdb57f5a268bc3efc28e06a88bb3f7c83ddb9ac878557f4ddeec0b7adf184544cbffcc89a0f49cd0407bfbe989870efb6e7fabdfbfe10, 0x18df157e8af946c01ed814be97f66f6025cc9417b478194d2e0cd3abfe04a1290a578a542b574b17d65ed552cf21dfc526fb3022bb4a759b3f254,
  0xb1b4f157cceed1548936cb492a9684b8811427fb120ffed1f5392b269afdd0c787be6f305a9c1d416183389123c58e68a7fedc31ebc608b92381d4, 0x3d9a9298c9d879283b5e9ab296a411f911e35e44a5c18bbc8f65997800dbf976d9b08145be8728bb47f2b9ea57fcac1112ccceda41e0012432da9210, 0x10da35990f741379f284bf8f1bb39cf12c90ca732889d1cf3c3b1f2f8c3fc14314616c2f84b32ccf2d92e21e3880a56df4399a9d3582c7f3d41e04c2e0,
  0x3b0bcd6a05ae4bf50a97d693ecd0b73b225f8908566ff3076906adbf97be819aad4be0188127759cc6bdc65174ae0c4c52e5c83ef43f51a0a81277c9f5e, 0xa7b0ef1d8dc2aaa6a16528eb9b27808e2f58fb7aa4408864c80159d468a6c9dfaae763af5ef367e34611153e41898608bb1c8341ab3a499857bff6e99486, 0x1864ccb118a3001643768b315437e47dd4cc627fbd5db64bf21f540537131d57e8d248af394341dfaf807b1e4ee9caaaf0729f45acd4ad3ba664abe3f2fe80,
  0x2efc42e0323f80f48f11e18c4e9089cd050d7ebbe6d18723df2baf661b8bd901045025d59f23024bde3eb60025b1cf2988799f6561603a365113d22a57a2020, 0x4b8b101978376cdcdd472a30ee005c5a8e81cd0f6d2213248159ed549fae72b678b95e22abac358d44c0a70e7db3ec30e591f0b0ce4bf938452ba2eff6aad828, 0x662b4f3271549ba4f7369b1c986b0aa6e960dad5a812981cf34611d6e76675a06de03d2d9d481be194e3026cabba50f4b5346b948a5fa2833618bd60fe5a4d068,
  0x7509a0b3ca0aad9250ec34d4459c1f971c674db8be03f44ade0b28b48d07096e1b9027ee9ab4b1f025d2a8e7eea3ccb8486adc13260c53477fc3039845da7f5220, 0x72426a91fd48abe578e3a98c93790ceac74a5dcb2b2e5737020eeb2a9aef83ee621154e1922188384cb3ff95cd1ecd54d5bc4c21c96cea270239b9e51584813e200, 0x5f97efe7c74d09de5fd2d102518827054b4f9e51e9810c6fa11406c2f6244dbc94e4f0cc924dee1598d968412b0852471ccfe9b632eeb8e02a583797abc59a6f4213,
  0x44e1b0adfb69bd52ddfd7652ebbdb78f82e868d0e58c0853fe95b6cf745974731f964ec5376a96de5e42052497ee1df03d1553c1d2ba393884806ace3f95bbe0858ef, 0x2af0e9f13fcd80344763c87e96e2133611af40ff877aa0eea0ab80cb3940cb8c763785c2c16c8380419885f3e6329482f70d1f218183a1eac52a88dfafdda69dcc7e70, 0x17411b052707bfec1f015399b327324edb9c0b418f9023c6a23b3d91bcd2e85aab4db9df092604a80d22574e3079fbcc2d0e127e1db122a27577ec8a4e0a1ec72d2acf8,
  0xafacf7fcdd2b36dea5870b1571178d51f9f5e3f5c8662f45fc28a8e3e03a45c35c5923c4979f0f0bd4a61519153f366f2079603d43998a75cd904778643b63571694326, 0x488f72ff04cf72aedec6b282fdb91f7de0714ec71a8a2dd62c3afbfaa9ab31c8c7ed1a19a2461f037d194cc115fc848c30a2e3221b92dd08e54c6b6e7f6d9fa264e07b46, 0x1a4bc90315cc242c82dfcda7c7b39b8bb0bbec50cff62971cf756bf90da316f1ee187471887d0658e82175815fd439de2f6fa663005ca476bb0d95eef89ede23da0cffff8,
  0x8625a1b3d80a52f6408eff32ed2efdae1cd6ff714cd1d630e814045bd2327de150a57a464a5ba7c54a27f7de020471a298089d533688078f0e09c49f7cb30675f1a891a30, 0x25b8c55c6db1d29cac056d6febdc6b4bbe227158e6d8157469d7500b1a7584612b9b3fb0682343c21978e3bd0750a4d1adb332e39601a9f344922e19adcff54530663ed063, 0x96024685558c0fe687be2d7d62ad4a7d18dadb06c6f7014133a1d5689a0d8a242ceb7a09da0ee80d39b06fd7cd169406d07767b02dd2ce66f377a051397b4f1d2df8dc6e57,
  0x2105007cad295b2e5fc851b8f96ef11fd48b9f0bef8b2570ae87c8facc0bb0da7948c08a83e0b38a015bee6ab9c49e68da693ed887bd525d9cb52fd2bdf3674b6b953012a00, 0x672bbc81eefb521adcb23b32082912a5d7e7b694375924ee0cb6ff4a27f368b549d209375e71b5af4b396734ef8862bf5cfc7752551d1a859b819c18938fb1e3d4b8ea20940, 0x11e705fff793f0377ca8f55be92d0ef1ccfec72106ef7c353b9d3166011133290219b9545c3fabd8eba5eff2252144bf4632b14d05b098da724fdaa6b98213f25fbe81911610,
  0x2c39ba0af9295124087a2167d14f89d88f9bad50c5f977199191f4336e9700a7f19c4d9aeddab8ee2a26650f5516337ae8a56397605e8ad25efa0992a450ccb7da8111d7c990, 0x6154064dbd5ac398f96c8453ec4a4c95f8b0f7d5f68592b8808ed9dd53a3232c1757e712b7df19a6edea0a1ecdd8355ec67bd8b5198566f9adec2a82808423a45135842f8540, 0xbf02bf7e727f830aa6c6440d5177fbe2cf2479e103768d194cf8484db3da4ba0f26aa93afda7b9ed652998022cefd2ac49573266b6deedfc77d1c42387a0d2f0e4ad22101b00,
  0x14e95fde3cddc11a5695d2ac65c4c8a29da4764eed718d2b50c5f3d0bd401fdb2520b7691a7473838e8f2d0330642fd77791718d205e3d6fc09c863ffe4b251acf9ee279ace44, 0x20b7ab5e33eb3a1a69dd110ddab1679194e2a6853146ba7de811387c76390552446c668f255939d06bd9ec7ed1310888572ff5599989042ed650964a19a496fef0b0eb0c02954, 0x2dbf29092958712498bc7404aee9acea40aa864b9328cc27bc897f4ab93978540a51e955eaf21cf4c028874d96d31bb91e92c098d038d518d9ed9869f98e6b80baa1fd8d26940,
  0x39306062eaede8c89741cb224b959d9e12b2beab4f8fafc730445b7959dfe20b24c064c06106621f46d6f69bb726bac828e3190af6306aa1aa758232730ee88fc34e5348d50e0, 0x3ff017fbdb519bffb01d46d219ab9ea77fcc98c1aacd2e80734744d222c39f5cc8fe3429566dfcd4eb954bcec9d09f9d21b582b6ad1de54696239753d1f5e4008066409355b18, 0x3ff017fbdb519bffb01d46d219ab9ea77fcc98c1aacd2e80734744d222c39f5cc8fe3429566dfcd4eb954bcec9d09f9d21b582b6ad1de54696239753d1f5e4008066409355b18,
  0x39306062eaede8c89741cb224b959d9e12b2beab4f8fafc730445b7959dfe20b24c064c06106621f46d6f69bb726bac828e3190af6306aa1aa758232730ee88fc34e5348d50e0, 0x2dbf29092958712498bc7404aee9acea40aa864b9328cc27bc897f4ab93978540a51e955eaf21cf4c028874d96d31bb91e92c098d038d518d9ed9869f98e6b80baa1fd8d26940, 0x20b7ab5e33eb3a1a69dd110ddab1679194e2a6853146ba7de811387c76390552446c668f255939d06bd9ec7ed1310888572ff5599989042ed650964a19a496fef0b0eb0c02954,
  0x14e95fde3cddc11a5695d2ac65c4c8a29da4764eed718d2b50c5f3d0bd401fdb2520b7691a7473838e8f2d0330642fd77791718d205e3d6fc09c863ffe4b251acf9ee279ace44, 0xbf02bf7e727f830aa6c6440d5177fbe2cf2479e103768d194cf8484db3da4ba0f26aa93afda7b9ed652998022cefd2ac49573266b6deedfc77d1c42387a0d2f0e4ad22101b00, 0x6154064dbd5ac398f96c8453ec4a4c95f8b0f7d5f68592b8808ed9dd53a3232c1757e712b7df19a6edea0a1ecdd8355ec67bd8b5198566f9adec2a82808423a45135842f8540,
  0x2c39ba0af9295124087a2167d14f89d88f9bad50c5f977199191f4336e9700a7f19c4d9aeddab8ee2a26650f5516337ae8a56397605e8ad25efa0992a450ccb7da8111d7c990, 0x11e705fff793f0377ca8f55be92d0ef1ccfec72106ef7c353b9d3166011133290219b9545c3fabd8eba5eff2252144bf4632b14d05b098da724fdaa6b98213f25fbe81911610, 0x672bbc81eefb521adcb23b32082912a5d7e7b694375924ee0cb6ff4a27f368b549d209375e71b5af4b396734ef8862bf5cfc7752551d1a859b819c18938fb1e3d4b8ea20940,
  0x2105007cad295b2e5fc851b8f96ef11fd48b9f0bef8b2570ae87c8facc0bb0da7948c08a83e0b38a015bee6ab9c49e68da693ed887bd525d9cb52fd2bdf3674b6b953012a00, 0x96024685558c0fe687be2d7d62ad4a7d18dadb06c6f7014133a1d5689a0d8a242ceb7a09da0ee80d39b06fd7cd169406d07767b02dd2ce66f377a051397b4f1d2df8dc6e57, 0x25b8c55c6db1d29cac056d6febdc6b4bbe227158e6d8157469d7500b1a7584612b9b3fb0682343c21978e3bd0750a4d1adb332e39601a9f344922e19adcff54530663ed063,
  0x8625a1b3d80a52f6408eff32ed2efdae1cd6ff714cd1d630e814045bd2327de150a57a464a5ba7c54a27f7de020471a298089d533688078f0e09c49f7cb30675f1a891a30, 0x1a4bc90315cc242c82dfcda7c7b39b8bb0bbec50cff62971cf756bf90da316f1ee187471887d0658e82175815fd439de2f6fa663005ca476bb0d95eef89ede23da0cffff8, 0x488f72ff04cf72aedec6b282fdb91f7de0714ec71a8a2dd62c3afbfaa9ab31c8c7ed1a19a2461f037d194cc115fc848c30a2e3221b92dd08e54c6b6e7f6d9fa264e07b46,
  0xafacf7fcdd2b36dea5870b1571178d51f9f5e3f5c8662f45fc28a8e3e03a45c35c5923c4979f0f0bd4a61519153f366f2079603d43998a75cd904778643b63571694326, 0x17411b052707bfec1f015399b327324edb9c0b418f9023c6a23b3d91bcd2e85aab4db9df092604a80d22574e3079fbcc2d0e127e1db122a27577ec8a4e0a1ec72d2acf8, 0x2af0e9f13fcd80344763c87e96e2133611af40ff877aa0eea0ab80cb3940cb8c763785c2c16c8380419885f3e6329482f70d1f218183a1eac52a88dfafdda69dcc7e70,
  0x44e1b0adfb69bd52ddfd7652ebbdb78f82e868d0e58c0853fe95b6cf745974731f964ec5376a96de5e42052497ee1df03d1553c1d2ba393884806ace3f95bbe0858ef, 0x5f97efe7c74d09de5fd2d102518827054b4f9e51e9810c6fa11406c2f6244dbc94e4f0cc924dee1598d968412b0852471ccfe9b632eeb8e02a583797abc59a6f4213, 0x72426a91fd48abe578e3a98c93790ceac74a5dcb2b2e5737020eeb2a9aef83ee621154e1922188384cb3ff95cd1ecd54d5bc4c21c96cea270239b9e51584813e200,
  0x7509a0b3ca0aad9250ec34d4459c1f971c674db8be03f44ade0b28b48d07096e1b9027ee9ab4b1f025d2a8e7eea3ccb8486adc13260c53477fc3039845da7f5220, 0x662b4f3271549ba4f7369b1c986b0aa6e960dad5a812981cf34611d6e76675a06de03d2d9d481be194e3026cabba50f4b5346b948a5fa2833618bd60fe5a4d068, 0x4b8b101978376cdcdd472a30ee005c5a8e81cd0f6d2213248159ed549fae72b678b95e22abac358d44c0a70e7db3ec30e591f0b0ce4bf938452ba2eff6aad828,
  0x2efc42e0323f80f48f11e18c4e9089cd050d7ebbe6d18723df2baf661b8bd901045025d59f23024bde3eb60025b1cf2988799f6561603a365113d22a57a2020, 0x1864ccb118a3001643768b315437e47dd4cc627fbd5db64bf21f540537131d57e8d248af394341dfaf807b1e4ee9caaaf0729f45acd4ad3ba664abe3f2fe80, 0xa7b0ef1d8dc2aaa6a16528eb9b27808e2f58fb7aa4408864c80159d468a6c9dfaae763af5ef367e34611153e41898608bb1c8341ab3a499857bff6e99486,
  0x3b0bcd6a05ae4bf50a97d693ecd0b73b225f8908566ff3076906adbf97be819aad4be0188127759cc6bdc65174ae0c4c52e5c83ef43f51a0a81277c9f5e, 0x10da35990f741379f284bf8f1bb39cf12c90ca732889d1cf3c3b1f2f8c3fc14314616c2f84b32ccf2d92e21e3880a56df4399a9d3582c7f3d41e04c2e0, 0x3d9a9298c9d879283b5e9ab296a411f911e35e44a5c18bbc8f65997800dbf976d9b08145be8728bb47f2b9ea57fcac1112ccceda41e0012432da9210,
  0xb1b4f157cceed1548936cb492a9684b8811427fb120ffed1f5392b269afdd0c787be6f305a9c1d416183389123c58e68a7fedc31ebc608b92381d4, 0x18df157e8af946c01ed814be97f66f6025cc9417b478194d2e0cd3abfe04a1290a578a542b574b17d65ed552cf21dfc526fb3022bb4a759b3f254, 0x2a6c0dfdb57f5a268bc3efc28e06a88bb3f7c83ddb9ac878557f4ddeec0b7adf184544cbffcc89a0f49cd0407bfbe989870efb6e7fabdfbfe10,
  0x35e88fa611fb9b8cdc165557e36219a52d9e7970a358ae6a1861a9eaf1f12036492da34c92011ca29b3b26e92efacac1d3277e4c25d6931e0, 0x31bb1a164a253244bdc59ff9330536867f8f602cf0c33137bdfd90664e7825a93fdafe1328c35837c85bb63c0bf85c93d4b29c371b5eaee, 0x204bff5e7d849c167ae34b7b5f5833c2467748b61fddf3362c11010914015d0f7f3d6dc5b1d6dc49938da9de7cfb495cc8096d95c4656,
  0xe3bd7451149690597423a3fabe9e5e04ab289d560fe314e12b5468a082dbbdad7c4b27a4d8245e48f9784ff09564bb918e381aaa80, 0x4128c16225e433ada44a02c9bd192b380c646a08263234a3bee436fb2c43dba5c97ccee3fce4a8852627718b31f280dc98afaaa0, 0xb771671a3021a541efa8ed8cc1825dcd8a4f3f3b849e01580388a203782e07993fcc15f5b11c4312186387171cee87d1b0448,
  0x1290ac908e5f213ea3c5dd2478f9565b7148acb05787fa46bd1f6059f49184e46e15ca0af518a9b3574906113230806e388, 0xfe5c9bac10c087ecad276f9c0586041e023261aad6876123c487d9d358b9b42cc267b4e7bfc097d5ed0e7f39aaf14a0, 0x677ec1cbb496e6ed6240bd33f7be623fd9a79ef0f05f6a5dff06fb604bb38a5bcdb2e4c1b343af9792c33a14b000,
  0x116a0d60c3d6e6ffa54b868d10de68f6682b6735f60f4b80bf43e4f6e903289217657ad8fb5861971b21d0675, 0x1020aef4fe4ec50e890cb366eb311fc478b4083a082a36bd9b9447563c56a4fb5c18fd74c24bd267cc379, 0x3ffec02ffed023dc13ff460bc3f6d87aeb357110617565ac281734e0ff196716679596384d720510,
  0x2fd27d63295b9c5438eaa9c41f4e0460f50801ce1b93f260cda4bbd9f9fc84d5d1ef890c488, 0x40448f544eba90ae37ae6aa16b40ebd6312db3975df6ab7b580d6400d04f8980c57fa, 0x45c32d89fc4cfa3674fbac16ce2b6d7321bde9d651933d80bd3789aec2aa5a,
  0xfffffffff948d5d530ee808b41b3fdb0409caa15676ed843eed88, 0x10112449b5fecc671e9ded9ae900cd8e95b16b08450, 0x3ffffffffffffffffffffffff95,
  0x1]

private theorem eulerianCoefficients_eq : descentCoeffs 106 = eulerianCoefficients := by
  decide +kernel

private theorem upper : upperOK (descentCoeffs 106) first gaps = true := by
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

private theorem lower (i : Fin (lastRepresentative 107 - 2)) :
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

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 107) :
    StrictNegativeInterlacing (originalQuotient 107 k) (eulerian 106) 104 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N107
