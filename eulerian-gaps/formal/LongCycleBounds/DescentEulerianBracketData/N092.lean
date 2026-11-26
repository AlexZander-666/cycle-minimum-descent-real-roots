import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentPackedData.C127L096.N092

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N092

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L096.N092 LongCycleBounds.DescentNecklace.Packed.C127L096.N092.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L096.N092 LongCycleBounds.DescentNecklace.Packed.C127L096.N092.rows

private theorem actual : RepresentativeChecks 92 previousNodes rows :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L096.N092 LongCycleBounds.DescentNecklace.Packed.C127L096.N092.dataChecks

private def first : LongCycleFinite.Dyadic := ⟨-2475880078570760549798248448, 0⟩

private def gaps : List Window := [
  ⟨⟨-2475799798340551765829615616, 0⟩, ⟨-10635919572860928, 0⟩⟩,
  ⟨⟨-10565516468944896, 0⟩, ⟨-233471737856, 0⟩⟩,
  ⟨⟨-233051258880, 0⟩, ⟨-652584960, 0⟩⟩,
  ⟨⟨-641929216, 0⟩, ⟨-15128352, 0⟩⟩,
  ⟨⟨-15097696, 0⟩, ⟨-1111264, 0⟩⟩,
  ⟨⟨-1110552, 0⟩, ⟨-324669, 1⟩⟩,
  ⟨⟨-162285, 0⟩, ⟨-147893, 2⟩⟩,
  ⟨⟨-73933, 1⟩, ⟨-91267, 3⟩⟩,
  ⟨⟨-365023, 5⟩, ⟨-279869, 6⟩⟩,
  ⟨⟨-279843, 6⟩, ⟨-125915, 6⟩⟩,
  ⟨⟨-503625, 8⟩, ⟨-511879, 9⟩⟩,
  ⟨⟨-255925, 8⟩, ⟨-142957, 8⟩⟩,
  ⟨⟨-285901, 9⟩, ⟨-344249, 10⟩⟩,
  ⟨⟨-344235, 10⟩, ⟨-27519, 7⟩⟩,
  ⟨⟨-440289, 11⟩, ⟨-295817, 11⟩⟩,
  ⟨⟨-2311, 4⟩, ⟨-207019, 11⟩⟩,
  ⟨⟨-207013, 11⟩, ⟨-9369, 7⟩⟩,
  ⟨⟨-299801, 12⟩, ⟨-446875, 13⟩⟩,
  ⟨⟨-446865, 13⟩, ⟨-341305, 13⟩⟩,
  ⟨⟨-170649, 12⟩, ⟨-133105, 12⟩⟩,
  ⟨⟨-266205, 13⟩, ⟨-422869, 14⟩⟩,
  ⟨⟨-211431, 13⟩, ⟨-341183, 14⟩⟩,
  ⟨⟨-341177, 14⟩, ⟨-139539, 13⟩⟩,
  ⟨⟨-139537, 13⟩, ⟨-231041, 14⟩⟩,
  ⟨⟨-462075, 15⟩, ⟨-386605, 15⟩⟩,
  ⟨⟨-48325, 12⟩, ⟨-326487, 15⟩⟩,
  ⟨⟨-326483, 15⟩, ⟨-277999, 15⟩⟩,
  ⟨⟨-277995, 15⟩, ⟨-119225, 14⟩⟩,
  ⟨⟨-476895, 16⟩, ⟨-6433, 10⟩⟩,
  ⟨⟨-411707, 16⟩, ⟨-178745, 15⟩⟩,
  ⟨⟨-357485, 16⟩, ⟨-311997, 16⟩⟩,
  ⟨⟨-311993, 16⟩, ⟨-2137, 9⟩⟩,
  ⟨⟨-273533, 16⟩, ⟨-240783, 16⟩⟩,
  ⟨⟨-481561, 17⟩, ⟨-425413, 17⟩⟩,
  ⟨⟨-6647, 11⟩, ⟨-376991, 17⟩⟩,
  ⟨⟨-376987, 17⟩, ⟨-334995, 17⟩⟩,
  ⟨⟨-20937, 13⟩, ⟨-149195, 16⟩⟩,
  ⟨⟨-298387, 17⟩, ⟨-66583, 15⟩⟩,
  ⟨⟨-266329, 17⟩, ⟨-476261, 18⟩⟩,
  ⟨⟨-476257, 18⟩, ⟨-426445, 18⟩⟩,
  ⟨⟨-426441, 18⟩, ⟨-191143, 17⟩⟩,
  ⟨⟨-382283, 18⟩, ⟨-171503, 17⟩⟩,
  ⟨⟨-343003, 18⟩, ⟨-307957, 18⟩⟩,
  ⟨⟨-153977, 17⟩, ⟨-17287, 14⟩⟩,
  ⟨⟨-138295, 17⟩, ⟨-124227, 17⟩⟩,
  ⟨⟨-496903, 19⟩, ⟨-446297, 19⟩⟩,
  ⟨⟨-446293, 19⟩, ⟨-200347, 18⟩⟩,
  ⟨⟨-200345, 18⟩, ⟨-11235, 14⟩⟩,
  ⟨⟨-359517, 19⟩, ⟨-80573, 17⟩⟩,
  ⟨⟨-20143, 15⟩, ⟨-288581, 19⟩⟩,
  ⟨⟨-144289, 18⟩, ⟨-516049, 20⟩⟩,
  ⟨⟨-516045, 20⟩, ⟨-230303, 19⟩⟩,
  ⟨⟨-230301, 19⟩, ⟨-410275, 20⟩⟩,
  ⟨⟨-410271, 20⟩, ⟨-182287, 19⟩⟩,
  ⟨⟨-182285, 19⟩, ⟨-323075, 20⟩⟩,
  ⟨⟨-631, 11⟩, ⟨-142701, 19⟩⟩,
  ⟨⟨-285399, 20⟩, ⟨-251229, 20⟩⟩,
  ⟨⟨-502453, 21⟩, ⟨-220259, 20⟩⟩,
  ⟨⟨-220257, 20⟩, ⟨-192231, 20⟩⟩,
  ⟨⟨-192229, 20⟩, ⟨-83457, 19⟩⟩,
  ⟨⟨-163, 10⟩, ⟨-72049, 19⟩⟩,
  ⟨⟨-4503, 15⟩, ⟨-247195, 21⟩⟩,
  ⟨⟨-30899, 18⟩, ⟨-420967, 22⟩⟩,
  ⟨⟨-210481, 21⟩, ⟨-355507, 22⟩⟩,
  ⟨⟨-355503, 22⟩, ⟨-148719, 21⟩⟩,
  ⟨⟨-148717, 21⟩, ⟨-246239, 22⟩⟩,
  ⟨⟨-492471, 23⟩, ⟨-402839, 23⟩⟩,
  ⟨⟨-402833, 23⟩, ⟨-10157, 18⟩⟩,
  ⟨⟨-325019, 23⟩, ⟨-8067, 18⟩⟩,
  ⟨⟨-64535, 21⟩, ⟨-201347, 23⟩⟩,
  ⟨⟨-402687, 24⟩, ⟨-153779, 23⟩⟩,
  ⟨⟨-9611, 19⟩, ⟨-229217, 24⟩⟩,
  ⟨⟨-458425, 25⟩, ⟨-165979, 24⟩⟩,
  ⟨⟨-331951, 25⟩, ⟨-464625, 26⟩⟩,
  ⟨⟨-464615, 26⟩, ⟨-312155, 26⟩⟩,
  ⟨⟨-312147, 26⟩, ⟨-199625, 26⟩⟩,
  ⟨⟨-199619, 26⟩, ⟨-120183, 26⟩⟩,
  ⟨⟨-480717, 28⟩, ⟨-134257, 27⟩⟩,
  ⟨⟨-33563, 25⟩, ⟨-136443, 28⟩⟩,
  ⟨⟨-272875, 29⟩, ⟨-245553, 30⟩⟩,
  ⟨⟨-491085, 31⟩, ⟨-188245, 31⟩⟩,
  ⟨⟨-47059, 29⟩, ⟨-464725, 34⟩⟩,
  ⟨⟨-464699, 34⟩, ⟨-423375, 36⟩⟩,
  ⟨⟨-423349, 36⟩, ⟨-123727, 37⟩⟩,
  ⟨⟨-494875, 39⟩, ⟨-145647, 41⟩⟩,
  ⟨⟨-36409, 39⟩, ⟨-218459, 47⟩⟩,
  ⟨⟨-109221, 46⟩, ⟨-308663, 56⟩⟩,
  ⟨⟨-308637, 56⟩, ⟨-446581, 72⟩⟩,
  ⟨⟨-111635, 70⟩, ⟨-262149, 109⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private def eulerianCoefficients : List ℤ := [
  0x1, 0x7ffffffffffffffffffffa4, 0x12c9389fcca4e0069a6fc4946479e435e9f15,
  0x3fffffff93fafa69274b722a07fd55aabe431fca02ca40, 0x9d1749bdcec0e5ae9132f25c6a31ae6fb7846923e975acd528b06, 0x96498c8a066561e7813dcdaa3e2a0b76a02939625a0eee7ee111cddd128,
  0xb131cf16ef1701fcfe43aa92dc8c34deea3d4a12dbd329ce7df0c29be7b00476, 0x1ffc0517c9c9cd62df1513f62fb0ab06a5d7379d81d1189fb0ce9d6497b49fcec6640, 0x160322bc1ca85401a8ad6794aaedb33967375e4150dd2d4c4adc8a9c9f6eaa01c039755cb,
  0x4e0cf225eb7b6d431fc9e2cab79624fbd1a5b0d65a1bd794103d112cc47bc7644741221349fc, 0x6e501bbe4a05983ffd56797fe25b68a780138296a83abcc1f3c6792f1cdcc316cad02c4901c3d8f, 0x48a57ac297a9111f949b0855492dbc5458d40b461676a0f55c458e4382392afc5ff1506346c8239580,
  0x191026c9a1ad6404e0049bd0e9b9c21ea873fcc7011f92d2ddab8cb46c8567aaca08da167639da48f5634, 0x4f4c074b875dbb9929b5c3f74667bb438f0317ed4aa2b23750147db488de3734a8a1de4659527fec714faf0, 0x9a4650393be9794fdf1528ccdc4664501220b5fb6663fd980d203ef1eedae93ea4a85703c61c6945ac60b46b4,
  0xc32d794241fbd09ed443baabd97819569d3975aa553d7b3c49c67bef2fd9f306bd9ea247427bba705695cc51580, 0xa7fb8db92aae9ccec3dfbec0b9b4e6da03f00fff3ca5df74e24ae6844e3104a06a95868995f8e9efb41cecfa7debb, 0x660e1b5883099375b7be97c73b95d105c08a391d38d2abd70416fb5ff595c98055ee509d717deac4f58ee462deff02c,
  0x2d20176826a5644ba0dcc01266567c49379d40ddfd992659749b1ef0e69396e9909b06fadab26c3b3df323981f2011567, 0xee5f7958e1247af6adc85345666cbc131a0ae329cbb60901c0a5be094176fc7364537d6b5034df5e75ddb24b582e582940, 0x3c0c351c44d02306b6797f6f7691b426dd22df9faa37f6948a9e95130a136db10e55529ffcefafdbc620a3e649d1ea7fa3fe,
  0xbc1909e94b3ec93baa74f36ebd6d8af38edf6983a8574ca91d3bbb68845f864c744ae35809ccfe7b2f5cdc407df6c0bc8a808, 0x1d13c9a086b44b09841f60a3f4a2a03d9fdfb5d1111f1a4ba754fcc0c28e5ce345022df4669493af5e2193a3f09bbaf6cb17ace, 0x3991b998a097c0235a1871844c79eed3586b46d73eee6a057a47ef18f19afcba88309496105423b0298568f38f82393f798f5d40,
  0x5c546ddf07611fc2879082179d3ce81e3edf90b7d70dfb8a0409575b2193b76074d224dab1d43840d4d6420d3405fe83259aee139, 0x7934e6cb74fbedcceabaa2ae619cb4e68b02c8bc24daa6bca4cac28aac49061665f9cbf7c4b044eb4cef8cead70426da4f324f05f4, 0x836f5df62aa153b1c6fb9bbf266c7fe03a79c0261990913d87d64f17d913892a08405b6d9d3151ce1ad73980d05dce9510c34eff7d5,
  0x76af1a9c4b3a0f973fa8c2ffaebc6981d0136378b83e81f128ce4341c5db8e980bb5585e41c810ae6f01229b4c2d62bef6c1b5710200, 0x59e123c22a369aa210fb037729e554244f09cae6cef421ed35e521994d89e026e63b4f2aa092d4a55bf07e837cfa11835873dd8e29df0, 0x397202d731d2472232ba785cb1daaab8b6171c233c669e926db899f45e1cbe30e9d0eb2aabd4ec28fffc3d70ebdefe19694dcfec499b40,
  0x1f29245b9d69005a06570cbb3f9831e828ea98a937d6165bc9b8e4c167c04f84599fd3b1f2c8dbb7e59b8361fde7eec0f4d4468c9fe60f0, 0xe6ac8ed67d2d6b966da47fbd3bc879b6e689e4eea1956cd0df85cbcb74f1b9b543cbff5d6bb9de09018f7ae25795c3280c5c7bd3f750200, 0x5b6f3e302d5c9f4d11455ad9db60adb043e1ac77f3383f277378f6a22fdd4197a764e4f31730e929038f1cc94f17195067990ae2d4c7367a,
  0x1f2c1cc3e986e7d75c3e2692c67c3189b0597859f2500a2163ccd41fb7df9981576aff0a087c54c1f871ce708ff2d46c1ada85d1c10966ea8, 0x92c2b92f22f773dbddd14c556343a3fe717eddfbafee5ae1d280760b92489cac4e6d59ac7b256fa5b86b46b1e20cdfb929c0b030dff3d71c2, 0x2563554b2f85f68f363b8b269b286824a03680259f9391d7da439984ad8ffa390f8481204125207d47aed08b8bc15d81f612af3a265c10b880,
  0x844cc48ac9428c057b94117126dcbafe8bd1ce5321514300d615d8a0953c56a15415ce5e002438e8caa8e7cae083b639102fb1b19139ba24ac, 0x19762f204d207345fc35882a7889bc2e090ee0ea8f7b84f39bf2559d3729ca0670169a96c969b9079e6a40453e530009d6b44209ae61f3a8ed0, 0x445e517e22769afe5eaf462f6a2a9f8ea3de56f0cd4c7d2ed516feec6ca40cc97e27e2cf9b6b3c7437341fa407e0d5f2c32895882b0f4d9f90c,
  0xa05ea7248bee16c73d2eeb74349ac2601bf12daa7a55d0121f1565052b2699b17cef349bc028827357fcc86a2ac9f44429c9815d648454d1080, 0x1491d03fc368549aec53471cdb3e3129d8cc956c3a8dd774b2e1738e481fc55edaaeef5e7cd01bf3efe2c28d47411203fec56b825978addb7abe, 0x24fa8db7b77106950d4f2893048685c080d63a1541ee7295928826ede29a71284d44d08817efcb6b28b7bebbdc6103503c1d16bd8512f8575198,
  0x3a4b39098b6633c00067caa92ed2b290fac13a46710fb78d2cf931e6a392b7554e923e2483541288b444b55e1d25ab2d279c857ea685c4a5dd66, 0x50a513eae1ec7d937d975d57bf29dd7de19901cf39d428ced8edcb761c213d46b9187f25259a6d60e04a2737b57f430a50dcd6828560d5fcd100, 0x61f608e9294f3d5186364af8535ab3bac2a190002c8dc9165ab05e4e7ca98b01644579b8a6dfed29001eaa47bbb12b33109dec2bfba949dc9838,
  0x6884f3be7ca05d11d8b3a2f5eb04b381be218a834bb0308b51d9f584d309f8b64554388cdc262340dd9b601625c1b0d272cb554e5f90f300c3a0, 0x61f608e9294f3d5186364af8535ab3bac2a190002c8dc9165ab05e4e7ca98b01644579b8a6dfed29001eaa47bbb12b33109dec2bfba949dc9838, 0x50a513eae1ec7d937d975d57bf29dd7de19901cf39d428ced8edcb761c213d46b9187f25259a6d60e04a2737b57f430a50dcd6828560d5fcd100,
  0x3a4b39098b6633c00067caa92ed2b290fac13a46710fb78d2cf931e6a392b7554e923e2483541288b444b55e1d25ab2d279c857ea685c4a5dd66, 0x24fa8db7b77106950d4f2893048685c080d63a1541ee7295928826ede29a71284d44d08817efcb6b28b7bebbdc6103503c1d16bd8512f8575198, 0x1491d03fc368549aec53471cdb3e3129d8cc956c3a8dd774b2e1738e481fc55edaaeef5e7cd01bf3efe2c28d47411203fec56b825978addb7abe,
  0xa05ea7248bee16c73d2eeb74349ac2601bf12daa7a55d0121f1565052b2699b17cef349bc028827357fcc86a2ac9f44429c9815d648454d1080, 0x445e517e22769afe5eaf462f6a2a9f8ea3de56f0cd4c7d2ed516feec6ca40cc97e27e2cf9b6b3c7437341fa407e0d5f2c32895882b0f4d9f90c, 0x19762f204d207345fc35882a7889bc2e090ee0ea8f7b84f39bf2559d3729ca0670169a96c969b9079e6a40453e530009d6b44209ae61f3a8ed0,
  0x844cc48ac9428c057b94117126dcbafe8bd1ce5321514300d615d8a0953c56a15415ce5e002438e8caa8e7cae083b639102fb1b19139ba24ac, 0x2563554b2f85f68f363b8b269b286824a03680259f9391d7da439984ad8ffa390f8481204125207d47aed08b8bc15d81f612af3a265c10b880, 0x92c2b92f22f773dbddd14c556343a3fe717eddfbafee5ae1d280760b92489cac4e6d59ac7b256fa5b86b46b1e20cdfb929c0b030dff3d71c2,
  0x1f2c1cc3e986e7d75c3e2692c67c3189b0597859f2500a2163ccd41fb7df9981576aff0a087c54c1f871ce708ff2d46c1ada85d1c10966ea8, 0x5b6f3e302d5c9f4d11455ad9db60adb043e1ac77f3383f277378f6a22fdd4197a764e4f31730e929038f1cc94f17195067990ae2d4c7367a, 0xe6ac8ed67d2d6b966da47fbd3bc879b6e689e4eea1956cd0df85cbcb74f1b9b543cbff5d6bb9de09018f7ae25795c3280c5c7bd3f750200,
  0x1f29245b9d69005a06570cbb3f9831e828ea98a937d6165bc9b8e4c167c04f84599fd3b1f2c8dbb7e59b8361fde7eec0f4d4468c9fe60f0, 0x397202d731d2472232ba785cb1daaab8b6171c233c669e926db899f45e1cbe30e9d0eb2aabd4ec28fffc3d70ebdefe19694dcfec499b40, 0x59e123c22a369aa210fb037729e554244f09cae6cef421ed35e521994d89e026e63b4f2aa092d4a55bf07e837cfa11835873dd8e29df0,
  0x76af1a9c4b3a0f973fa8c2ffaebc6981d0136378b83e81f128ce4341c5db8e980bb5585e41c810ae6f01229b4c2d62bef6c1b5710200, 0x836f5df62aa153b1c6fb9bbf266c7fe03a79c0261990913d87d64f17d913892a08405b6d9d3151ce1ad73980d05dce9510c34eff7d5, 0x7934e6cb74fbedcceabaa2ae619cb4e68b02c8bc24daa6bca4cac28aac49061665f9cbf7c4b044eb4cef8cead70426da4f324f05f4,
  0x5c546ddf07611fc2879082179d3ce81e3edf90b7d70dfb8a0409575b2193b76074d224dab1d43840d4d6420d3405fe83259aee139, 0x3991b998a097c0235a1871844c79eed3586b46d73eee6a057a47ef18f19afcba88309496105423b0298568f38f82393f798f5d40, 0x1d13c9a086b44b09841f60a3f4a2a03d9fdfb5d1111f1a4ba754fcc0c28e5ce345022df4669493af5e2193a3f09bbaf6cb17ace,
  0xbc1909e94b3ec93baa74f36ebd6d8af38edf6983a8574ca91d3bbb68845f864c744ae35809ccfe7b2f5cdc407df6c0bc8a808, 0x3c0c351c44d02306b6797f6f7691b426dd22df9faa37f6948a9e95130a136db10e55529ffcefafdbc620a3e649d1ea7fa3fe, 0xee5f7958e1247af6adc85345666cbc131a0ae329cbb60901c0a5be094176fc7364537d6b5034df5e75ddb24b582e582940,
  0x2d20176826a5644ba0dcc01266567c49379d40ddfd992659749b1ef0e69396e9909b06fadab26c3b3df323981f2011567, 0x660e1b5883099375b7be97c73b95d105c08a391d38d2abd70416fb5ff595c98055ee509d717deac4f58ee462deff02c, 0xa7fb8db92aae9ccec3dfbec0b9b4e6da03f00fff3ca5df74e24ae6844e3104a06a95868995f8e9efb41cecfa7debb,
  0xc32d794241fbd09ed443baabd97819569d3975aa553d7b3c49c67bef2fd9f306bd9ea247427bba705695cc51580, 0x9a4650393be9794fdf1528ccdc4664501220b5fb6663fd980d203ef1eedae93ea4a85703c61c6945ac60b46b4, 0x4f4c074b875dbb9929b5c3f74667bb438f0317ed4aa2b23750147db488de3734a8a1de4659527fec714faf0,
  0x191026c9a1ad6404e0049bd0e9b9c21ea873fcc7011f92d2ddab8cb46c8567aaca08da167639da48f5634, 0x48a57ac297a9111f949b0855492dbc5458d40b461676a0f55c458e4382392afc5ff1506346c8239580, 0x6e501bbe4a05983ffd56797fe25b68a780138296a83abcc1f3c6792f1cdcc316cad02c4901c3d8f,
  0x4e0cf225eb7b6d431fc9e2cab79624fbd1a5b0d65a1bd794103d112cc47bc7644741221349fc, 0x160322bc1ca85401a8ad6794aaedb33967375e4150dd2d4c4adc8a9c9f6eaa01c039755cb, 0x1ffc0517c9c9cd62df1513f62fb0ab06a5d7379d81d1189fb0ce9d6497b49fcec6640,
  0xb131cf16ef1701fcfe43aa92dc8c34deea3d4a12dbd329ce7df0c29be7b00476, 0x96498c8a066561e7813dcdaa3e2a0b76a02939625a0eee7ee111cddd128, 0x9d1749bdcec0e5ae9132f25c6a31ae6fb7846923e975acd528b06,
  0x3fffffff93fafa69274b722a07fd55aabe431fca02ca40, 0x12c9389fcca4e0069a6fc4946479e435e9f15, 0x7ffffffffffffffffffffa4,
  0x1]

private theorem eulerianCoefficients_eq : descentCoeffs 91 = eulerianCoefficients := by
  decide +kernel

private theorem upper : upperOK (descentCoeffs 91) first gaps = true := by
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

private theorem lower (i : Fin (lastRepresentative 92 - 2)) :
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

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 92) :
    StrictNegativeInterlacing (originalQuotient 92 k) (eulerian 91) 89 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N092
