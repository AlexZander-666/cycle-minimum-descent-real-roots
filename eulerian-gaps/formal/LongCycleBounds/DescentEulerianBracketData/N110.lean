import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentPackedData.C127L112.N110

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N110

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L112.N110 LongCycleBounds.DescentNecklace.Packed.C127L112.N110.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L112.N110 LongCycleBounds.DescentNecklace.Packed.C127L112.N110.rows

private theorem actual : RepresentativeChecks 110 previousNodes rows :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L112.N110 LongCycleBounds.DescentNecklace.Packed.C127L112.N110.dataChecks

private def first : LongCycleFinite.Dyadic := ⟨-649037107316853453566312041152512, 0⟩

private def gaps : List Window := [
  ⟨⟨-649016062336185602101638756040704, 0⟩, ⟨-15646384714787323904, 0⟩⟩,
  ⟨⟨-15628335131905753088, 0⟩, ⟨-42004377501696, 0⟩⟩,
  ⟨⟨-41353958391808, 0⟩, ⟨-36987731968, 0⟩⟩,
  ⟨⟨-35100295168, 0⟩, ⟨-412049408, 0⟩⟩,
  ⟨⟨-410271744, 0⟩, ⟨-18423936, 0⟩⟩,
  ⟨⟨-18403904, 0⟩, ⟨-1870800, 0⟩⟩,
  ⟨⟨-1869936, 0⟩, ⟨-323239, 0⟩⟩,
  ⟨⟨-323155, 0⟩, ⟨-80300, 0⟩⟩,
  ⟨⟨-321147, 2⟩, ⟨-413699, 4⟩⟩,
  ⟨⟨-413651, 4⟩, ⟨-161367, 4⟩⟩,
  ⟨⟨-322705, 5⟩, ⟨-145613, 5⟩⟩,
  ⟨⟨-145603, 5⟩, ⟨-294311, 7⟩⟩,
  ⟨⟨-147147, 6⟩, ⟨-325371, 8⟩⟩,
  ⟨⟨-325355, 8⟩, ⟨-386691, 9⟩⟩,
  ⟨⟨-386675, 9⟩, ⟨-487589, 10⟩⟩,
  ⟨⟨-487571, 10⟩, ⟨-322833, 10⟩⟩,
  ⟨⟨-161411, 9⟩, ⟨-222697, 10⟩⟩,
  ⟨⟨-222691, 10⟩, ⟨-318067, 11⟩⟩,
  ⟨⟨-318059, 11⟩, ⟨-467909, 12⟩⟩,
  ⟨⟨-467899, 12⟩, ⟨-44127, 9⟩⟩,
  ⟨⟨-22063, 8⟩, ⟨-136123, 11⟩⟩,
  ⟨⟨-17015, 8⟩, ⟨-428001, 13⟩⟩,
  ⟨⟨-213997, 12⟩, ⟨-85527, 11⟩⟩,
  ⟨⟨-171051, 12⟩, ⟨-277505, 13⟩⟩,
  ⟨⟨-277501, 13⟩, ⟨-228043, 13⟩⟩,
  ⟨⟨-28505, 10⟩, ⟨-379141, 14⟩⟩,
  ⟨⟨-379135, 14⟩, ⟨-79607, 12⟩⟩,
  ⟨⟨-39803, 11⟩, ⟨-67475, 12⟩⟩,
  ⟨⟨-33737, 11⟩, ⟨-230655, 14⟩⟩,
  ⟨⟨-461305, 15⟩, ⟨-397157, 15⟩⟩,
  ⟨⟨-12411, 10⟩, ⟨-344201, 15⟩⟩,
  ⟨⟨-344197, 15⟩, ⟨-300099, 15⟩⟩,
  ⟨⟨-4689, 9⟩, ⟨-131535, 14⟩⟩,
  ⟨⟨-263067, 15⟩, ⟨-463481, 16⟩⟩,
  ⟨⟨-115869, 14⟩, ⟨-205049, 15⟩⟩,
  ⟨⟨-205047, 15⟩, ⟨-364325, 16⟩⟩,
  ⟨⟨-364321, 16⟩, ⟨-162419, 15⟩⟩,
  ⟨⟨-324835, 16⟩, ⟨-145293, 15⟩⟩,
  ⟨⟨-290583, 16⟩, ⟨-521441, 17⟩⟩,
  ⟨⟨-521437, 17⟩, ⟨-234555, 16⟩⟩,
  ⟨⟨-234553, 16⟩, ⟨-423055, 17⟩⟩,
  ⟨⟨-423051, 17⟩, ⟨-95589, 15⟩⟩,
  ⟨⟨-23897, 13⟩, ⟨-86561, 15⟩⟩,
  ⟨⟨-346241, 17⟩, ⟨-39261, 14⟩⟩,
  ⟨⟨-314085, 17⟩, ⟨-142679, 16⟩⟩,
  ⟨⟨-285355, 17⟩, ⟨-519211, 18⟩⟩,
  ⟨⟨-519207, 18⟩, ⟨-59113, 15⟩⟩,
  ⟨⟨-472901, 18⟩, ⟨-53895, 15⟩⟩,
  ⟨⟨-107789, 16⟩, ⟨-196713, 17⟩⟩,
  ⟨⟨-393423, 18⟩, ⟨-359237, 18⟩⟩,
  ⟨⟨-179617, 17⟩, ⟨-328189, 18⟩⟩,
  ⟨⟨-164093, 17⟩, ⟨-299935, 18⟩⟩,
  ⟨⟨-74983, 16⟩, ⟨-274175, 18⟩⟩,
  ⟨⟨-68543, 16⟩, ⟨-501287, 19⟩⟩,
  ⟨⟨-501283, 19⟩, ⟨-229117, 18⟩⟩,
  ⟨⟨-229115, 18⟩, ⟨-418783, 19⟩⟩,
  ⟨⟨-418779, 19⟩, ⟨-191295, 18⟩⟩,
  ⟨⟨-382587, 19⟩, ⟨-349341, 19⟩⟩,
  ⟨⟨-174669, 18⟩, ⟨-318769, 19⟩⟩,
  ⟨⟨-159383, 18⟩, ⟨-290629, 19⟩⟩,
  ⟨⟨-145313, 18⟩, ⟨-132355, 18⟩⟩,
  ⟨⟨-264707, 19⟩, ⟨-481639, 20⟩⟩,
  ⟨⟨-481635, 20⟩, ⟨-437583, 20⟩⟩,
  ⟨⟨-109395, 18⟩, ⟨-396945, 20⟩⟩,
  ⟨⟨-198471, 19⟩, ⟨-11233, 15⟩⟩,
  ⟨⟨-359453, 20⟩, ⟨-324875, 20⟩⟩,
  ⟨⟨-40609, 17⟩, ⟨-73245, 18⟩⟩,
  ⟨⟨-146489, 19⟩, ⟨-263577, 20⟩⟩,
  ⟨⟨-131787, 19⟩, ⟨-472975, 21⟩⟩,
  ⟨⟨-472971, 21⟩, ⟨-211553, 20⟩⟩,
  ⟨⟨-211551, 20⟩, ⟨-188623, 20⟩⟩,
  ⟨⟨-188621, 20⟩, ⟨-83785, 19⟩⟩,
  ⟨⟨-10473, 16⟩, ⟨-74135, 19⟩⟩,
  ⟨⟨-296537, 21⟩, ⟨-261225, 21⟩⟩,
  ⟨⟨-522445, 22⟩, ⟨-457981, 22⟩⟩,
  ⟨⟨-457977, 22⟩, ⟨-49913, 19⟩⟩,
  ⟨⟨-99825, 20⟩, ⟨-346063, 22⟩⟩,
  ⟨⟨-346059, 22⟩, ⟨-18621, 18⟩⟩,
  ⟨⟨-74483, 20⟩, ⟨-254613, 22⟩⟩,
  ⟨⟨-509221, 23⟩, ⟨-431625, 23⟩⟩,
  ⟨⟨-107905, 21⟩, ⟨-181253, 22⟩⟩,
  ⟨⟨-362501, 23⟩, ⟨-301351, 23⟩⟩,
  ⟨⟨-150673, 22⟩, ⟨-495275, 24⟩⟩,
  ⟨⟨-123817, 22⟩, ⟨-401745, 24⟩⟩,
  ⟨⟨-401739, 24⟩, ⟨-321121, 24⟩⟩,
  ⟨⟨-321115, 24⟩, ⟨-504849, 25⟩⟩,
  ⟨⟨-63105, 22⟩, ⟨-389333, 25⟩⟩,
  ⟨⟨-389325, 25⟩, ⟨-293733, 25⟩⟩,
  ⟨⟨-293727, 25⟩, ⟨-216057, 25⟩⟩,
  ⟨⟨-432105, 26⟩, ⟨-308591, 26⟩⟩,
  ⟨⟨-38573, 23⟩, ⟨-425737, 27⟩⟩,
  ⟨⟨-425727, 27⟩, ⟨-281889, 27⟩⟩,
  ⟨⟨-281881, 27⟩, ⟨-22215, 24⟩⟩,
  ⟨⟨-177715, 27⟩, ⟨-211217, 28⟩⟩,
  ⟨⟨-422421, 29⟩, ⟨-116751, 28⟩⟩,
  ⟨⟨-116747, 28⟩, ⟨-471955, 31⟩⟩,
  ⟨⟨-471937, 31⟩, ⟨-425899, 32⟩⟩,
  ⟨⟨-425881, 32⟩, ⟨-83061, 31⟩⟩,
  ⟨⟨-83057, 31⟩, ⟨-213971, 34⟩⟩,
  ⟨⟨-26745, 31⟩, ⟨-425291, 37⟩⟩,
  ⟨⟨-425265, 37⟩, ⟨-146965, 38⟩⟩,
  ⟨⟨-146955, 38⟩, ⟨-477905, 43⟩⟩,
  ⟨⟨-477871, 43⟩, ⟨-10689, 42⟩⟩,
  ⟨⟨-342023, 47⟩, ⟨-248993, 53⟩⟩,
  ⟨⟨-497947, 54⟩, ⟨-444635, 64⟩⟩,
  ⟨⟨-222299, 63⟩, ⟨-309399, 82⟩⟩,
  ⟨⟨-309369, 82⟩, ⟨-262149, 127⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private def eulerianCoefficients : List ℤ := [
  0x1, 0x1fffffffffffffffffffffffff92, 0x1b1ced3c631df90d67aa80f569315ae09c9b649bb5be,
  0x3fffffffff45992100d691ef94254bc968ccccaf37cb53ac51ead4a, 0x22104d3dec21962c8ebd2fcada45161f8f2c388a7c5cb0ac44f341e2e6189d47, 0x3639d98e9628e288a86c8fa0f648c23669eda1af971a57ed005ccb47fd69da5a3d1b634,
  0x401312b0a637b8bc620d4e447b7c0ced4db8b15f74ee9c38a63b681bad428a3ccfae401ef3474, 0x7ffe477c8eaeef76dcefeacc72824a652f121c7afcbebd495ae31bcd998ef4f1781ec470a90134aaf4, 0x2dee64fdbbee03a5d4074cdf5cbcf4de260404c0ed2e3ee7d3988ea3ceaaf35407529fcac517d287fe56e8b,
  0x440cdd511cee29135d1e28a436c15fd14e28b01df550dbf1dafb8228111f765f986573a3c68a2ddff75c852cd52, 0x21aa1e073ea3e5fb366f1dcf3ec55ba3eaa48b2a8e534c56ad6699fe2d527579808164d1916c3be6356b5a15c683636, 0x6b8bddebb2078f31e0e8523f12c978970b6f1f48af9142a4baebf5100216337724ae18bd034968992b43bb7830c7295dfa,
  0xa002610fcb77bf9d1c1e38f6c86fa95df02350d19dce6565dc7e3ca9333d832c2f0270b29e78a843873da19b98355baa1cc9d, 0x7bd0379256dcba1392a87dd632464558ceeab2e5fdb72f07cccc1f37e8dd228bb3ef1cdf67fbf413315dcb9d639457972e079690, 0x3656e130865b75a599e06d5d971c28603c274d22a5173ef0bd60e10806f41372761aee38fb5515539344f3ae788b670e242d96f0d50,
  0xe7ebf1a582eeca6cae0c04533a11d93780018b957c0509552995dab52d6568b2954030a3b9f9d469db38133417787aff4eb45c3587d10, 0x27c3d5f5c7e7d2ff71b41f70abbf5e2338ff384fe6a29d18af8206e3ffdd5d7f080a893a78844637f24d2269a2cbaf11e90850c2feee8dbe, 0x4967d7d848c0a0af6a6b97e21094a645ded483591fed7c98815e37e099d786d10b933fe11c0ec0657361fbf094726af1c34b4bb919dd157b4c,
  0x5eb54e336e4b566259ecfd907617d32d7c13c8d97399abf477e063a5b0855054e724fc3a94dec600aea835794f198524e7c2f0afbe6e1b92e9b4, 0x5828c692bc6c4e57d9a0cbadcba8ac61b1d3034293ceafe90e86721dfca6c5c5f4f1a9561a379a0c5ffa42c481d7e09ea36513f369ca2b9dfd645c, 0x3cd109928bf4635d046645fdf2c1d72679dab8c5d4dc93824cab6d3a21f5c4add4fdc54766283c68b0a622206326e11e55f55353472e71e1a82cf832,
  0x1fcf97bc021685917a8594164a282b2606315c6db6f74cb13a134089d9fc3f41871d27309c4280bd98b76488c632e4a7f1bd46164849b2c1b81943e628, 0xcddc83deca84d0d7ed831b5ef51af7262f7a8d16f34fb2a97af3d575fcb0929d15fe00e42c83102872d831dc5384933535987cd5dab4a638ee7e491e268, 0x417c74c828359db7f26202d579296965a8699208ab9685b08921f60a7b032fc96e344abf151fc4a313fcd3972a562cc3b407f14caa9d36f16611c53a34728,
  0x10a0b8e036b71a6ba610f188158614f95cf00bb7cd7639fa29057d621f967c4de14892b37f908a7ec8b4ebcec9253588d1a6d909aafe1ccfa0c36eae34dc122, 0x369f440ddad8ab7c1387fff1ca728ea93154093195e0812717f83233c0a6f53d5a6d260b5d7a0227b0bcce029192a0cd8d7e34c13b05a97e5a4b6dc98c03ac3c, 0x92bf7b5edb1f7b454373d5f06a65a720e28572be9dcc7360119aae454d50a9c81e9f7ad6e69524efb0f9012d2e6283055d40959d9d67497d3846c8557426d8bd4,
  0x145b2f14ca8aa42200d72bce70055fffec071d40b5636aff11d9264b963d96ab0a06c2431a85168943c6cff5909ba0440abbfd11b57696be2099d49a779e089c1ac, 0x25a8937af8b77ad726012095465443094f6d8009e4421609f8ac677fdf565dfc42c0c9c8e591508aada43da30df817464414af5a2644dc96f8e149afaaab6e0e814e, 0x3a88d75a617eea5402ae31046a051ee33c5687280734088961a9304436ed0f31b47b2791e7c6f74a35b2893da846ca1c181c9c22805fe29c44199bd57445ec61e0ed0,
  0x4cfdaa0d7b1d95a59ea6a15ad165358446a5ed576a8f06bf80aa18cd17484eb96b0a539620158d83153fed7d532e993f05c949870aed5ef5b81f67f75f6e1a16062810, 0x563e16a63a6e9ccc6d172bc55e3bf442d9304818fe56bc3a58f2d58f5cc70bcfdf6e3aaa359ee29e69167451835f27f8c2875216e787d6a89c8e06404ab21f14a015650, 0x52bf79aa3e5dc6b90554245afa4da5c05d44650c39126a13f6fd11f4c2446e4d7c4b016bf80875805fe14f142bf68452c9daf8b50b583af9c5270bda4b851a22cf7d2c9b,
  0x445c08bf46f31c47ddd1604d08ba4619b8ed79e68aeef320cc2091ae79ae6c4b2fc3e35b5365ea1c42abc5bcafa0f52c235291d27fa30869bf5482ae7342e29e77a20df16, 0x30da1343839c4b6d1776253c882d754a0ecc146d69bb6f6cac8caf5d23db11577cbc6883b518713f26430b93e79eb79832b36c851d703b1293a353f9e7f7e13af3361377fa, 0x1e53f8da842967d7c4bd7df675d3112c1e34e9b1baa92d7af6787cce32e5e504c26245540370878c71b05d068a6818bd9dccc094197ede08e0ad7fdfe5219e7c1c057cfb0fe,
  0x106b56173f02498ba92dad6d0a4b1fe70a8c2d783156192d4cf99e89bf34775f6b3340893ce39c7c82e2090496f6b447280f911b5358337588509f55499ebd19c495251895fd, 0x7c769f8243a9c845a5fe4cd622546542f3330ce3e6b432dda93ef8f54b625ec4a0a510a25d975ffbadedd7cc304bdca202e20a540c95c52e1396c577fb5c300ecd3ace3d644c, 0x33c3cb26b9cf97ff498f6f571e6ec61e7d40615a48f039bfb86b610fc6329db285cd1e34c81ac0bb44ae41d6f7c6c2ee82e3bfbe6fd42905e02c2122c7b67c0f96bb3606c424c,
  0x12f42437855573c11f311aad899d4d7526c92c3682a7433321a4a0d8e82906bd5ee518a4adc4ce3c9aa2c0eca74a32be7e375e4723e4965a1e5649abb4dd3f29cf060b215d040c, 0x6201fc92aafdb9c2840374612084a1e55557af4723a12059f74c57cf53745ad104c9e52febc893acb5d4262dd470601883a5b356ac73829fccc5418ead11db0c2c0b5935c65c51, 0x1c05d1e1ebf0d1d3f425b5d78dbfbb575d581fa2dc80a55f29ef31a70e05ddc0a632c8e3797468dfb8470db5fe9191d234e6ac9631db925b6fcb884f6a2d495e758cabc3dc1d926,
  0x71a8639a341453f0b3ea51508405d88daa0a8bab331866892b4c765f8fc87a80f9ef41f32fadbf00899c5f01eae02ea5ed79e3422a77352ff634479a6fabc47e392c08513361a52, 0x1997a380e2e74ca71008c95ca3c7afd3babc5492ff8325b80ad3ca32ff87b609a2aa48d859cbf95f87d5d99b2d01994f30acbe47d500c82822c97e1b26f0278086fd769a55d46f1e, 0x520a0343f48c6f62f5c9b25975b894401b27b7858cf6d3b5895ee79a00816887b49d462c29423596e6d11461595da3ae11778d6fea484749e99ac163dc6fb4203071c3b7110a33a7,
  0xea5a48cd7e1c951ae0c709d9eb2187da6cd12777e00864ab2d8047d59a9f19e4e093d09c0a8424557c1d250bbd9896685b84da8ab9fa6c858cbd9f7e12d955295607a699b0c71f20, 0x2555d46cfc0cd0f7a293805e47073b52bb9e154d47a6d90e9efb0c5772ed905bab5ebc560d364afe9f26da1f87b3353d2f058e4bae1cea87682519aa23979bfcd202524971cbdbaa0, 0x5505151d850bfda528dbe7d898f0075d02db8ea279f557ef7c725ef7f65ff6bdfa220372868eb9cc190e92d7ca62c2efb31aea0d40d81590b1e99e0aca76aa6552b664db0cc7a4820,
  0xad23bda2470c81db263ba607d17d6e5b6e67b3245a40b4e487095a5a8385353afea71b330c9e9502aab6f39310914e2f510baa8cb11f4a465905ed4162f44626a5a7874246792d414, 0x13b979a2a8df8dac1a4cc737098c3bc5d7cad57cb28bb7304668a22d18fa14255482b7004e759341c3b1dc82d63c5280a9a50efc1ace718c9adf5ba8909ae9afd2b078177f343c5748, 0x203427c4746ee6e1026b7e9913d98c31431955ec95a116091ec4b385919888912dccc38f67f29608f28bd5cf7d7ce22a47fec9d70b0b691dbd6252284581b3075b4d9a7198c5b20c38,
  0x2f1f79357292fa0c8c79b0d43aa5cfc390edfaa21be89e69f5ac3b64274c24810db17e7407a6cb5460d5532ad83066d22fb11df643ec177cea3bf85f31515d936a48a88436e601aaa8, 0x3dd3de6cf7fe8015c7adbf4f8af615e2f13dda8bdaaca4876f99e0f417fbc720c7786b80197129097831c55d90fe2b3050812d537bf07078124ff431725010568ae159f77743ef388c, 0x48c2baf8e02435dcc185acdedbe850b11bf1ef82e1dbc78d58618878204dc9e12590fce9d067f8c09c4e2bd9e1ba49dafff5a66191a2c1ac9c949a3cd1c7875b3031d6d000c3b72930,
  0x4cd137682193cc48aec14444470168ff65ff45b40782b84f8f1aad765e52998c4712f3ce8ed973cefc161aa4e4ac79b70aa41d426b26523f995ab729b5486e43ea4cfd24f2fdbf6db0, 0x48c2baf8e02435dcc185acdedbe850b11bf1ef82e1dbc78d58618878204dc9e12590fce9d067f8c09c4e2bd9e1ba49dafff5a66191a2c1ac9c949a3cd1c7875b3031d6d000c3b72930, 0x3dd3de6cf7fe8015c7adbf4f8af615e2f13dda8bdaaca4876f99e0f417fbc720c7786b80197129097831c55d90fe2b3050812d537bf07078124ff431725010568ae159f77743ef388c,
  0x2f1f79357292fa0c8c79b0d43aa5cfc390edfaa21be89e69f5ac3b64274c24810db17e7407a6cb5460d5532ad83066d22fb11df643ec177cea3bf85f31515d936a48a88436e601aaa8, 0x203427c4746ee6e1026b7e9913d98c31431955ec95a116091ec4b385919888912dccc38f67f29608f28bd5cf7d7ce22a47fec9d70b0b691dbd6252284581b3075b4d9a7198c5b20c38, 0x13b979a2a8df8dac1a4cc737098c3bc5d7cad57cb28bb7304668a22d18fa14255482b7004e759341c3b1dc82d63c5280a9a50efc1ace718c9adf5ba8909ae9afd2b078177f343c5748,
  0xad23bda2470c81db263ba607d17d6e5b6e67b3245a40b4e487095a5a8385353afea71b330c9e9502aab6f39310914e2f510baa8cb11f4a465905ed4162f44626a5a7874246792d414, 0x5505151d850bfda528dbe7d898f0075d02db8ea279f557ef7c725ef7f65ff6bdfa220372868eb9cc190e92d7ca62c2efb31aea0d40d81590b1e99e0aca76aa6552b664db0cc7a4820, 0x2555d46cfc0cd0f7a293805e47073b52bb9e154d47a6d90e9efb0c5772ed905bab5ebc560d364afe9f26da1f87b3353d2f058e4bae1cea87682519aa23979bfcd202524971cbdbaa0,
  0xea5a48cd7e1c951ae0c709d9eb2187da6cd12777e00864ab2d8047d59a9f19e4e093d09c0a8424557c1d250bbd9896685b84da8ab9fa6c858cbd9f7e12d955295607a699b0c71f20, 0x520a0343f48c6f62f5c9b25975b894401b27b7858cf6d3b5895ee79a00816887b49d462c29423596e6d11461595da3ae11778d6fea484749e99ac163dc6fb4203071c3b7110a33a7, 0x1997a380e2e74ca71008c95ca3c7afd3babc5492ff8325b80ad3ca32ff87b609a2aa48d859cbf95f87d5d99b2d01994f30acbe47d500c82822c97e1b26f0278086fd769a55d46f1e,
  0x71a8639a341453f0b3ea51508405d88daa0a8bab331866892b4c765f8fc87a80f9ef41f32fadbf00899c5f01eae02ea5ed79e3422a77352ff634479a6fabc47e392c08513361a52, 0x1c05d1e1ebf0d1d3f425b5d78dbfbb575d581fa2dc80a55f29ef31a70e05ddc0a632c8e3797468dfb8470db5fe9191d234e6ac9631db925b6fcb884f6a2d495e758cabc3dc1d926, 0x6201fc92aafdb9c2840374612084a1e55557af4723a12059f74c57cf53745ad104c9e52febc893acb5d4262dd470601883a5b356ac73829fccc5418ead11db0c2c0b5935c65c51,
  0x12f42437855573c11f311aad899d4d7526c92c3682a7433321a4a0d8e82906bd5ee518a4adc4ce3c9aa2c0eca74a32be7e375e4723e4965a1e5649abb4dd3f29cf060b215d040c, 0x33c3cb26b9cf97ff498f6f571e6ec61e7d40615a48f039bfb86b610fc6329db285cd1e34c81ac0bb44ae41d6f7c6c2ee82e3bfbe6fd42905e02c2122c7b67c0f96bb3606c424c, 0x7c769f8243a9c845a5fe4cd622546542f3330ce3e6b432dda93ef8f54b625ec4a0a510a25d975ffbadedd7cc304bdca202e20a540c95c52e1396c577fb5c300ecd3ace3d644c,
  0x106b56173f02498ba92dad6d0a4b1fe70a8c2d783156192d4cf99e89bf34775f6b3340893ce39c7c82e2090496f6b447280f911b5358337588509f55499ebd19c495251895fd, 0x1e53f8da842967d7c4bd7df675d3112c1e34e9b1baa92d7af6787cce32e5e504c26245540370878c71b05d068a6818bd9dccc094197ede08e0ad7fdfe5219e7c1c057cfb0fe, 0x30da1343839c4b6d1776253c882d754a0ecc146d69bb6f6cac8caf5d23db11577cbc6883b518713f26430b93e79eb79832b36c851d703b1293a353f9e7f7e13af3361377fa,
  0x445c08bf46f31c47ddd1604d08ba4619b8ed79e68aeef320cc2091ae79ae6c4b2fc3e35b5365ea1c42abc5bcafa0f52c235291d27fa30869bf5482ae7342e29e77a20df16, 0x52bf79aa3e5dc6b90554245afa4da5c05d44650c39126a13f6fd11f4c2446e4d7c4b016bf80875805fe14f142bf68452c9daf8b50b583af9c5270bda4b851a22cf7d2c9b, 0x563e16a63a6e9ccc6d172bc55e3bf442d9304818fe56bc3a58f2d58f5cc70bcfdf6e3aaa359ee29e69167451835f27f8c2875216e787d6a89c8e06404ab21f14a015650,
  0x4cfdaa0d7b1d95a59ea6a15ad165358446a5ed576a8f06bf80aa18cd17484eb96b0a539620158d83153fed7d532e993f05c949870aed5ef5b81f67f75f6e1a16062810, 0x3a88d75a617eea5402ae31046a051ee33c5687280734088961a9304436ed0f31b47b2791e7c6f74a35b2893da846ca1c181c9c22805fe29c44199bd57445ec61e0ed0, 0x25a8937af8b77ad726012095465443094f6d8009e4421609f8ac677fdf565dfc42c0c9c8e591508aada43da30df817464414af5a2644dc96f8e149afaaab6e0e814e,
  0x145b2f14ca8aa42200d72bce70055fffec071d40b5636aff11d9264b963d96ab0a06c2431a85168943c6cff5909ba0440abbfd11b57696be2099d49a779e089c1ac, 0x92bf7b5edb1f7b454373d5f06a65a720e28572be9dcc7360119aae454d50a9c81e9f7ad6e69524efb0f9012d2e6283055d40959d9d67497d3846c8557426d8bd4, 0x369f440ddad8ab7c1387fff1ca728ea93154093195e0812717f83233c0a6f53d5a6d260b5d7a0227b0bcce029192a0cd8d7e34c13b05a97e5a4b6dc98c03ac3c,
  0x10a0b8e036b71a6ba610f188158614f95cf00bb7cd7639fa29057d621f967c4de14892b37f908a7ec8b4ebcec9253588d1a6d909aafe1ccfa0c36eae34dc122, 0x417c74c828359db7f26202d579296965a8699208ab9685b08921f60a7b032fc96e344abf151fc4a313fcd3972a562cc3b407f14caa9d36f16611c53a34728, 0xcddc83deca84d0d7ed831b5ef51af7262f7a8d16f34fb2a97af3d575fcb0929d15fe00e42c83102872d831dc5384933535987cd5dab4a638ee7e491e268,
  0x1fcf97bc021685917a8594164a282b2606315c6db6f74cb13a134089d9fc3f41871d27309c4280bd98b76488c632e4a7f1bd46164849b2c1b81943e628, 0x3cd109928bf4635d046645fdf2c1d72679dab8c5d4dc93824cab6d3a21f5c4add4fdc54766283c68b0a622206326e11e55f55353472e71e1a82cf832, 0x5828c692bc6c4e57d9a0cbadcba8ac61b1d3034293ceafe90e86721dfca6c5c5f4f1a9561a379a0c5ffa42c481d7e09ea36513f369ca2b9dfd645c,
  0x5eb54e336e4b566259ecfd907617d32d7c13c8d97399abf477e063a5b0855054e724fc3a94dec600aea835794f198524e7c2f0afbe6e1b92e9b4, 0x4967d7d848c0a0af6a6b97e21094a645ded483591fed7c98815e37e099d786d10b933fe11c0ec0657361fbf094726af1c34b4bb919dd157b4c, 0x27c3d5f5c7e7d2ff71b41f70abbf5e2338ff384fe6a29d18af8206e3ffdd5d7f080a893a78844637f24d2269a2cbaf11e90850c2feee8dbe,
  0xe7ebf1a582eeca6cae0c04533a11d93780018b957c0509552995dab52d6568b2954030a3b9f9d469db38133417787aff4eb45c3587d10, 0x3656e130865b75a599e06d5d971c28603c274d22a5173ef0bd60e10806f41372761aee38fb5515539344f3ae788b670e242d96f0d50, 0x7bd0379256dcba1392a87dd632464558ceeab2e5fdb72f07cccc1f37e8dd228bb3ef1cdf67fbf413315dcb9d639457972e079690,
  0xa002610fcb77bf9d1c1e38f6c86fa95df02350d19dce6565dc7e3ca9333d832c2f0270b29e78a843873da19b98355baa1cc9d, 0x6b8bddebb2078f31e0e8523f12c978970b6f1f48af9142a4baebf5100216337724ae18bd034968992b43bb7830c7295dfa, 0x21aa1e073ea3e5fb366f1dcf3ec55ba3eaa48b2a8e534c56ad6699fe2d527579808164d1916c3be6356b5a15c683636,
  0x440cdd511cee29135d1e28a436c15fd14e28b01df550dbf1dafb8228111f765f986573a3c68a2ddff75c852cd52, 0x2dee64fdbbee03a5d4074cdf5cbcf4de260404c0ed2e3ee7d3988ea3ceaaf35407529fcac517d287fe56e8b, 0x7ffe477c8eaeef76dcefeacc72824a652f121c7afcbebd495ae31bcd998ef4f1781ec470a90134aaf4,
  0x401312b0a637b8bc620d4e447b7c0ced4db8b15f74ee9c38a63b681bad428a3ccfae401ef3474, 0x3639d98e9628e288a86c8fa0f648c23669eda1af971a57ed005ccb47fd69da5a3d1b634, 0x22104d3dec21962c8ebd2fcada45161f8f2c388a7c5cb0ac44f341e2e6189d47,
  0x3fffffffff45992100d691ef94254bc968ccccaf37cb53ac51ead4a, 0x1b1ced3c631df90d67aa80f569315ae09c9b649bb5be, 0x1fffffffffffffffffffffffff92,
  0x1]

private theorem eulerianCoefficients_eq : descentCoeffs 109 = eulerianCoefficients := by
  decide +kernel

private theorem upper : upperOK (descentCoeffs 109) first gaps = true := by
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

private theorem lower (i : Fin (lastRepresentative 110 - 2)) :
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

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 110) :
    StrictNegativeInterlacing (originalQuotient 110 k) (eulerian 109) 107 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N110
