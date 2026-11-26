import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentPackedData.C127L112.N105

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N105

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L112.N105 LongCycleBounds.DescentNecklace.Packed.C127L112.N105.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L112.N105 LongCycleBounds.DescentNecklace.Packed.C127L112.N105.rows

private theorem actual : RepresentativeChecks 105 previousNodes rows :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L112.N105 LongCycleBounds.DescentNecklace.Packed.C127L112.N105.dataChecks

private def first : LongCycleFinite.Dyadic := ⟨-20282409603651670423947251286016, 0⟩

private def gaps : List Window := [
  ⟨⟨-20281751948005800065676211126272, 0⟩, ⟨-2550101716347387904, 0⟩⟩,
  ⟨⟨-1973645362090475520, 0⟩, ⟨-9852688531456, 0⟩⟩,
  ⟨⟨-9769372876800, 0⟩, ⟨-12210438144, 0⟩⟩,
  ⟨⟨-11762106368, 0⟩, ⟨-164623360, 0⟩⟩,
  ⟨⟨-164049920, 0⟩, ⟨-8450912, 0⟩⟩,
  ⟨⟨-8442944, 0⟩, ⟨-950326, 0⟩⟩,
  ⟨⟨-949934, 0⟩, ⟨-177293, 0⟩⟩,
  ⟨⟨-354503, 1⟩, ⟨-187167, 2⟩⟩,
  ⟨⟨-374277, 3⟩, ⟨-506171, 5⟩⟩,
  ⟨⟨-126529, 3⟩, ⟨-205461, 5⟩⟩,
  ⟨⟨-51361, 3⟩, ⟨-383345, 7⟩⟩,
  ⟨⟨-383319, 7⟩, ⟨-99613, 6⟩⟩,
  ⟨⟨-398431, 8⟩, ⟨-112795, 7⟩⟩,
  ⟨⟨-451159, 9⟩, ⟨-273697, 9⟩⟩,
  ⟨⟨-136843, 8⟩, ⟨-87839, 8⟩⟩,
  ⟨⟨-21959, 6⟩, ⟨-472617, 11⟩⟩,
  ⟨⟨-472603, 11⟩, ⟨-82633, 9⟩⟩,
  ⟨⟨-330523, 11⟩, ⟨-238935, 11⟩⟩,
  ⟨⟨-477859, 12⟩, ⟨-355301, 12⟩⟩,
  ⟨⟨-355293, 12⟩, ⟨-270629, 12⟩⟩,
  ⟨⟨-270623, 12⟩, ⟨-52623, 10⟩⟩,
  ⟨⟨-26311, 9⟩, ⟨-333445, 13⟩⟩,
  ⟨⟨-333439, 13⟩, ⟨-268343, 13⟩⟩,
  ⟨⟨-134169, 12⟩, ⟨-437975, 14⟩⟩,
  ⟨⟨-27373, 10⟩, ⟨-361859, 14⟩⟩,
  ⟨⟨-180927, 13⟩, ⟨-75565, 12⟩⟩,
  ⟨⟨-302255, 14⟩, ⟨-254943, 14⟩⟩,
  ⟨⟨-509879, 15⟩, ⟨-54227, 12⟩⟩,
  ⟨⟨-216905, 14⟩, ⟨-371969, 15⟩⟩,
  ⟨⟨-92991, 13⟩, ⟨-321167, 15⟩⟩,
  ⟨⟨-321163, 15⟩, ⟨-279041, 15⟩⟩,
  ⟨⟨-139519, 14⟩, ⟨-487617, 16⟩⟩,
  ⟨⟨-121903, 14⟩, ⟨-428211, 16⟩⟩,
  ⟨⟨-428207, 16⟩, ⟨-94441, 14⟩⟩,
  ⟨⟨-11805, 11⟩, ⟨-334635, 16⟩⟩,
  ⟨⟨-41829, 13⟩, ⟨-297529, 16⟩⟩,
  ⟨⟨-148763, 15⟩, ⟨-16589, 12⟩⟩,
  ⟨⟨-265421, 16⟩, ⟨-474991, 17⟩⟩,
  ⟨⟨-474987, 17⟩, ⟨-426159, 17⟩⟩,
  ⟨⟨-426155, 17⟩, ⟨-95817, 15⟩⟩,
  ⟨⟨-11977, 12⟩, ⟨-86359, 15⟩⟩,
  ⟨⟨-43179, 14⟩, ⟨-311929, 17⟩⟩,
  ⟨⟨-155963, 16⟩, ⟨-282145, 17⟩⟩,
  ⟨⟨-282143, 17⟩, ⟨-511151, 18⟩⟩,
  ⟨⟨-511147, 18⟩, ⟨-463595, 18⟩⟩,
  ⟨⟨-463591, 18⟩, ⟨-420909, 18⟩⟩,
  ⟨⟨-420905, 18⟩, ⟨-382485, 18⟩⟩,
  ⟨⟨-191241, 17⟩, ⟨-173903, 17⟩⟩,
  ⟨⟨-347803, 18⟩, ⟨-316433, 18⟩⟩,
  ⟨⟨-316431, 18⟩, ⟨-287989, 18⟩⟩,
  ⟨⟨-143993, 17⟩, ⟨-262145, 18⟩⟩,
  ⟨⟨-524285, 19⟩, ⟨-477241, 19⟩⟩,
  ⟨⟨-477237, 19⟩, ⟨-108585, 17⟩⟩,
  ⟨⟨-434337, 19⟩, ⟨-395163, 19⟩⟩,
  ⟨⟨-395159, 19⟩, ⟨-359335, 19⟩⟩,
  ⟨⟨-89833, 17⟩, ⟨-326531, 19⟩⟩,
  ⟨⟨-2551, 12⟩, ⟨-296465, 19⟩⟩,
  ⟨⟨-148231, 18⟩, ⟨-268883, 19⟩⟩,
  ⟨⟨-268881, 19⟩, ⟨-60891, 17⟩⟩,
  ⟨⟨-121781, 18⟩, ⟨-220307, 19⟩⟩,
  ⟨⟨-220305, 19⟩, ⟨-397875, 20⟩⟩,
  ⟨⟨-397871, 20⟩, ⟨-44825, 17⟩⟩,
  ⟨⟨-358597, 20⟩, ⟨-161255, 19⟩⟩,
  ⟨⟨-322507, 20⟩, ⟨-36169, 17⟩⟩,
  ⟨⟨-289349, 20⟩, ⟨-129453, 19⟩⟩,
  ⟨⟨-517807, 21⟩, ⟨-28871, 17⟩⟩,
  ⟨⟨-461931, 21⟩, ⟨-205359, 20⟩⟩,
  ⟨⟨-205357, 20⟩, ⟨-363825, 21⟩⟩,
  ⟨⟨-181911, 20⟩, ⟨-320965, 21⟩⟩,
  ⟨⟨-320961, 21⟩, ⟨-281863, 21⟩⟩,
  ⟨⟨-281859, 21⟩, ⟨-492547, 22⟩⟩,
  ⟨⟨-246271, 21⟩, ⟨-427943, 22⟩⟩,
  ⟨⟨-427939, 22⟩, ⟨-369497, 22⟩⟩,
  ⟨⟨-92373, 20⟩, ⟨-79205, 20⟩⟩,
  ⟨⟨-19801, 18⟩, ⟨-269553, 22⟩⟩,
  ⟨⟨-134775, 21⟩, ⟨-454711, 23⟩⟩,
  ⟨⟨-454705, 23⟩, ⟨-379819, 23⟩⟩,
  ⟨⟨-379813, 23⟩, ⟨-313809, 23⟩⟩,
  ⟨⟨-78451, 21⟩, ⟨-256095, 23⟩⟩,
  ⟨⟨-512183, 24⟩, ⟨-412183, 24⟩⟩,
  ⟨⟨-25761, 20⟩, ⟨-326473, 24⟩⟩,
  ⟨⟨-81617, 22⟩, ⟨-31741, 21⟩⟩,
  ⟨⟨-507847, 25⟩, ⟨-193419, 24⟩⟩,
  ⟨⟨-386831, 25⟩, ⟨-143807, 24⟩⟩,
  ⟨⟨-35951, 22⟩, ⟨-207907, 25⟩⟩,
  ⟨⟨-415805, 26⟩, ⟨-71, 14⟩⟩,
  ⟨⟨-290809, 26⟩, ⟨-391179, 27⟩⟩,
  ⟨⟨-391169, 27⟩, ⟨-502171, 28⟩⟩,
  ⟨⟨-502157, 28⟩, ⟨-304637, 28⟩⟩,
  ⟨⟨-76157, 26⟩, ⟨-172477, 28⟩⟩,
  ⟨⟨-172471, 28⟩, ⟨-179271, 29⟩⟩,
  ⟨⟨-2801, 23⟩, ⟨-167245, 30⟩⟩,
  ⟨⟨-83619, 29⟩, ⟨-135777, 31⟩⟩,
  ⟨⟨-271541, 32⟩, ⟨-91803, 32⟩⟩,
  ⟨⟨-45899, 31⟩, ⟨-96913, 34⟩⟩,
  ⟨⟨-387629, 36⟩, ⟨-289353, 38⟩⟩,
  ⟨⟨-144667, 37⟩, ⟨-520483, 42⟩⟩,
  ⟨⟨-520447, 42⟩, ⟨-213929, 45⟩⟩,
  ⟨⟨-213913, 45⟩, ⟨-5951, 46⟩⟩,
  ⟨⟨-190417, 51⟩, ⟨-468591, 62⟩⟩,
  ⟨⟨-58569, 59⟩, ⟨-293709, 79⟩⟩,
  ⟨⟨-146841, 78⟩, ⟨-262165, 122⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private def eulerianCoefficients : List ℤ := [
  0x1, 0xffffffffffffffffffffffff97, 0x1c9040830aa8879a52dfdf4c48e4fba82690be5a75,
  0xfffffffff448d58a40a0e04bf7022d69b61a14c8082ea1f2c933, 0x2ca5dfb2303143f9fc4ec523290054b68b84876741d599331b10943fe08fb, 0x1c903f5e0a1c70ea0f91c76cae7e146b647c31fbe8b0e24f5fe2fea8f07e6995e56d,
  0xf9d89438d2b13d22dd7ef16b0114b077417a51285dc10ad91a2cc52c1d50f6990baad987f, 0xfff99860465f5f620d4a22b7f1eb79ec95bbdd20ca1dc21f59f8be61a58794f1cf28b9eb985259, 0x32f76669b0f3f812c4d1accd996211bfd9a370ed04f3fa3ce1921a89b79bd0317b037a50d3b3558872c,
  0x2c90f6e3f496a76bdd2d4334b2fde4b499684fad3ce4b6c457a6618e719f0a6ec103aa29e5695cac45695f4, 0xdac8dd61b2bbe4c383e21afc1e213cd0dee0fca04400fa6e4e7a4550ad5666415a82554d9e4479da115080e8dc, 0x1c364789e316abec1339f99f14e28e9587c4601f667c7cc8cc33f46a9aeb80021dac1ee726b3ae757c83ca0d78d904,
  0x1c06ec4f5e99a5493ef53e448581ed047f1461e569af19f890f5983d614af1c79de8be2c0ba183f6d44ffda7f3d38b074, 0xee33fac7ad1b344ab2b5c413fac6c147e782bfe88e0271143010eec7f13bad83fc6e3832f4e310fc44ec02c9118190ec3ec, 0x49733168a51e0490e28a8e9aa0b24cc68c3606e4d05066bced0a75b97982f15cd6d655d7593835a979d15aaf9cefd639c78b24,
  0xe096c78fbe4b0d881cb926e09f20f7b0fb87625f3fa7fa50a785c4975ddb3b49a7100621b211442cae7d87f288d08a36c492137c, 0x1c0bf86527693a16f7115625e5010f4c46844290c3b626bab4d128a8d5c468a8a23c4e55d9d632f5c6659edd5f514493cc368b386aa, 0x263db67bd17b42a2bf486ad255ff3e66823891f4455b09efbf084cb9ea401376cc3384a52edcd5b97f55447c76a755e7d73c80ac59546,
  0x24e14c84ff9424bb551aeaa0cc1864944765cda83e7075b739aea61f018c535aa1c35325a398ddc3774019b2204b23d4332e21349b688f2, 0x19ec9dfc14f66d33f9d07c85c714e80462c3ffd4db365348180c124ca47a65240f2198cbb0a90e0a1533e8413202de4d67313ea34af615b9e, 0xd9fa070e5d4f6b5b52049738f45312ad46fba42ab98bb4505dd396c65c7a382b84dc392f08a3ebc3513f94769280a2b5a09b95750d65e567fe,
  0x5782051cb0b9109282404466dac3d38fd6a28fdc390a01b220b763c31aca57e429a481b2a5bc22cc07f2562a3f3dba0685d6e3abd3f45af66592, 0x1b5709e7fcc306ee9717bcb040695c5ea043036ca76c5418b715f3697eb348981a26a776c449ccf710a7c385c01a54c98d03a1d7b36b05b006ab26, 0x6c150b486055ba9b56e32aa40c73e5b5c26376c52fce893449385eebaa681d997dd8c85fb0ab0865c38819623335141b228a86dfcf52edab0a74fca,
  0x156a889e86a29df43cd28f9a8d99e7a59b3ea552814c5cf784ace057be74ddef3c6a195444c51182b14efd9432a83bdf3e9535cbe631430d504a4ee4c, 0x371ec2b18814435f2cf77cd3fd6e7c30e7924d0de6bf1271bafefb3927f14903aa81938c448ba30ddb8badd67119fefc52a585dfc02d424b8bcf2b3fd4, 0x746a99d84249514450408e09f6e3bf6e4af2c9341e7de76beeea924f973f3ac9c823bdc5675339a23e73236ddaefe9707c6a94d6a0a4dc27f3c880a81fc,
  0xcbb23916b08425a8629d541c5cdfc6e4a69b9365728cbe93decfdea80da1766a4654639550366cda9c9e2925472a57b654efb059c58f9da1a292eeb146e4, 0x129c560f0dc730d3e93f75bbba16d0adbecd44fdd73de680da8a7aa0258f0672d7c647893c910c37a18425a337946c4b32038c453f7e6002e499f2f9c15cb4, 0x16e6b50997695ec157bed3cbc53b30d5a8636241c1de8787f634865a7ad8d73280cbeba647289183ddf37d28fc61b65fb879c2bdf2ad0ff901a7880c3eef7ac,
  0x17e1c1eb8d69aa5a472ef86a200ee2b14e4a9dd0bbcb23ac82e023f49a19c2fe2c7c4407e8f03f30106e52a174e4e00db246de1b7834e4aca60b76ab84fe2ce4, 0x153b9774bac4a828f8bcea2470cf534ebea96407ff09d555dbfaacf71402a64905424ce09a5f0e9b4c1a2f5c0593b497b9cb4397bc2664d07ef9575856e84b1bc, 0x102e7e3bdbb547fe270d7a596f934d9441ea04597685c9c3f5cb926eb56796989265d802f96f21c0c25bd556b79fcee9baf01829f83c64430f53a0aa070dc15227,
  0xa9f59d43b4e8f617477be18db3256d588436c7ef3eda03c9befe843a9a708cf5cab9d2929dfbb7eee849c8bc245393bfee2a4bbe83ec87eb498824331892a41901, 0x6086685a9e65eeb634fba15410f2c89ba5e34c71e0807aa4b378afb304e06ea31cf005b822f106c2305c88650d3873076d3c22ef179278713ebfd4a54e3da0b1193, 0x2f9d6016690055a9e294b7bb7edbd202ef9fe2ac75e27d89b66add1004b3bbb171fd5b6d0b4690bd2fcdb0b4027e97e4539f450d8b5ef5acd845587481bdb3f19a05,
  0x147947e7a2bc01d1681e083663e543698d27f7b49d128f554c249a2c2caaee1ca7bdb10071f2c15ba86f66281a5044ceda223d78b5e962518b92038628100b3ba39ed, 0x7b2ce1576decde78a94266381f728af709ea7beade7d6790178570a5a0f5b76d64a9b0709ffce5de6f4d748e41e1bd17ebb6a8680e47fd8e96dd3024e03ec0ef57f6b, 0x289ead6b6727b50d84530aec2385b409fbfb41fcff6f72570b32e702d554713127886dec545ac46547c2402dc689a3ad731e4df7f58858df5faf0baa61709ff5d67a89,
  0xbc7514538fed335016fe196ce0a6c6e7214b65894009cc7c918c6a6feaa44c415fc30861e53224460d264706592b03f6dbdafaf0f02e8c14487b4dd7e13db2ff9230df, 0x302a0ff247a99497f10334aa6b1a9d5203a27b0a705e2c51d98d6e65c723e91baef44a19fc82a861c17f781c6b7c1036b5494ffa7a9e3e0a9dd96fb22e2d0d6956d8a98, 0xadf348121c3f0bfb00a968b4a796cd03e52306febbac8612f00fd4d5d28cdd2c84b9866e1dcfe04662fa3cda3477e48419a05abaa7404ad9e97a4c1eab035d739653da8,
  0x22be8f6e1860f550d70b9619903c2adf9cc30b9160bba91842df5cc8e4ced63d150a1ce22251c529e4db75dbda8dffde7191dcd57c9183d5352b6b2b8c4c7ff6731e74f8, 0x626a525d92f7f1323ee44b23b4f97ccbdeaa693495bd1280c46bdf30957921e0d80e6224833bf5fccacffc1cc17f97c905e8269fd55b4c05a7f16529a2bc5b36418e90c8, 0xf77117903c07c9701569254077bfff1e1020028c2c36836ce64f4d458316b7a9a79a1a5b091073190d3907e7de778f63ec8aedd5e6b09c962e05ae0c733483d8957a2a28,
  0x228ed17b8ac6d589ef60725f08380b4946dc913b29e086d4dcf69215ab16ae25d8c31cfced2aac964c97436c913b0fc0931798dfb7530449dadc4af1f815637ffd10a3c98, 0x44b4edfbef231b07bf3f14ed02fc25576c654eb6b2dcd3d4bb992c556374b47d516209ca552e90fd43a2d9605f09b460011faff0dc1d32ad7192e1551a51ad965cdfcfc88, 0x79a647f1d63829ebda010dd2e5375ee76d87ed11a760cee29e86a502c9265592ea8398e382f280f9718d306a11777d768fa9292bc8e73fb64115f0a6370b0a398ebebb2b8,
  0xbff5a51ee7523bb222cf24b4d20d029ab99f11b2eb9dd7583801ae797f1ba1de9aa439de723c337425ebc49cdf91228b79f9eb3bdd404a15f74707b83d6ecfea3be4bdc2c, 0x10e1ef3922d054b61f7e38a7e0438474ae429cb23744e2c146fca06e65813fa8bed50bcc58705008ddffb0bf6f5db41aba5c406bc34c844780c67380a3b94e10bda161cbf4, 0x1531e0a63bc30e74801bc3ef8e48e41b0ec8682b8756c77f1ddee208374d3744a957874ec55fa30c007c7a9662b0f7b6f667a104ff088b0979da9d1185e079e9bc854c689c,
  0x17bf060a9446ba486e4e25d5bc5ea8ee4f9d09f391c00747dca43b428e03f6683992d0765f9a3bac7314ce9dbb9b32be7f61a429fc4262b3c8e4d146b718873df7d3efae44, 0x17bf060a9446ba486e4e25d5bc5ea8ee4f9d09f391c00747dca43b428e03f6683992d0765f9a3bac7314ce9dbb9b32be7f61a429fc4262b3c8e4d146b718873df7d3efae44, 0x1531e0a63bc30e74801bc3ef8e48e41b0ec8682b8756c77f1ddee208374d3744a957874ec55fa30c007c7a9662b0f7b6f667a104ff088b0979da9d1185e079e9bc854c689c,
  0x10e1ef3922d054b61f7e38a7e0438474ae429cb23744e2c146fca06e65813fa8bed50bcc58705008ddffb0bf6f5db41aba5c406bc34c844780c67380a3b94e10bda161cbf4, 0xbff5a51ee7523bb222cf24b4d20d029ab99f11b2eb9dd7583801ae797f1ba1de9aa439de723c337425ebc49cdf91228b79f9eb3bdd404a15f74707b83d6ecfea3be4bdc2c, 0x79a647f1d63829ebda010dd2e5375ee76d87ed11a760cee29e86a502c9265592ea8398e382f280f9718d306a11777d768fa9292bc8e73fb64115f0a6370b0a398ebebb2b8,
  0x44b4edfbef231b07bf3f14ed02fc25576c654eb6b2dcd3d4bb992c556374b47d516209ca552e90fd43a2d9605f09b460011faff0dc1d32ad7192e1551a51ad965cdfcfc88, 0x228ed17b8ac6d589ef60725f08380b4946dc913b29e086d4dcf69215ab16ae25d8c31cfced2aac964c97436c913b0fc0931798dfb7530449dadc4af1f815637ffd10a3c98, 0xf77117903c07c9701569254077bfff1e1020028c2c36836ce64f4d458316b7a9a79a1a5b091073190d3907e7de778f63ec8aedd5e6b09c962e05ae0c733483d8957a2a28,
  0x626a525d92f7f1323ee44b23b4f97ccbdeaa693495bd1280c46bdf30957921e0d80e6224833bf5fccacffc1cc17f97c905e8269fd55b4c05a7f16529a2bc5b36418e90c8, 0x22be8f6e1860f550d70b9619903c2adf9cc30b9160bba91842df5cc8e4ced63d150a1ce22251c529e4db75dbda8dffde7191dcd57c9183d5352b6b2b8c4c7ff6731e74f8, 0xadf348121c3f0bfb00a968b4a796cd03e52306febbac8612f00fd4d5d28cdd2c84b9866e1dcfe04662fa3cda3477e48419a05abaa7404ad9e97a4c1eab035d739653da8,
  0x302a0ff247a99497f10334aa6b1a9d5203a27b0a705e2c51d98d6e65c723e91baef44a19fc82a861c17f781c6b7c1036b5494ffa7a9e3e0a9dd96fb22e2d0d6956d8a98, 0xbc7514538fed335016fe196ce0a6c6e7214b65894009cc7c918c6a6feaa44c415fc30861e53224460d264706592b03f6dbdafaf0f02e8c14487b4dd7e13db2ff9230df, 0x289ead6b6727b50d84530aec2385b409fbfb41fcff6f72570b32e702d554713127886dec545ac46547c2402dc689a3ad731e4df7f58858df5faf0baa61709ff5d67a89,
  0x7b2ce1576decde78a94266381f728af709ea7beade7d6790178570a5a0f5b76d64a9b0709ffce5de6f4d748e41e1bd17ebb6a8680e47fd8e96dd3024e03ec0ef57f6b, 0x147947e7a2bc01d1681e083663e543698d27f7b49d128f554c249a2c2caaee1ca7bdb10071f2c15ba86f66281a5044ceda223d78b5e962518b92038628100b3ba39ed, 0x2f9d6016690055a9e294b7bb7edbd202ef9fe2ac75e27d89b66add1004b3bbb171fd5b6d0b4690bd2fcdb0b4027e97e4539f450d8b5ef5acd845587481bdb3f19a05,
  0x6086685a9e65eeb634fba15410f2c89ba5e34c71e0807aa4b378afb304e06ea31cf005b822f106c2305c88650d3873076d3c22ef179278713ebfd4a54e3da0b1193, 0xa9f59d43b4e8f617477be18db3256d588436c7ef3eda03c9befe843a9a708cf5cab9d2929dfbb7eee849c8bc245393bfee2a4bbe83ec87eb498824331892a41901, 0x102e7e3bdbb547fe270d7a596f934d9441ea04597685c9c3f5cb926eb56796989265d802f96f21c0c25bd556b79fcee9baf01829f83c64430f53a0aa070dc15227,
  0x153b9774bac4a828f8bcea2470cf534ebea96407ff09d555dbfaacf71402a64905424ce09a5f0e9b4c1a2f5c0593b497b9cb4397bc2664d07ef9575856e84b1bc, 0x17e1c1eb8d69aa5a472ef86a200ee2b14e4a9dd0bbcb23ac82e023f49a19c2fe2c7c4407e8f03f30106e52a174e4e00db246de1b7834e4aca60b76ab84fe2ce4, 0x16e6b50997695ec157bed3cbc53b30d5a8636241c1de8787f634865a7ad8d73280cbeba647289183ddf37d28fc61b65fb879c2bdf2ad0ff901a7880c3eef7ac,
  0x129c560f0dc730d3e93f75bbba16d0adbecd44fdd73de680da8a7aa0258f0672d7c647893c910c37a18425a337946c4b32038c453f7e6002e499f2f9c15cb4, 0xcbb23916b08425a8629d541c5cdfc6e4a69b9365728cbe93decfdea80da1766a4654639550366cda9c9e2925472a57b654efb059c58f9da1a292eeb146e4, 0x746a99d84249514450408e09f6e3bf6e4af2c9341e7de76beeea924f973f3ac9c823bdc5675339a23e73236ddaefe9707c6a94d6a0a4dc27f3c880a81fc,
  0x371ec2b18814435f2cf77cd3fd6e7c30e7924d0de6bf1271bafefb3927f14903aa81938c448ba30ddb8badd67119fefc52a585dfc02d424b8bcf2b3fd4, 0x156a889e86a29df43cd28f9a8d99e7a59b3ea552814c5cf784ace057be74ddef3c6a195444c51182b14efd9432a83bdf3e9535cbe631430d504a4ee4c, 0x6c150b486055ba9b56e32aa40c73e5b5c26376c52fce893449385eebaa681d997dd8c85fb0ab0865c38819623335141b228a86dfcf52edab0a74fca,
  0x1b5709e7fcc306ee9717bcb040695c5ea043036ca76c5418b715f3697eb348981a26a776c449ccf710a7c385c01a54c98d03a1d7b36b05b006ab26, 0x5782051cb0b9109282404466dac3d38fd6a28fdc390a01b220b763c31aca57e429a481b2a5bc22cc07f2562a3f3dba0685d6e3abd3f45af66592, 0xd9fa070e5d4f6b5b52049738f45312ad46fba42ab98bb4505dd396c65c7a382b84dc392f08a3ebc3513f94769280a2b5a09b95750d65e567fe,
  0x19ec9dfc14f66d33f9d07c85c714e80462c3ffd4db365348180c124ca47a65240f2198cbb0a90e0a1533e8413202de4d67313ea34af615b9e, 0x24e14c84ff9424bb551aeaa0cc1864944765cda83e7075b739aea61f018c535aa1c35325a398ddc3774019b2204b23d4332e21349b688f2, 0x263db67bd17b42a2bf486ad255ff3e66823891f4455b09efbf084cb9ea401376cc3384a52edcd5b97f55447c76a755e7d73c80ac59546,
  0x1c0bf86527693a16f7115625e5010f4c46844290c3b626bab4d128a8d5c468a8a23c4e55d9d632f5c6659edd5f514493cc368b386aa, 0xe096c78fbe4b0d881cb926e09f20f7b0fb87625f3fa7fa50a785c4975ddb3b49a7100621b211442cae7d87f288d08a36c492137c, 0x49733168a51e0490e28a8e9aa0b24cc68c3606e4d05066bced0a75b97982f15cd6d655d7593835a979d15aaf9cefd639c78b24,
  0xee33fac7ad1b344ab2b5c413fac6c147e782bfe88e0271143010eec7f13bad83fc6e3832f4e310fc44ec02c9118190ec3ec, 0x1c06ec4f5e99a5493ef53e448581ed047f1461e569af19f890f5983d614af1c79de8be2c0ba183f6d44ffda7f3d38b074, 0x1c364789e316abec1339f99f14e28e9587c4601f667c7cc8cc33f46a9aeb80021dac1ee726b3ae757c83ca0d78d904,
  0xdac8dd61b2bbe4c383e21afc1e213cd0dee0fca04400fa6e4e7a4550ad5666415a82554d9e4479da115080e8dc, 0x2c90f6e3f496a76bdd2d4334b2fde4b499684fad3ce4b6c457a6618e719f0a6ec103aa29e5695cac45695f4, 0x32f76669b0f3f812c4d1accd996211bfd9a370ed04f3fa3ce1921a89b79bd0317b037a50d3b3558872c,
  0xfff99860465f5f620d4a22b7f1eb79ec95bbdd20ca1dc21f59f8be61a58794f1cf28b9eb985259, 0xf9d89438d2b13d22dd7ef16b0114b077417a51285dc10ad91a2cc52c1d50f6990baad987f, 0x1c903f5e0a1c70ea0f91c76cae7e146b647c31fbe8b0e24f5fe2fea8f07e6995e56d,
  0x2ca5dfb2303143f9fc4ec523290054b68b84876741d599331b10943fe08fb, 0xfffffffff448d58a40a0e04bf7022d69b61a14c8082ea1f2c933, 0x1c9040830aa8879a52dfdf4c48e4fba82690be5a75,
  0xffffffffffffffffffffffff97, 0x1]

private theorem eulerianCoefficients_eq : descentCoeffs 104 = eulerianCoefficients := by
  decide +kernel

private theorem upper : upperOK (descentCoeffs 104) first gaps = true := by
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

private theorem lower (i : Fin (lastRepresentative 105 - 2)) :
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

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 105) :
    StrictNegativeInterlacing (originalQuotient 105 k) (eulerian 104) 102 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N105
