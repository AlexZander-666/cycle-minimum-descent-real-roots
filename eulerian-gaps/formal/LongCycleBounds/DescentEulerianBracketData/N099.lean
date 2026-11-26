import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentPackedData.C127L104.N099

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N099

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L104.N099 LongCycleBounds.DescentNecklace.Packed.C127L104.N099.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L104.N099 LongCycleBounds.DescentNecklace.Packed.C127L104.N099.rows

private theorem actual : RepresentativeChecks 99 previousNodes rows :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L104.N099 LongCycleBounds.DescentNecklace.Packed.C127L104.N099.dataChecks

private def first : LongCycleFinite.Dyadic := ⟨-316912650057057350374175801344, 0⟩

private def gaps : List Window := [
  ⟨⟨-316902374187590626026190798848, 0⟩, ⟨-185745996838338560, 0⟩⟩,
  ⟨⟨-176738797583597568, 0⟩, ⟨-1757333684224, 0⟩⟩,
  ⟨⟨-1750018818048, 0⟩, ⟨-3101335552, 0⟩⟩,
  ⟨⟨-3021447168, 0⟩, ⟨-54772992, 0⟩⟩,
  ⟨⟨-54625408, 0⟩, ⟨-3316432, 0⟩⟩,
  ⟨⟨-3313824, 0⟩, ⟨-420907, 0⟩⟩,
  ⟨⟨-420755, 0⟩, ⟨-344399, 2⟩⟩,
  ⟨⟨-344327, 2⟩, ⟨-390861, 4⟩⟩,
  ⟨⟨-390807, 4⟩, ⟨-280083, 5⟩⟩,
  ⟨⟨-140027, 4⟩, ⟨-476945, 7⟩⟩,
  ⟨⟨-119227, 5⟩, ⟨-28935, 4⟩⟩,
  ⟨⟨-115733, 6⟩, ⟨-15549, 4⟩⟩,
  ⟨⟨-497543, 9⟩, ⟨-289851, 9⟩⟩,
  ⟨⟨-144919, 8⟩, ⟨-360407, 10⟩⟩,
  ⟨⟨-180197, 9⟩, ⟨-472617, 11⟩⟩,
  ⟨⟨-236301, 10⟩, ⟨-10119, 6⟩⟩,
  ⟨⟨-161899, 10⟩, ⟨-460353, 12⟩⟩,
  ⟨⟨-460341, 12⟩, ⟨-168783, 11⟩⟩,
  ⟨⟨-168779, 11⟩, ⟨-508347, 13⟩⟩,
  ⟨⟨-31771, 9⟩, ⟨-195781, 12⟩⟩,
  ⟨⟨-195777, 12⟩, ⟨-76897, 11⟩⟩,
  ⟨⟨-307583, 13⟩, ⟨-491559, 14⟩⟩,
  ⟨⟨-491551, 14⟩, ⟨-398679, 14⟩⟩,
  ⟨⟨-398673, 14⟩, ⟨-40951, 11⟩⟩,
  ⟨⟨-327603, 14⟩, ⟨-68083, 12⟩⟩,
  ⟨⟨-272327, 14⟩, ⟨-457403, 15⟩⟩,
  ⟨⟨-457397, 15⟩, ⟨-48453, 12⟩⟩,
  ⟨⟨-387619, 15⟩, ⟨-165573, 14⟩⟩,
  ⟨⟨-165571, 14⟩, ⟨-142471, 14⟩⟩,
  ⟨⟨-142469, 14⟩, ⟨-123383, 14⟩⟩,
  ⟨⟨-493527, 16⟩, ⟨-429871, 16⟩⟩,
  ⟨⟨-429867, 16⟩, ⟨-376359, 16⟩⟩,
  ⟨⟨-376355, 16⟩, ⟨-331029, 16⟩⟩,
  ⟨⟨-331025, 16⟩, ⟨-146183, 15⟩⟩,
  ⟨⟨-292363, 16⟩, ⟨-259177, 16⟩⟩,
  ⟨⟨-518349, 17⟩, ⟨-115257, 15⟩⟩,
  ⟨⟨-14407, 12⟩, ⟨-411247, 17⟩⟩,
  ⟨⟨-411243, 17⟩, ⟨-91951, 15⟩⟩,
  ⟨⟨-367801, 17⟩, ⟨-82427, 15⟩⟩,
  ⟨⟨-329705, 17⟩, ⟨-148077, 16⟩⟩,
  ⟨⟨-296151, 17⟩, ⟨-66621, 15⟩⟩,
  ⟨⟨-266481, 17⟩, ⟨-240145, 17⟩⟩,
  ⟨⟨-240143, 17⟩, ⟨-54171, 15⟩⟩,
  ⟨⟨-108341, 16⟩, ⟨-195719, 17⟩⟩,
  ⟨⟨-195717, 17⟩, ⟨-176927, 17⟩⟩,
  ⟨⟨-353851, 18⟩, ⟨-320075, 18⟩⟩,
  ⟨⟨-40009, 15⟩, ⟨-72409, 16⟩⟩,
  ⟨⟨-289633, 18⟩, ⟨-262145, 18⟩⟩,
  ⟨⟨-524285, 19⟩, ⟨-14829, 14⟩⟩,
  ⟨⟨-118631, 17⟩, ⟨-214701, 18⟩⟩,
  ⟨⟨-214699, 18⟩, ⟨-194205, 18⟩⟩,
  ⟨⟨-194203, 18⟩, ⟨-351117, 19⟩⟩,
  ⟨⟨-175557, 18⟩, ⟨-39643, 16⟩⟩,
  ⟨⟨-317141, 19⟩, ⟨-17885, 15⟩⟩,
  ⟨⟨-286157, 19⟩, ⟨-515755, 20⟩⟩,
  ⟨⟨-515751, 20⟩, ⟨-464083, 20⟩⟩,
  ⟨⟨-464079, 20⟩, ⟨-416855, 20⟩⟩,
  ⟨⟨-416851, 20⟩, ⟨-186839, 19⟩⟩,
  ⟨⟨-186837, 19⟩, ⟨-334203, 20⟩⟩,
  ⟨⟨-334199, 20⟩, ⟨-149059, 19⟩⟩,
  ⟨⟨-298115, 20⟩, ⟨-66287, 18⟩⟩,
  ⟨⟨-265145, 20⟩, ⟨-470097, 21⟩⟩,
  ⟨⟨-117523, 19⟩, ⟨-415189, 21⟩⟩,
  ⟨⟨-415185, 21⟩, ⟨-2853, 14⟩⟩,
  ⟨⟨-91295, 19⟩, ⟨-79931, 19⟩⟩,
  ⟨⟨-39965, 18⟩, ⟨-278485, 21⟩⟩,
  ⟨⟨-139241, 20⟩, ⟨-482343, 22⟩⟩,
  ⟨⟨-241169, 21⟩, ⟨-103761, 20⟩⟩,
  ⟨⟨-415039, 22⟩, ⟨-354571, 22⟩⟩,
  ⟨⟨-354567, 22⟩, ⟨-4695, 16⟩⟩,
  ⟨⟨-75119, 20⟩, ⟨-126171, 21⟩⟩,
  ⟨⟨-252339, 22⟩, ⟨-209765, 22⟩⟩,
  ⟨⟨-419525, 23⟩, ⟨-43093, 20⟩⟩,
  ⟨⟨-172369, 22⟩, ⟨-279605, 23⟩⟩,
  ⟨⟨-17475, 19⟩, ⟨-223419, 23⟩⟩,
  ⟨⟨-446831, 24⟩, ⟨-351007, 24⟩⟩,
  ⟨⟨-351001, 24⟩, ⟨-270365, 24⟩⟩,
  ⟨⟨-33795, 21⟩, ⟨-25447, 21⟩⟩,
  ⟨⟨-50893, 22⟩, ⟨-4665, 19⟩⟩,
  ⟨⟨-298553, 25⟩, ⟨-424451, 26⟩⟩,
  ⟨⟨-424441, 26⟩, ⟨-290813, 26⟩⟩,
  ⟨⟨-145403, 25⟩, ⟨-190675, 26⟩⟩,
  ⟨⟨-95335, 25⟩, ⟨-237089, 27⟩⟩,
  ⟨⟨-118541, 26⟩, ⟨-138119, 27⟩⟩,
  ⟨⟨-69057, 26⟩, ⟨-37111, 26⟩⟩,
  ⟨⟨-296877, 29⟩, ⟨-288175, 30⟩⟩,
  ⟨⟨-288163, 30⟩, ⟨-245377, 31⟩⟩,
  ⟨⟨-122683, 30⟩, ⟨-351665, 33⟩⟩,
  ⟨⟨-351647, 33⟩, ⟨-199545, 34⟩⟩,
  ⟨⟨-399067, 35⟩, ⟨-326659, 37⟩⟩,
  ⟨⟨-163319, 36⟩, ⟨-331619, 40⟩⟩,
  ⟨⟨-82899, 38⟩, ⟨-160897, 43⟩⟩,
  ⟨⟨-160885, 43⟩, ⟨-91127, 48⟩⟩,
  ⟨⟨-364479, 50⟩, ⟨-329289, 59⟩⟩,
  ⟨⟨-329261, 59⟩, ⟨-26137, 72⟩⟩,
  ⟨⟨-52269, 73⟩, ⟨-262165, 116⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private def eulerianCoefficients : List ℤ := [
  0x1, 0x3ffffffffffffffffffffff9d, 0xa07d06bd2945f6126958d45fb65d50988cd6a7c,
  0xffffffffc1efa664d909ed016142a5defc79e9d501894c154, 0xbb445d46ca61282b0bab94f823a8ce487e6ce57bb1a6d4b844698143c, 0x281f3d28934f2850612ddc3f17642706bfd842386c40119ee269c07451c0e1d4,
  0x8b2c797bbf8c0091f8964cb31b683f5f65c82b71044cfa093f88e02c0fef6c444272c, 0x3ffca2d9c886287c04be9d8d9931e494b917b29b99ce4983bd4528e8c24683de1be7388dc4, 0x6483c620dd016855b87e150cd08a2e37f6fba7d3b601325031f1322adf269c47d96f79a0e50278,
  0x2eaa339f7ecf7be94bfe880c412e736d73046b85403509274fc1fe18ba44b8f71ce411a47f26a458a0, 0x810b5b35b427eabc8813d62f0ed5bd5b6d6d8428bb138919d24b207a6ff6d32c97a0ba63b9435d878fb2c, 0x9d5b092a21da4de5924ac7e102274d15c75309904d132568d96c1641427861308cff84eba0f14948b5cc72a4,
  0x601b095194778c01491e50f773c631c0c512a428b4891c4b07561b490855db3bb41a7f241c97442039feb29657c, 0x206cbdf9386c5983970e77e41d1507888432db1587bb7533fc5f384000a1651b8af2f5fba66576a13170399f947f74, 0x68666b8751ee8b94b445789c65cfe0b3eff240194f0d20170250d89e046eb4101b0633433c9f93f76a24ac2a79ef89dc,
  0xd51dff9bbbc8a11ddc8faeb0be4ab34958672742a77be4787049d3b8c150cce19c10bf98fdcca5267b69b33268b9bab194, 0x121c4209a658408cf8154e61719cb238afe0e2936348c8ab43b39bdb6f3ad1aaa296ac3e445cec2411e60f1118115a065bbf6, 0x111389b2fa9515104768b6202ee28d357efe56083a0687ffb168b61b862a8c0ad35dd3c615d53623076d9bf9e9b57977798ecc6,
  0xb8ba0e44249bd30714a08ce37f84e14c4e1b3ccf0a806df84a226e5884ac19d70feb94ed469672886e8fac5f2bac499c339e40e4, 0x5c186f189d5a165aa7cd1f3a099d71949eeb50dac396eff1bf7bbde1fe0d2eb47bb2dd8e849226a7699e3332275f07b7d317f87a4c, 0x22aa67e19c65603e9b1e043a391b5fd5f1774417f01c646b38b521ed1b536c2be48a931d9376b5df270e505790e2999b4a82c3e8a5c4,
  0xa0d5700c2b874022412f69d5b6f5ad7edc007c481db1a67498b7a9e7b93e6a23df021fb080e159f87e4120e3a1671ab6389d695d78dec, 0x248df5f09c990dec0c9d9d83d325da244e30dac34b8b2a18f173c649fb4ec409a566d15d2d717f4d27b409430490f366cd932d756081034, 0x69c2d7e8ceb74eb8eeaafe2f852cda98f8d329268c9d85ecd3a48873c0d4eb33a2ab789845284cd918878676bc2491e497536d25e0d5bedc,
  0xf6a3c29b9ace70d276dc3cd7a07ed6f2a40ede38aa8b351a49af9707ae360d511e30bb3c7d4e2d0d73a5723ec08213fa139ca122db290e880, 0x1d4eb30d82282cd6112279be2d57396aaca0b899aec5744755cc441eb703a02a1db0c192a9d41fb7ba9eb68032388e46cc3759be7c70424c838, 0x2de23ace64d01bfe57c7cde49f5b2bb56e110aa19819e086f07cc531f7ce82ea3f8bf120bd68c4f67a041da8e9af61540a96426b5e625b0b1e54,
  0x3badfe35e30b99f016aa5c6017dcfe78f855e643046289726ad8b55afa76180cfd7e8f74de5dc321ace54e34898e12a4bee34941d7ee7e01ef25c, 0x40feeed2f77e7e3d245b40ff5ca7c6b75dd0c54bcb30b005a58c3c1b828dc16ecfd3c64032f3611f2d10072c87106a1dc05a03a4e5bb238bc16e24, 0x3baf4de5436c41789a0cf8ac423a8a9b5ab3c912fc922cfc42ee720217a10154e0c5b7d11f64bc7a25ad3eed037fb85bd2e8a1cfacbfa5b4b8d812c,
  0x2e8033b97fe0f3efc1bc252a18b1a4f6fecc7ee0279f6c9d9d5a10e6a713715c9b4d53b8c7945d7c8e575ada53120bb86fe446a695290a499d96c424, 0x1ee8c29f46cf2d6d1d7f14a215bebf395153b1aef636ee09a3e05cca40777129677be9a7ba9c9235cf28932a75087ace8665499ff5a56abd68504d2ec, 0x119daea27de6a06bac2e897efa5249c629147e51b422cbc250d41f8adfb13975eb8d7a4aa283f8d659c9f1b32f26cfc47c8628421a3be322a079928f7b,
  0x8a58bf81aca5adc08d4eaafd43139ff4bd38af3d2dde7a3e0d6dbfc335802554978220b83a6af1c6253c337e0cd7d3e2496db63587af749104e58c7b07, 0x3ab7c89583ef1e8ed9d0b759eaacc5ef7ded4a855cd17465fc8bb1d73998cf7a63fbe4854ff11442d1d112055f546d3a984e38d04277c672e37d7c9a0d8, 0x15a060cf3f5babed114d0df8b5a7e12572e54e8b407697af09c6b456a90264d57bf3df2bf8307460a19cd099cd9c33b7e226201d72014682cbf860998348,
  0x6ef3223646ec3f943bc1f4f853e09ebc781d6ecea0f1494d8760b22bd20cbe1966751fe665c50fbe8b80738d1c15e1ab8c4669e6bc3dfa0fd3a414b373d8, 0x1f0f44a716d0c833a8c9206a046b51dd68d991b96caddc14e70e23670e85359fa35787d3fb906782b698924f632256984dbc8d33d7a634dd0e5da536d2bc8, 0x79c580da23f8acd94609717a53b1a2230fda240859c4e91f48412e923e488972dc367165a90965567eb446b66f22ae629b1d0722ffbc290aa260355f49db8,
  0x1a2d4e27d46952ec411568e6e2ac815ce02be8217ecede97bc8decf6165888bb18b099eb54b8b8971926f76332d92f11bf9dbc38b27efe310bcfac22f041a8, 0x4f255b58105e47b586549f68f38992d055c9747704dd0db2901d59457877ee4a4cb430ab63dff3b01555712ae5197062fdfa0cb481273b18d47758b1a29110, 0xd2b9b875ef43c99b36585bed187ed226bed94959309b377611f6cc28c6b704133346bf1d9d3253e508af13819b2270713148dcaaddb71a334ed66c7529ab20,
  0x1eed261558ab354894c3da3838eb9d0ad0d0cd460c1b80da906c4b590fb014c504fd90acc0e654e50189ccf2c584f267278b5251916e73234abea8b2de5a838, 0x4021bed7c096faeb646362a9a40775d8666fcec00194f7a46c5592ae54f8ed7a4a0b92da1dc0e0d36d0fcfeacd803e8f8dd16f862442e575a09a4a7c5a0b5e8, 0x7592eff60c3649550636a987f59d048d4d00e08619823f37d40ebddf7df0ed8adbd63fc9f7adbdbfbdd22c7de7b7bd4c98437b700481d3a34d15063947800d8,
  0xbebccd49c25a8ce7b0b4a9ec3e3b51f7b0f7eb9d474810c95db8665e2141e1cf6e7e348ea108d692f39164f2a93bf5e9df6080457a8298cdc394b1075c16188, 0x1120189ac85d3b4da6679b9316d710803dd7cedb0808cf70d096f4708ecc294df10a791985e76d82316aaddeecca6c3a7bb0c2bc6779b0a1f34f1aa756860318, 0x15cc024220b083103fd78116c508ac4a6051eac221ec5ce04e05e3e6ea285731607aa8a5f1bf94f99a875084741f62270b3ada06c1d3ed15ef93a5f115a2df48,
  0x1896af95845429c862488f3871ea4073a67e093efc29eb41d08ea452ec062e0aaf910d47df61b60be796799faa648ea61d85c2ad1c674b259b31395e1d570524, 0x1896af95845429c862488f3871ea4073a67e093efc29eb41d08ea452ec062e0aaf910d47df61b60be796799faa648ea61d85c2ad1c674b259b31395e1d570524, 0x15cc024220b083103fd78116c508ac4a6051eac221ec5ce04e05e3e6ea285731607aa8a5f1bf94f99a875084741f62270b3ada06c1d3ed15ef93a5f115a2df48,
  0x1120189ac85d3b4da6679b9316d710803dd7cedb0808cf70d096f4708ecc294df10a791985e76d82316aaddeecca6c3a7bb0c2bc6779b0a1f34f1aa756860318, 0xbebccd49c25a8ce7b0b4a9ec3e3b51f7b0f7eb9d474810c95db8665e2141e1cf6e7e348ea108d692f39164f2a93bf5e9df6080457a8298cdc394b1075c16188, 0x7592eff60c3649550636a987f59d048d4d00e08619823f37d40ebddf7df0ed8adbd63fc9f7adbdbfbdd22c7de7b7bd4c98437b700481d3a34d15063947800d8,
  0x4021bed7c096faeb646362a9a40775d8666fcec00194f7a46c5592ae54f8ed7a4a0b92da1dc0e0d36d0fcfeacd803e8f8dd16f862442e575a09a4a7c5a0b5e8, 0x1eed261558ab354894c3da3838eb9d0ad0d0cd460c1b80da906c4b590fb014c504fd90acc0e654e50189ccf2c584f267278b5251916e73234abea8b2de5a838, 0xd2b9b875ef43c99b36585bed187ed226bed94959309b377611f6cc28c6b704133346bf1d9d3253e508af13819b2270713148dcaaddb71a334ed66c7529ab20,
  0x4f255b58105e47b586549f68f38992d055c9747704dd0db2901d59457877ee4a4cb430ab63dff3b01555712ae5197062fdfa0cb481273b18d47758b1a29110, 0x1a2d4e27d46952ec411568e6e2ac815ce02be8217ecede97bc8decf6165888bb18b099eb54b8b8971926f76332d92f11bf9dbc38b27efe310bcfac22f041a8, 0x79c580da23f8acd94609717a53b1a2230fda240859c4e91f48412e923e488972dc367165a90965567eb446b66f22ae629b1d0722ffbc290aa260355f49db8,
  0x1f0f44a716d0c833a8c9206a046b51dd68d991b96caddc14e70e23670e85359fa35787d3fb906782b698924f632256984dbc8d33d7a634dd0e5da536d2bc8, 0x6ef3223646ec3f943bc1f4f853e09ebc781d6ecea0f1494d8760b22bd20cbe1966751fe665c50fbe8b80738d1c15e1ab8c4669e6bc3dfa0fd3a414b373d8, 0x15a060cf3f5babed114d0df8b5a7e12572e54e8b407697af09c6b456a90264d57bf3df2bf8307460a19cd099cd9c33b7e226201d72014682cbf860998348,
  0x3ab7c89583ef1e8ed9d0b759eaacc5ef7ded4a855cd17465fc8bb1d73998cf7a63fbe4854ff11442d1d112055f546d3a984e38d04277c672e37d7c9a0d8, 0x8a58bf81aca5adc08d4eaafd43139ff4bd38af3d2dde7a3e0d6dbfc335802554978220b83a6af1c6253c337e0cd7d3e2496db63587af749104e58c7b07, 0x119daea27de6a06bac2e897efa5249c629147e51b422cbc250d41f8adfb13975eb8d7a4aa283f8d659c9f1b32f26cfc47c8628421a3be322a079928f7b,
  0x1ee8c29f46cf2d6d1d7f14a215bebf395153b1aef636ee09a3e05cca40777129677be9a7ba9c9235cf28932a75087ace8665499ff5a56abd68504d2ec, 0x2e8033b97fe0f3efc1bc252a18b1a4f6fecc7ee0279f6c9d9d5a10e6a713715c9b4d53b8c7945d7c8e575ada53120bb86fe446a695290a499d96c424, 0x3baf4de5436c41789a0cf8ac423a8a9b5ab3c912fc922cfc42ee720217a10154e0c5b7d11f64bc7a25ad3eed037fb85bd2e8a1cfacbfa5b4b8d812c,
  0x40feeed2f77e7e3d245b40ff5ca7c6b75dd0c54bcb30b005a58c3c1b828dc16ecfd3c64032f3611f2d10072c87106a1dc05a03a4e5bb238bc16e24, 0x3badfe35e30b99f016aa5c6017dcfe78f855e643046289726ad8b55afa76180cfd7e8f74de5dc321ace54e34898e12a4bee34941d7ee7e01ef25c, 0x2de23ace64d01bfe57c7cde49f5b2bb56e110aa19819e086f07cc531f7ce82ea3f8bf120bd68c4f67a041da8e9af61540a96426b5e625b0b1e54,
  0x1d4eb30d82282cd6112279be2d57396aaca0b899aec5744755cc441eb703a02a1db0c192a9d41fb7ba9eb68032388e46cc3759be7c70424c838, 0xf6a3c29b9ace70d276dc3cd7a07ed6f2a40ede38aa8b351a49af9707ae360d511e30bb3c7d4e2d0d73a5723ec08213fa139ca122db290e880, 0x69c2d7e8ceb74eb8eeaafe2f852cda98f8d329268c9d85ecd3a48873c0d4eb33a2ab789845284cd918878676bc2491e497536d25e0d5bedc,
  0x248df5f09c990dec0c9d9d83d325da244e30dac34b8b2a18f173c649fb4ec409a566d15d2d717f4d27b409430490f366cd932d756081034, 0xa0d5700c2b874022412f69d5b6f5ad7edc007c481db1a67498b7a9e7b93e6a23df021fb080e159f87e4120e3a1671ab6389d695d78dec, 0x22aa67e19c65603e9b1e043a391b5fd5f1774417f01c646b38b521ed1b536c2be48a931d9376b5df270e505790e2999b4a82c3e8a5c4,
  0x5c186f189d5a165aa7cd1f3a099d71949eeb50dac396eff1bf7bbde1fe0d2eb47bb2dd8e849226a7699e3332275f07b7d317f87a4c, 0xb8ba0e44249bd30714a08ce37f84e14c4e1b3ccf0a806df84a226e5884ac19d70feb94ed469672886e8fac5f2bac499c339e40e4, 0x111389b2fa9515104768b6202ee28d357efe56083a0687ffb168b61b862a8c0ad35dd3c615d53623076d9bf9e9b57977798ecc6,
  0x121c4209a658408cf8154e61719cb238afe0e2936348c8ab43b39bdb6f3ad1aaa296ac3e445cec2411e60f1118115a065bbf6, 0xd51dff9bbbc8a11ddc8faeb0be4ab34958672742a77be4787049d3b8c150cce19c10bf98fdcca5267b69b33268b9bab194, 0x68666b8751ee8b94b445789c65cfe0b3eff240194f0d20170250d89e046eb4101b0633433c9f93f76a24ac2a79ef89dc,
  0x206cbdf9386c5983970e77e41d1507888432db1587bb7533fc5f384000a1651b8af2f5fba66576a13170399f947f74, 0x601b095194778c01491e50f773c631c0c512a428b4891c4b07561b490855db3bb41a7f241c97442039feb29657c, 0x9d5b092a21da4de5924ac7e102274d15c75309904d132568d96c1641427861308cff84eba0f14948b5cc72a4,
  0x810b5b35b427eabc8813d62f0ed5bd5b6d6d8428bb138919d24b207a6ff6d32c97a0ba63b9435d878fb2c, 0x2eaa339f7ecf7be94bfe880c412e736d73046b85403509274fc1fe18ba44b8f71ce411a47f26a458a0, 0x6483c620dd016855b87e150cd08a2e37f6fba7d3b601325031f1322adf269c47d96f79a0e50278,
  0x3ffca2d9c886287c04be9d8d9931e494b917b29b99ce4983bd4528e8c24683de1be7388dc4, 0x8b2c797bbf8c0091f8964cb31b683f5f65c82b71044cfa093f88e02c0fef6c444272c, 0x281f3d28934f2850612ddc3f17642706bfd842386c40119ee269c07451c0e1d4,
  0xbb445d46ca61282b0bab94f823a8ce487e6ce57bb1a6d4b844698143c, 0xffffffffc1efa664d909ed016142a5defc79e9d501894c154, 0xa07d06bd2945f6126958d45fb65d50988cd6a7c,
  0x3ffffffffffffffffffffff9d, 0x1]

private theorem eulerianCoefficients_eq : descentCoeffs 98 = eulerianCoefficients := by
  decide +kernel

private theorem upper : upperOK (descentCoeffs 98) first gaps = true := by
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

private theorem lower (i : Fin (lastRepresentative 99 - 2)) :
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

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 99) :
    StrictNegativeInterlacing (originalQuotient 99 k) (eulerian 98) 96 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N099
