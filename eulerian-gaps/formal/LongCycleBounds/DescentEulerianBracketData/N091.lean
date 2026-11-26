import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentPackedData.C127L096.N091

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N091

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L096.N091 LongCycleBounds.DescentNecklace.Packed.C127L096.N091.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L096.N091 LongCycleBounds.DescentNecklace.Packed.C127L096.N091.rows

private theorem actual : RepresentativeChecks 91 previousNodes rows :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L096.N091 LongCycleBounds.DescentNecklace.Packed.C127L096.N091.dataChecks

private def first : LongCycleFinite.Dyadic := ⟨-1237940039285380274899124224, 0⟩

private def gaps : List Window := [
  ⟨⟨-1237899899170275882914807808, 0⟩, ⟨-7064774525321216, 0⟩⟩,
  ⟨⟨-7029572973363200, 0⟩, ⟨-175227535360, 0⟩⟩,
  ⟨⟨-174946516992, 0⟩, ⟨-518060032, 0⟩⟩,
  ⟨⟨-510077952, 0⟩, ⟨-12569440, 0⟩⟩,
  ⟨⟨-12544768, 0⟩, ⟨-950028, 0⟩⟩,
  ⟨⟨-949438, 0⟩, ⟨-141640, 0⟩⟩,
  ⟨⟨-283195, 1⟩, ⟨-524109, 4⟩⟩,
  ⟨⟨-524015, 4⟩, ⟨-81835, 3⟩⟩,
  ⟨⟨-81825, 3⟩, ⟨-506759, 7⟩⟩,
  ⟨⟨-253357, 6⟩, ⟨-459591, 8⟩⟩,
  ⟨⟨-459559, 8⟩, ⟨-470123, 9⟩⟩,
  ⟨⟨-470097, 9⟩, ⟨-132017, 8⟩⟩,
  ⟨⟨-132011, 8⟩, ⟨-159697, 9⟩⟩,
  ⟨⟨-319381, 10⟩, ⟨-410139, 11⟩⟩,
  ⟨⟨-410125, 11⟩, ⟨-138249, 10⟩⟩,
  ⟨⟨-276489, 11⟩, ⟨-97039, 10⟩⟩,
  ⟨⟨-388145, 12⟩, ⟨-281797, 12⟩⟩,
  ⟨⟨-140895, 11⟩, ⟨-52623, 10⟩⟩,
  ⟨⟨-420975, 13⟩, ⟨-80543, 11⟩⟩,
  ⟨⟨-322165, 13⟩, ⟨-251721, 13⟩⟩,
  ⟨⟨-503433, 14⟩, ⟨-200229, 13⟩⟩,
  ⟨⟨-400451, 14⟩, ⟨-323531, 14⟩⟩,
  ⟨⟨-161763, 13⟩, ⟨-264945, 14⟩⟩,
  ⟨⟨-264941, 14⟩, ⟨-219557, 14⟩⟩,
  ⟨⟨-439107, 15⟩, ⟨-367705, 15⟩⟩,
  ⟨⟨-91925, 13⟩, ⟨-77687, 13⟩⟩,
  ⟨⟨-310743, 15⟩, ⟨-66189, 13⟩⟩,
  ⟨⟨-264753, 15⟩, ⟨-454403, 16⟩⟩,
  ⟨⟨-227199, 15⟩, ⟨-392441, 16⟩⟩,
  ⟨⟨-392437, 16⟩, ⟨-340849, 16⟩⟩,
  ⟨⟨-340845, 16⟩, ⟨-148765, 15⟩⟩,
  ⟨⟨-297527, 16⟩, ⟨-130437, 15⟩⟩,
  ⟨⟨-521743, 17⟩, ⟨-57409, 14⟩⟩,
  ⟨⟨-459267, 17⟩, ⟨-405681, 17⟩⟩,
  ⟨⟨-405677, 17⟩, ⟨-359437, 17⟩⟩,
  ⟨⟨-359433, 17⟩, ⟨-159655, 16⟩⟩,
  ⟨⟨-159653, 16⟩, ⟨-71079, 15⟩⟩,
  ⟨⟨-284313, 17⟩, ⟨-253653, 17⟩⟩,
  ⟨⟨-507301, 18⟩, ⟨-56667, 15⟩⟩,
  ⟨⟨-113333, 16⟩, ⟨-405657, 18⟩⟩,
  ⟨⟨-405653, 18⟩, ⟨-363377, 18⟩⟩,
  ⟨⟨-181687, 17⟩, ⟨-2545, 11⟩⟩,
  ⟨⟨-325757, 18⟩, ⟨-292189, 18⟩⟩,
  ⟨⟨-146093, 17⟩, ⟨-131073, 17⟩⟩,
  ⟨⟨-524287, 19⟩, ⟨-470383, 19⟩⟩,
  ⟨⟨-470379, 19⟩, ⟨-210953, 18⟩⟩,
  ⟨⟨-421903, 19⟩, ⟨-378231, 19⟩⟩,
  ⟨⟨-94557, 17⟩, ⟨-169405, 18⟩⟩,
  ⟨⟨-338807, 19⟩, ⟨-151587, 18⟩⟩,
  ⟨⟨-303171, 19⟩, ⟨-67731, 17⟩⟩,
  ⟨⟨-270921, 19⟩, ⟨-483407, 20⟩⟩,
  ⟨⟨-483403, 20⟩, ⟨-430429, 20⟩⟩,
  ⟨⟨-430425, 20⟩, ⟨-382375, 20⟩⟩,
  ⟨⟨-382371, 20⟩, ⟨-338789, 20⟩⟩,
  ⟨⟨-338785, 20⟩, ⟨-299257, 20⟩⟩,
  ⟨⟨-149627, 19⟩, ⟨-131711, 19⟩⟩,
  ⟨⟨-263419, 20⟩, ⟨-461937, 21⟩⟩,
  ⟨⟨-115483, 19⟩, ⟨-403229, 21⟩⟩,
  ⟨⟨-403225, 21⟩, ⟨-87555, 19⟩⟩,
  ⟨⟨-43777, 18⟩, ⟨-2363, 14⟩⟩,
  ⟨⟨-75615, 19⟩, ⟨-259559, 21⟩⟩,
  ⟨⟨-64889, 19⟩, ⟨-221145, 21⟩⟩,
  ⟨⟨-442285, 22⟩, ⟨-186891, 21⟩⟩,
  ⟨⟨-373777, 22⟩, ⟨-312995, 22⟩⟩,
  ⟨⟨-312991, 22⟩, ⟨-518751, 23⟩⟩,
  ⟨⟨-64843, 20⟩, ⟨-26551, 19⟩⟩,
  ⟨⟨-212405, 22⟩, ⟨-85803, 21⟩⟩,
  ⟨⟨-343207, 23⟩, ⟨-273005, 23⟩⟩,
  ⟨⟨-34125, 20⟩, ⟨-213307, 23⟩⟩,
  ⟨⟨-426607, 24⟩, ⟨-163237, 23⟩⟩,
  ⟨⟨-326467, 24⟩, ⟨-487729, 25⟩⟩,
  ⟨⟨-60965, 22⟩, ⟨-177045, 24⟩⟩,
  ⟨⟨-177041, 24⟩, ⟨-497085, 26⟩⟩,
  ⟨⟨-497073, 26⟩, ⟨-335119, 26⟩⟩,
  ⟨⟨-167555, 25⟩, ⟨-215165, 26⟩⟩,
  ⟨⟨-215159, 26⟩, ⟨-32535, 24⟩⟩,
  ⟨⟨-16267, 23⟩, ⟨-36545, 25⟩⟩,
  ⟨⟨-146175, 27⟩, ⟨-299069, 29⟩⟩,
  ⟨⟨-299057, 29⟩, ⟨-271233, 30⟩⟩,
  ⟨⟨-271221, 30⟩, ⟨-209935, 31⟩⟩,
  ⟨⟨-209925, 31⟩, ⟨-262257, 33⟩⟩,
  ⟨⟨-262243, 33⟩, ⟨-485231, 36⟩⟩,
  ⟨⟨-485201, 36⟩, ⟨-36169, 35⟩⟩,
  ⟨⟨-72333, 36⟩, ⟨-175071, 41⟩⟩,
  ⟨⟨-87529, 40⟩, ⟨-34163, 44⟩⟩,
  ⟨⟨-136641, 46⟩, ⟨-205815, 55⟩⟩,
  ⟨⟨-102899, 54⟩, ⟨-334911, 71⟩⟩,
  ⟨⟨-334879, 71⟩, ⟨-262165, 108⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private def eulerianCoefficients : List ℤ := [
  0x1, 0x3ffffffffffffffffffffa5, 0x64312dfeee1989788cfec3176d34c11f94e8,
  0xfffffffdc6284a6615caaba25e170a6ac2e3f59c9e6a0, 0x1f6b0eae2959c7b00b80552233a9ded9f2bcc62bef990a8576eee, 0x190c4054ad3e7aab395c1c4cdaed6d0497e2004e7d3f5caae9417ea6cde,
  0x19502f256830bccdde156f1f132bfcd4cc70b2be0850500fb28541a247d5fb40, 0x3ff70065a48ad4c5ffb88c0b509b0cbf6cf40c9baed6d9f418f86851fe414d56bea8, 0x271fb6f6bd81e0c9ba84100d07e8e57ad027bac5e298209155bcf3b1cb25e8fe3729b97b,
  0x7ccd76621a51290e9846a0c8ebdc2d6a1a1806940ac2048f6918f77122745532a2ebf12300f, 0xa03b156e4d1063bd16dd8495d58122e48dd34740d661f08977da8069ebbb6ef41fb25c8e1f8c70, 0x6099e0653196a555e2052ecfcdceaff741dfa1aa6d9a2dcd971577f9d6d4ab379a348b88787db4ee0,
  0x1eb41cae0303ccf5f93fd3f57f818907d2a5bc0510a713fe70474b2cccd3d3bd7aeca24e08c0d3116264, 0x59f4f848d135c1391e630ea241d4bb2d2eb71240cb5d28cfd1ef0274a2d1ec0e3355455a6a2d84764536e4, 0xa2c17d2063b6070eeae0fbd3aa0a380c0944276a31ac0e26055322e463c7d442cd2384f55885cae69d03d9e0,
  0xc028622fe8222ffd4d680dffac1068cc640d71ef1cd189f9152d310972fffdd68050398fb5173eec8f2bfa0670, 0x9aca2d93af2bc08578f58e1d46d145956eec4c35cee0bd67a8345ce06b32c8280c56a4384052df083b857760783b, 0x583ad921871beba67e9bb1daa0292491b696675271be1942aed2b2d778938d02526838cc612e986f7f8a50fb5610d7,
  0x24ad16a9ad3354f9a9752320cad4007b425b1d2df71ccca6e8ba84bd6b5c2d3b20029064cf56c310a2ba4deaa5648a88, 0xb6723bfa86be6f405e7f811cf11a7cc0591a9bf7182b25f5728dd3c32f6a72fbcf756a3f2b1d2d34a0143d1aae21a75c0, 0x2b5750e93abea306e229444b10de544711f9812d62d8ed0937f585e1060cf7dd92fd8137407a2f888381be8b88b4bac9e46,
  0x802defd860dc1d914c159375f951ffeea2e0dd3b16c5ce6efa21e37dcf1170615bb581767eab557159bf8d3327b26cd83e96, 0x12b9bfab43e068337b7f7cef5363c762b991991b22fdd7225f2033e6c000f60a2d529025a117df2bc0e8b8bf50b275eab6a2a0, 0x231041ca170ac2f91e31b8387c379e936a15bc1d5bc1fdeae60240dfc46727953819c432b65bdd9b06da65407eb7369e16081c8,
  0x3537caa8688b13ab1776b79a21bef1ac95d466b5dc2f7ec61ac6e1857ba1bd7375356052d48ba21548fcdd273f4525e6412d5109, 0x42253de0062c5a4b92e13f990305d549e03c529e500dc9e0f750ea178b5481ff287768152d78c814ced79b0422e51f6f5a1689ed5, 0x43ef5ad0c30009efc197f3515cd5582176d6c69ec1eb4c6f0ed6f8af54900bf1ec6e3ed0bba488e40adb8b582800f77794accaa740,
  0x3a1d4b600f212c0f9b0195cf9fbae68e8a7eaec096b8f630cc0e02e7f7444fc69bc5973c9d11acd562739227938782c9c0e84abaf80, 0x29b2b86426e41aeb28bc7b5d477f14a2e2bbed2f1fec7a1e74c9c1974adcb9aa7ed6ff6b6d3278e3c70356ebffd1802e2d3ade6f8830, 0x1940634c3bf2af42cc318153415a9b9601b1eb09816c73bb3a5dba2b9663e2c965eb1e905945b4bcb6494bf0f1057807969629a0ae330,
  0xcfa381a09df0ec19aad08bb0cea1e5da2543bb1863128a96173e6e9d0fd2a91bc0bc4dba3e0a4fb51a31f1db7fcb645c101499d97f180, 0x5b011e3a6c147a2034cdcf7fe5ad43ebe2e7028a752e8a2ad90994ef529e2d09614fee92e297b9ad47b5e31972d10bd13c4bd3e27ec340, 0x2229b0979e47b5e4ad23d749658c7ba7397f3d84de29f30f4f3fe19aae75b8d49a2a69320e0b9bd085d56d4ec2baa0c56bf9f8c0ca7477a,
  0xb06e6f1ad05040fc9e3c76f20b20de49cdb98aa4784f534ab38a34c8d570669f6d19818cbe854732a692760568223c378a77a19726e9862, 0x3121e3dc6b3d111798f409fd06c26edb6ef1a00d49aa5fb25f5383ca72a2189ae258fe17d6464a6ba185ca3f656c752c3ff6e177df37b350, 0xbd7134f8ab20beb93e64b188ef7f1baf1c0bb2bdfc2ccd94267b3dc9e703b0a4d55cb5a3d74556d37443e5b69960ff1e725a29ff7ca9d1c0,
  0x279c4d0af790a75effa4832819b09d6cf0c69cf0915b84af9215593bc3b873c0d3ff84e7b28c3fad8fdcad987ef21b6be6c10127a4f2b30fc, 0x733e135e3bff93ffa399cd7958618d4a7b1419adea95a82c4afedce9279a25c8827e03bc0bcb0ac36c415bf9c70d01b66bfcf123d4cf3525c, 0x1242a72c2766d92bab6933f50b05eb33c85d3389c32c1ad1179da220e23b8b0ffe018ec8e480e711218e3110f38e6ae906128cf7b13b3e3400,
  0x2868cfeed18cbb96ecd6cdd653830263204db5aab335c9f76dbba270eb286f189af741d2bd68a164aac5dd2e07b13d1f88d216168e9b1ddcd0, 0x4e2b49d57484f4f8db6d2c5ea61fcc19981fdbfb248a26d6d46a971165a09118ada69135197849ae18215a774f6ee60473996494f3e5a1c49e, 0x8455ef86411ed3b9950b3034007bce8f43cf43c44dfcbcf1741451d2355bec9b51633dfe4f01d580f3d6bd58bc20a0d78f7498f66a49dff966,
  0xc44024db5ede13327c4b4ffb698ee268879825882485024d283766a325dd0044ee194916d78d398f038c89ad6bfc9134f50136df2abc4c12a0, 0xff1d62f2e984f43a531e820387fa9d5318489bc411588dd3aafc8ce5eeb90721bcd008621e2e3d97a0b90829d8b9a1d3b3ec471b367d443640, 0x122d620ade05a0e1b662061481ea8e85de489da787991392aa0fa5223af69a8f00ed417cabda1c64530fe4305f9c1ec06d01f8933202f29bf58,
  0x122d620ade05a0e1b662061481ea8e85de489da787991392aa0fa5223af69a8f00ed417cabda1c64530fe4305f9c1ec06d01f8933202f29bf58, 0xff1d62f2e984f43a531e820387fa9d5318489bc411588dd3aafc8ce5eeb90721bcd008621e2e3d97a0b90829d8b9a1d3b3ec471b367d443640, 0xc44024db5ede13327c4b4ffb698ee268879825882485024d283766a325dd0044ee194916d78d398f038c89ad6bfc9134f50136df2abc4c12a0,
  0x8455ef86411ed3b9950b3034007bce8f43cf43c44dfcbcf1741451d2355bec9b51633dfe4f01d580f3d6bd58bc20a0d78f7498f66a49dff966, 0x4e2b49d57484f4f8db6d2c5ea61fcc19981fdbfb248a26d6d46a971165a09118ada69135197849ae18215a774f6ee60473996494f3e5a1c49e, 0x2868cfeed18cbb96ecd6cdd653830263204db5aab335c9f76dbba270eb286f189af741d2bd68a164aac5dd2e07b13d1f88d216168e9b1ddcd0,
  0x1242a72c2766d92bab6933f50b05eb33c85d3389c32c1ad1179da220e23b8b0ffe018ec8e480e711218e3110f38e6ae906128cf7b13b3e3400, 0x733e135e3bff93ffa399cd7958618d4a7b1419adea95a82c4afedce9279a25c8827e03bc0bcb0ac36c415bf9c70d01b66bfcf123d4cf3525c, 0x279c4d0af790a75effa4832819b09d6cf0c69cf0915b84af9215593bc3b873c0d3ff84e7b28c3fad8fdcad987ef21b6be6c10127a4f2b30fc,
  0xbd7134f8ab20beb93e64b188ef7f1baf1c0bb2bdfc2ccd94267b3dc9e703b0a4d55cb5a3d74556d37443e5b69960ff1e725a29ff7ca9d1c0, 0x3121e3dc6b3d111798f409fd06c26edb6ef1a00d49aa5fb25f5383ca72a2189ae258fe17d6464a6ba185ca3f656c752c3ff6e177df37b350, 0xb06e6f1ad05040fc9e3c76f20b20de49cdb98aa4784f534ab38a34c8d570669f6d19818cbe854732a692760568223c378a77a19726e9862,
  0x2229b0979e47b5e4ad23d749658c7ba7397f3d84de29f30f4f3fe19aae75b8d49a2a69320e0b9bd085d56d4ec2baa0c56bf9f8c0ca7477a, 0x5b011e3a6c147a2034cdcf7fe5ad43ebe2e7028a752e8a2ad90994ef529e2d09614fee92e297b9ad47b5e31972d10bd13c4bd3e27ec340, 0xcfa381a09df0ec19aad08bb0cea1e5da2543bb1863128a96173e6e9d0fd2a91bc0bc4dba3e0a4fb51a31f1db7fcb645c101499d97f180,
  0x1940634c3bf2af42cc318153415a9b9601b1eb09816c73bb3a5dba2b9663e2c965eb1e905945b4bcb6494bf0f1057807969629a0ae330, 0x29b2b86426e41aeb28bc7b5d477f14a2e2bbed2f1fec7a1e74c9c1974adcb9aa7ed6ff6b6d3278e3c70356ebffd1802e2d3ade6f8830, 0x3a1d4b600f212c0f9b0195cf9fbae68e8a7eaec096b8f630cc0e02e7f7444fc69bc5973c9d11acd562739227938782c9c0e84abaf80,
  0x43ef5ad0c30009efc197f3515cd5582176d6c69ec1eb4c6f0ed6f8af54900bf1ec6e3ed0bba488e40adb8b582800f77794accaa740, 0x42253de0062c5a4b92e13f990305d549e03c529e500dc9e0f750ea178b5481ff287768152d78c814ced79b0422e51f6f5a1689ed5, 0x3537caa8688b13ab1776b79a21bef1ac95d466b5dc2f7ec61ac6e1857ba1bd7375356052d48ba21548fcdd273f4525e6412d5109,
  0x231041ca170ac2f91e31b8387c379e936a15bc1d5bc1fdeae60240dfc46727953819c432b65bdd9b06da65407eb7369e16081c8, 0x12b9bfab43e068337b7f7cef5363c762b991991b22fdd7225f2033e6c000f60a2d529025a117df2bc0e8b8bf50b275eab6a2a0, 0x802defd860dc1d914c159375f951ffeea2e0dd3b16c5ce6efa21e37dcf1170615bb581767eab557159bf8d3327b26cd83e96,
  0x2b5750e93abea306e229444b10de544711f9812d62d8ed0937f585e1060cf7dd92fd8137407a2f888381be8b88b4bac9e46, 0xb6723bfa86be6f405e7f811cf11a7cc0591a9bf7182b25f5728dd3c32f6a72fbcf756a3f2b1d2d34a0143d1aae21a75c0, 0x24ad16a9ad3354f9a9752320cad4007b425b1d2df71ccca6e8ba84bd6b5c2d3b20029064cf56c310a2ba4deaa5648a88,
  0x583ad921871beba67e9bb1daa0292491b696675271be1942aed2b2d778938d02526838cc612e986f7f8a50fb5610d7, 0x9aca2d93af2bc08578f58e1d46d145956eec4c35cee0bd67a8345ce06b32c8280c56a4384052df083b857760783b, 0xc028622fe8222ffd4d680dffac1068cc640d71ef1cd189f9152d310972fffdd68050398fb5173eec8f2bfa0670,
  0xa2c17d2063b6070eeae0fbd3aa0a380c0944276a31ac0e26055322e463c7d442cd2384f55885cae69d03d9e0, 0x59f4f848d135c1391e630ea241d4bb2d2eb71240cb5d28cfd1ef0274a2d1ec0e3355455a6a2d84764536e4, 0x1eb41cae0303ccf5f93fd3f57f818907d2a5bc0510a713fe70474b2cccd3d3bd7aeca24e08c0d3116264,
  0x6099e0653196a555e2052ecfcdceaff741dfa1aa6d9a2dcd971577f9d6d4ab379a348b88787db4ee0, 0xa03b156e4d1063bd16dd8495d58122e48dd34740d661f08977da8069ebbb6ef41fb25c8e1f8c70, 0x7ccd76621a51290e9846a0c8ebdc2d6a1a1806940ac2048f6918f77122745532a2ebf12300f,
  0x271fb6f6bd81e0c9ba84100d07e8e57ad027bac5e298209155bcf3b1cb25e8fe3729b97b, 0x3ff70065a48ad4c5ffb88c0b509b0cbf6cf40c9baed6d9f418f86851fe414d56bea8, 0x19502f256830bccdde156f1f132bfcd4cc70b2be0850500fb28541a247d5fb40,
  0x190c4054ad3e7aab395c1c4cdaed6d0497e2004e7d3f5caae9417ea6cde, 0x1f6b0eae2959c7b00b80552233a9ded9f2bcc62bef990a8576eee, 0xfffffffdc6284a6615caaba25e170a6ac2e3f59c9e6a0,
  0x64312dfeee1989788cfec3176d34c11f94e8, 0x3ffffffffffffffffffffa5, 0x1]

private theorem eulerianCoefficients_eq : descentCoeffs 90 = eulerianCoefficients := by
  decide +kernel

private theorem upper : upperOK (descentCoeffs 90) first gaps = true := by
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

private theorem lower (i : Fin (lastRepresentative 91 - 2)) :
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

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 91) :
    StrictNegativeInterlacing (originalQuotient 91 k) (eulerian 90) 88 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N091
