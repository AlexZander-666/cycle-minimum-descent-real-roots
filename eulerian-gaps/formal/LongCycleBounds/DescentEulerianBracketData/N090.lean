import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentPackedData.C127L096.N090

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N090

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L096.N090 LongCycleBounds.DescentNecklace.Packed.C127L096.N090.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L096.N090 LongCycleBounds.DescentNecklace.Packed.C127L096.N090.rows

private theorem actual : RepresentativeChecks 90 previousNodes rows :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L096.N090 LongCycleBounds.DescentNecklace.Packed.C127L096.N090.dataChecks

private def first : LongCycleFinite.Dyadic := ⟨-618970019642690137449562112, 0⟩

private def gaps : List Window := [
  ⟨⟨-618949949585137941457403904, 0⟩, ⟨-4716252048130048, 0⟩⟩,
  ⟨⟨-4698642682216448, 0⟩, ⟨-131269918720, 0⟩⟩,
  ⟨⟨-131083010048, 0⟩, ⟨-417298432, 0⟩⟩,
  ⟨⟨-411312128, 0⟩, ⟨-10459328, 0⟩⟩,
  ⟨⟨-10439840, 0⟩, ⟨-812630, 0⟩⟩,
  ⟨⟨-812140, 0⟩, ⟨-247159, 1⟩⟩,
  ⟨⟨-494173, 2⟩, ⟨-29020, 0⟩⟩,
  ⟨⟨-464239, 4⟩, ⟨-293519, 5⟩⟩,
  ⟨⟨-73371, 3⟩, ⟨-458709, 7⟩⟩,
  ⟨⟨-458669, 7⟩, ⟨-104823, 6⟩⟩,
  ⟨⟨-419263, 8⟩, ⟨-431719, 9⟩⟩,
  ⟨⟨-431695, 9⟩, ⟨-487591, 10⟩⟩,
  ⟨⟨-487569, 10⟩, ⟨-37035, 7⟩⟩,
  ⟨⟨-74067, 8⟩, ⟨-190993, 10⟩⟩,
  ⟨⟨-381973, 11⟩, ⟨-516795, 12⟩⟩,
  ⟨⟨-129195, 10⟩, ⟨-181915, 11⟩⟩,
  ⟨⟨-363821, 12⟩, ⟨-264819, 12⟩⟩,
  ⟨⟨-264813, 12⟩, ⟨-396515, 13⟩⟩,
  ⟨⟨-396507, 13⟩, ⟨-38005, 10⟩⟩,
  ⟨⟨-152017, 12⟩, ⟨-118981, 12⟩⟩,
  ⟨⟨-118979, 12⟩, ⟨-189571, 13⟩⟩,
  ⟨⟨-1481, 6⟩, ⟨-153353, 13⟩⟩,
  ⟨⟨-306701, 14⟩, ⟨-125727, 13⟩⟩,
  ⟨⟨-502901, 15⟩, ⟨-208581, 14⟩⟩,
  ⟨⟨-104289, 13⟩, ⟨-87403, 13⟩⟩,
  ⟨⟨-349607, 15⟩, ⟨-147833, 14⟩⟩,
  ⟨⟨-147831, 14⟩, ⟨-63013, 13⟩⟩,
  ⟨⟨-252049, 15⟩, ⟨-108199, 14⟩⟩,
  ⟨⟨-432791, 16⟩, ⟨-373913, 16⟩⟩,
  ⟨⟨-93477, 14⟩, ⟨-162419, 15⟩⟩,
  ⟨⟨-162417, 15⟩, ⟨-283597, 16⟩⟩,
  ⟨⟨-283593, 16⟩, ⟨-248671, 16⟩⟩,
  ⟨⟨-497337, 17⟩, ⟨-437771, 17⟩⟩,
  ⟨⟨-218883, 16⟩, ⟨-386639, 17⟩⟩,
  ⟨⟨-386635, 17⟩, ⟨-42811, 14⟩⟩,
  ⟨⟨-85621, 15⟩, ⟨-304155, 17⟩⟩,
  ⟨⟨-304151, 17⟩, ⟨-135355, 16⟩⟩,
  ⟨⟨-270707, 17⟩, ⟨-482781, 18⟩⟩,
  ⟨⟨-482777, 18⟩, ⟨-431159, 18⟩⟩,
  ⟨⟨-431155, 18⟩, ⟨-192769, 17⟩⟩,
  ⟨⟨-192767, 17⟩, ⟨-21567, 14⟩⟩,
  ⟨⟨-345069, 18⟩, ⟨-309061, 18⟩⟩,
  ⟨⟨-154529, 17⟩, ⟨-138461, 17⟩⟩,
  ⟨⟨-34615, 15⟩, ⟨-496315, 19⟩⟩,
  ⟨⟨-496311, 19⟩, ⟨-444699, 19⟩⟩,
  ⟨⟨-444695, 19⟩, ⟨-398295, 19⟩⟩,
  ⟨⟨-398291, 19⟩, ⟨-356491, 19⟩⟩,
  ⟨⟨-44561, 16⟩, ⟨-159385, 18⟩⟩,
  ⟨⟨-159383, 18⟩, ⟨-71171, 17⟩⟩,
  ⟨⟨-284681, 19⟩, ⟨-507705, 20⟩⟩,
  ⟨⟨-507701, 20⟩, ⟨-451875, 20⟩⟩,
  ⟨⟨-451871, 20⟩, ⟨-401301, 20⟩⟩,
  ⟨⟨-401297, 20⟩, ⟨-88869, 18⟩⟩,
  ⟨⟨-22217, 16⟩, ⟨-156977, 19⟩⟩,
  ⟨⟨-313951, 20⟩, ⟨-138175, 19⟩⟩,
  ⟨⟨-276347, 20⟩, ⟨-60579, 18⟩⟩,
  ⟨⟨-484627, 21⟩, ⟨-211553, 20⟩⟩,
  ⟨⟨-211551, 20⟩, ⟨-183787, 20⟩⟩,
  ⟨⟨-183785, 20⟩, ⟨-79391, 19⟩⟩,
  ⟨⟨-39695, 18⟩, ⟨-68161, 19⟩⟩,
  ⟨⟨-272641, 21⟩, ⟨-116213, 20⟩⟩,
  ⟨⟨-232423, 21⟩, ⟨-393125, 22⟩⟩,
  ⟨⟨-12285, 17⟩, ⟨-82367, 20⟩⟩,
  ⟨⟨-329463, 22⟩, ⟨-273293, 22⟩⟩,
  ⟨⟨-273289, 22⟩, ⟨-224059, 22⟩⟩,
  ⟨⟨-448111, 23⟩, ⟨-90627, 21⟩⟩,
  ⟨⟨-181251, 22⟩, ⟨-288789, 23⟩⟩,
  ⟨⟨-18049, 19⟩, ⟨-452055, 24⟩⟩,
  ⟨⟨-452047, 24⟩, ⟨-346625, 24⟩⟩,
  ⟨⟨-346619, 24⟩, ⟨-259499, 24⟩⟩,
  ⟨⟨-129747, 23⟩, ⟨-377769, 25⟩⟩,
  ⟨⟨-377761, 25⟩, ⟨-265949, 25⟩⟩,
  ⟨⟨-132971, 24⟩, ⟨-44977, 23⟩⟩,
  ⟨⟨-359807, 26⟩, ⟨-231947, 26⟩⟩,
  ⟨⟨-463881, 27⟩, ⟨-281891, 27⟩⟩,
  ⟨⟨-140941, 26⟩, ⟨-318367, 28⟩⟩,
  ⟨⟨-79589, 26⟩, ⟨-327797, 29⟩⟩,
  ⟨⟨-40973, 26⟩, ⟨-74907, 28⟩⟩,
  ⟨⟨-299615, 30⟩, ⟨-468303, 32⟩⟩,
  ⟨⟨-58535, 29⟩, ⟨-296025, 33⟩⟩,
  ⟨⟨-37001, 30⟩, ⟨-139033, 34⟩⟩,
  ⟨⟨-278049, 35⟩, ⟨-169185, 37⟩⟩,
  ⟨⟨-169173, 37⟩, ⟨-210441, 41⟩⟩,
  ⟨⟨-420851, 42⟩, ⟨-5343, 41⟩⟩,
  ⟨⟨-341925, 47⟩, ⟨-137237, 54⟩⟩,
  ⟨⟨-137225, 54⟩, ⟨-502373, 71⟩⟩,
  ⟨⟨-251163, 70⟩, ⟨-262149, 107⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private def eulerianCoefficients : List ℤ := [
  0x1, 0x1ffffffffffffffffffffa6, 0x2165b9ffa4b2f3282eff965d2466eb0a9148,
  0x3fffffff4423c9c2018f685df7a25234133d15e4ca1ca, 0x6489c84eeab8e6307e54f978918f641c0710822b1d0bcbb8376a, 0x42cb50a6d8bb93cb5d8df1cf3eaaf6a8d05073c28eca3f019c3df55672,
  0x39dba761963b686e715877d36d52409d0802fc51730a399e7b13f31fe30cd68, 0x7feba884608132e3a3f74020c6048b497b8ae61863e0aa5e1c2493b50217c7084be, 0x4589298c6df7e7782697d4d8a956fd947cfe74a729858f7532da0627b5995240a1fe967,
  0xc78beff987d095ca2b9d779752175b06302d901b69630214d4d300bb7fd2ff7f60c118ef0c, 0xe8b56b335bc2d52c0b2e6200abf39c802891c74b59ea30de47c5cf3ca490b5d7ae631794d8810, 0x806d6b36d0fc704821e7a4aa14ccd50d486ed0e7e721e8b60351c293d97d2e14a6324e9aecbe86d4,
  0x2599d2e1a7c513bfb541d7da3f9c8d12595aaa291ffe58331e8ca7b58e7f75a92829d75b2e3701405fc, 0x6600049483b4fc54a8e7b8df6402f8e2999ca23473f15c518d9ffd340a602c2daa96d6d9286cb20048794, 0xab96633e8af3a5bc1a64ff16f4324edb8dc6ee4c808e37219bad3edfa706fb2326a36f6fcde40709b71d710,
  0xbd04113eb2f6d9e46bac5493f077bcfabee4dd721636ef56a7a374f2baa10d1d4b8b1b755902220b91a1a004c, 0x8e78738b3996a0c92621797e3726b0bf7036092368af0e6dd9d0085dadb81d7422ae5b26d45213ec05a95675113, 0x4c2b66bafc59ee9624534f392aef91d128222b5d1c9cdeb9a500d3484497f63547971a0b1c7701bcfb478b00c7106,
  0x1dc1f55a6ef5af65125fb9762302599d8b12f5676f40090aa62bcaf82021448cca512f86698c5a8e28aec6b6d92c6c8, 0x8b5ac0bec1936faf78525d575783de5152d37b1f86a6b5f5fec6252d186760c702ad84da4fdf6678f56fcffe5feb776a, 0x1f350f23063cc184c4efe48826aa3f81da0b891a7482ea6b88efe9e6621a0eec528775631046a943328610474900d2c2a2,
  0x571aa4eb976715634800aacf79618951eafce9a7f844bdfffeb5410d9c17932b63f97382083492c77246d951697825d8922, 0xc0541b0f11f443d9fb054f043e9ad1dfe341a97b86e663f370f175aa01ceb060e8c4b1db7f858dbc939c5507f17cd6b09e28, 0x15474110854a62bdfe446153bc4ba42db5b410c519a8bb703c6633d75daa640c6c32085bf4ce943bab75846848f7fd3cb6f68e,
  0x1e8c6e01601d6022a139042a968752c831451b20ab3eb753f2b0fafada8caddc52c2dd8c3d13708e0457670d07f918b6251fd75, 0x23ee83a86a51c7ee04e38d415a570f8cf386042451957482dcbc4b4d725ccafc70e4e12059d2fb62ec25cafc339cd8b6d5549650, 0x22ef3ec1933647157b7ab4268871874151c0c0f066d41c087fcbca955093773a8e584fb94571a72325d1d5b0100f43224b764edc0,
  0x1c4baad1623ac0530a115d6a5dcd1f031fa4b670d0cf4b061e0f592c2040031af86c7d7ede461e1d90151a9c24546e702de819e630, 0x133998d6dd4c11d7c02a155fbc04159623e6a3dc949bbca95d8589ed9356be4c1e2a546da0c0d2892b19815de4f9f5c1a8e3ac3a5d0, 0xb06387804ea6e67ac7b7463f84b89d5fd6883321aac7314bb3e59c3302683f82396f3701eea89e77b357342f83ee2625e9549617ab0,
  0x55d4bcd5f56c49551ad787dbd46684a0de7173277b60f52d9954f6b63f9e0d88e4c969b8aa60688ced80c70871ffc7f540b82479c7c0, 0x239c8b5a8e42429ccbcf11981ddcd1ad67d16e802ddf98d4ab598009a8fa5ff56a4ac19aa9a9c0ca667c9a9d40458c5ddb30b1bd36dd0, 0xca6e557ce91cb0e226834fe8349eabd0f80de4b8d76edc946069887ff1d92f3e102a76f098186da81447577d281645949d9aae6c0031a,
  0x3dd0e0f9699ac2a2f2a9fd3fb0aa22d6b7c308cebc657a6fd790555c65ecb9ee674b51717e6d19c7a2d9aed7c8918ab19fb4cba62ac30c, 0x1047679c47608df32da7b462542a9ce870cc5341dba2d2b4125d3b0681fb92413fe2faa41e744efc532764925fcb414b9be618312740790, 0x3b53722350c943025d173434dba20e5c7c9425936085d25966d30148ae4f8465928e6e3fdbd0adeab4a1fe38a39822f6766c185f57e1dd4,
  0xbb7a75647254696b3e5061dd105602bdcc1745488370b612c47483336e5ea4d945c5047e1cecd66f131844fce06ecfe3b93fad11864c7f4, 0x202e32f972aa25f7c33df667d286a1258d666f4c97508e8461d1ff0d441b2e2b972d919a1420d8938c5674ec639d80488987e60666bd3564, 0x4cf4a2e8ed0872993973a37c6abb8ced52fc061b99d6eb70eaa3f4faad4859d2f4d407f0373c977734d6300622ef194a1b270829f54064d0,
  0xa0807ca90ee6b80f5c1e81b6a7fdbb989e899c7ae3996d32c653041310e0214a1ad34e58dc306165e19470b85e4a46f1bc3b9627ab2ea4fc, 0x124589f21f11212dfe37e3869fbb6927b8a5d8bfaa2e1f07616fc1aacc9df7a58b165c0f8285ca6719c8b9ee8e721a99756625f3fb7f6c4f6, 0x1d18c067e85f60cdfde7a14c151178946d1390c081d523c72e5ab108d04626edd82a324ec8de83aca66db85ab9dca455f0bb5722c0077b888,
  0x288b1f1f1fe829f74272c302aa8cd3990616dd7f7ca8c70ebd73d7a3fbec1c1619e6366328898e56b8a7f45252c0fb9bf5236bb52da2ebb60, 0x317614314449cee45d1081e1585bfa17d9994067d86bea947f718ce4726fcd51c04448f3f120c9fd698fe0e5d380ff894d075b2b45f9b44b8, 0x34d91ecce22437370f22760016fa7aca6d22945ff8a8e04428bd1b676e5df2b7d4a4e5b51f6d55e25b8e708347b5b51b0c53566e79f512468,
  0x317614314449cee45d1081e1585bfa17d9994067d86bea947f718ce4726fcd51c04448f3f120c9fd698fe0e5d380ff894d075b2b45f9b44b8, 0x288b1f1f1fe829f74272c302aa8cd3990616dd7f7ca8c70ebd73d7a3fbec1c1619e6366328898e56b8a7f45252c0fb9bf5236bb52da2ebb60, 0x1d18c067e85f60cdfde7a14c151178946d1390c081d523c72e5ab108d04626edd82a324ec8de83aca66db85ab9dca455f0bb5722c0077b888,
  0x124589f21f11212dfe37e3869fbb6927b8a5d8bfaa2e1f07616fc1aacc9df7a58b165c0f8285ca6719c8b9ee8e721a99756625f3fb7f6c4f6, 0xa0807ca90ee6b80f5c1e81b6a7fdbb989e899c7ae3996d32c653041310e0214a1ad34e58dc306165e19470b85e4a46f1bc3b9627ab2ea4fc, 0x4cf4a2e8ed0872993973a37c6abb8ced52fc061b99d6eb70eaa3f4faad4859d2f4d407f0373c977734d6300622ef194a1b270829f54064d0,
  0x202e32f972aa25f7c33df667d286a1258d666f4c97508e8461d1ff0d441b2e2b972d919a1420d8938c5674ec639d80488987e60666bd3564, 0xbb7a75647254696b3e5061dd105602bdcc1745488370b612c47483336e5ea4d945c5047e1cecd66f131844fce06ecfe3b93fad11864c7f4, 0x3b53722350c943025d173434dba20e5c7c9425936085d25966d30148ae4f8465928e6e3fdbd0adeab4a1fe38a39822f6766c185f57e1dd4,
  0x1047679c47608df32da7b462542a9ce870cc5341dba2d2b4125d3b0681fb92413fe2faa41e744efc532764925fcb414b9be618312740790, 0x3dd0e0f9699ac2a2f2a9fd3fb0aa22d6b7c308cebc657a6fd790555c65ecb9ee674b51717e6d19c7a2d9aed7c8918ab19fb4cba62ac30c, 0xca6e557ce91cb0e226834fe8349eabd0f80de4b8d76edc946069887ff1d92f3e102a76f098186da81447577d281645949d9aae6c0031a,
  0x239c8b5a8e42429ccbcf11981ddcd1ad67d16e802ddf98d4ab598009a8fa5ff56a4ac19aa9a9c0ca667c9a9d40458c5ddb30b1bd36dd0, 0x55d4bcd5f56c49551ad787dbd46684a0de7173277b60f52d9954f6b63f9e0d88e4c969b8aa60688ced80c70871ffc7f540b82479c7c0, 0xb06387804ea6e67ac7b7463f84b89d5fd6883321aac7314bb3e59c3302683f82396f3701eea89e77b357342f83ee2625e9549617ab0,
  0x133998d6dd4c11d7c02a155fbc04159623e6a3dc949bbca95d8589ed9356be4c1e2a546da0c0d2892b19815de4f9f5c1a8e3ac3a5d0, 0x1c4baad1623ac0530a115d6a5dcd1f031fa4b670d0cf4b061e0f592c2040031af86c7d7ede461e1d90151a9c24546e702de819e630, 0x22ef3ec1933647157b7ab4268871874151c0c0f066d41c087fcbca955093773a8e584fb94571a72325d1d5b0100f43224b764edc0,
  0x23ee83a86a51c7ee04e38d415a570f8cf386042451957482dcbc4b4d725ccafc70e4e12059d2fb62ec25cafc339cd8b6d5549650, 0x1e8c6e01601d6022a139042a968752c831451b20ab3eb753f2b0fafada8caddc52c2dd8c3d13708e0457670d07f918b6251fd75, 0x15474110854a62bdfe446153bc4ba42db5b410c519a8bb703c6633d75daa640c6c32085bf4ce943bab75846848f7fd3cb6f68e,
  0xc0541b0f11f443d9fb054f043e9ad1dfe341a97b86e663f370f175aa01ceb060e8c4b1db7f858dbc939c5507f17cd6b09e28, 0x571aa4eb976715634800aacf79618951eafce9a7f844bdfffeb5410d9c17932b63f97382083492c77246d951697825d8922, 0x1f350f23063cc184c4efe48826aa3f81da0b891a7482ea6b88efe9e6621a0eec528775631046a943328610474900d2c2a2,
  0x8b5ac0bec1936faf78525d575783de5152d37b1f86a6b5f5fec6252d186760c702ad84da4fdf6678f56fcffe5feb776a, 0x1dc1f55a6ef5af65125fb9762302599d8b12f5676f40090aa62bcaf82021448cca512f86698c5a8e28aec6b6d92c6c8, 0x4c2b66bafc59ee9624534f392aef91d128222b5d1c9cdeb9a500d3484497f63547971a0b1c7701bcfb478b00c7106,
  0x8e78738b3996a0c92621797e3726b0bf7036092368af0e6dd9d0085dadb81d7422ae5b26d45213ec05a95675113, 0xbd04113eb2f6d9e46bac5493f077bcfabee4dd721636ef56a7a374f2baa10d1d4b8b1b755902220b91a1a004c, 0xab96633e8af3a5bc1a64ff16f4324edb8dc6ee4c808e37219bad3edfa706fb2326a36f6fcde40709b71d710,
  0x6600049483b4fc54a8e7b8df6402f8e2999ca23473f15c518d9ffd340a602c2daa96d6d9286cb20048794, 0x2599d2e1a7c513bfb541d7da3f9c8d12595aaa291ffe58331e8ca7b58e7f75a92829d75b2e3701405fc, 0x806d6b36d0fc704821e7a4aa14ccd50d486ed0e7e721e8b60351c293d97d2e14a6324e9aecbe86d4,
  0xe8b56b335bc2d52c0b2e6200abf39c802891c74b59ea30de47c5cf3ca490b5d7ae631794d8810, 0xc78beff987d095ca2b9d779752175b06302d901b69630214d4d300bb7fd2ff7f60c118ef0c, 0x4589298c6df7e7782697d4d8a956fd947cfe74a729858f7532da0627b5995240a1fe967,
  0x7feba884608132e3a3f74020c6048b497b8ae61863e0aa5e1c2493b50217c7084be, 0x39dba761963b686e715877d36d52409d0802fc51730a399e7b13f31fe30cd68, 0x42cb50a6d8bb93cb5d8df1cf3eaaf6a8d05073c28eca3f019c3df55672,
  0x6489c84eeab8e6307e54f978918f641c0710822b1d0bcbb8376a, 0x3fffffff4423c9c2018f685df7a25234133d15e4ca1ca, 0x2165b9ffa4b2f3282eff965d2466eb0a9148,
  0x1ffffffffffffffffffffa6, 0x1]

private theorem eulerianCoefficients_eq : descentCoeffs 89 = eulerianCoefficients := by
  decide +kernel

private theorem upper : upperOK (descentCoeffs 89) first gaps = true := by
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

private theorem lower (i : Fin (lastRepresentative 90 - 2)) :
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

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 90) :
    StrictNegativeInterlacing (originalQuotient 90 k) (eulerian 89) 87 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N090
