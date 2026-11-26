import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentPackedData.C127L088.N088

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N088

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L088.N088 LongCycleBounds.DescentNecklace.Packed.C127L088.N088.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L088.N088 LongCycleBounds.DescentNecklace.Packed.C127L088.N088.rows

private theorem actual : RepresentativeChecks 88 previousNodes rows :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L088.N088 LongCycleBounds.DescentNecklace.Packed.C127L088.N088.dataChecks

private def first : LongCycleFinite.Dyadic := ⟨-154742504910672534362390528, 0⟩

private def gaps : List Window := [
  ⟨⟨-154737487396284485364350976, 0⟩, ⟨-2092843074060288, 0⟩⟩,
  ⟨⟨-2088440732581888, 0⟩, ⟨-73836265472, 0⟩⟩,
  ⟨⟨-73753165824, 0⟩, ⟨-264111104, 0⟩⟩,
  ⟨⟨-260747264, 0⟩, ⟨-7238432, 0⟩⟩,
  ⟨⟨-7225936, 0⟩, ⟨-594038, 0⟩⟩,
  ⟨⟨-593700, 0⟩, ⟨-376247, 2⟩⟩,
  ⟨⟨-188071, 1⟩, ⟨-364323, 4⟩⟩,
  ⟨⟨-182131, 3⟩, ⟨-471755, 6⟩⟩,
  ⟨⟨-471701, 6⟩, ⟨-46973, 4⟩⟩,
  ⟨⟨-46969, 4⟩, ⟨-174451, 7⟩⟩,
  ⟨⟨-348879, 8⟩, ⟨-11373, 4⟩⟩,
  ⟨⟨-363917, 9⟩, ⟨-103883, 8⟩⟩,
  ⟨⟨-207757, 9⟩, ⟨-509709, 11⟩⟩,
  ⟨⟨-254845, 10⟩, ⟨-82793, 9⟩⟩,
  ⟨⟨-331161, 11⟩, ⟨-112781, 10⟩⟩,
  ⟨⟨-451111, 12⟩, ⟨-319475, 12⟩⟩,
  ⟨⟨-159733, 11⟩, ⟨-467459, 13⟩⟩,
  ⟨⟨-58431, 10⟩, ⟨-351529, 13⟩⟩,
  ⟨⟨-351521, 13⟩, ⟨-67649, 11⟩⟩,
  ⟨⟨-135295, 12⟩, ⟨-26563, 10⟩⟩,
  ⟨⟨-53125, 11⟩, ⟨-339579, 14⟩⟩,
  ⟨⟨-339573, 14⟩, ⟨-275409, 14⟩⟩,
  ⟨⟨-68851, 12⟩, ⟨-452579, 15⟩⟩,
  ⟨⟨-113143, 13⟩, ⟨-376125, 15⟩⟩,
  ⟨⟨-47015, 12⟩, ⟨-78931, 13⟩⟩,
  ⟨⟨-315719, 15⟩, ⟨-267361, 15⟩⟩,
  ⟨⟨-133679, 14⟩, ⟨-114085, 14⟩⟩,
  ⟨⟨-228167, 15⟩, ⟨-392121, 16⟩⟩,
  ⟨⟨-98029, 14⟩, ⟨-338979, 16⟩⟩,
  ⟨⟨-338975, 16⟩, ⟨-294613, 16⟩⟩,
  ⟨⟨-147305, 15⟩, ⟨-514521, 17⟩⟩,
  ⟨⟨-514515, 17⟩, ⟨-451159, 17⟩⟩,
  ⟨⟨-225577, 16⟩, ⟨-99261, 15⟩⟩,
  ⟨⟨-24815, 13⟩, ⟨-350531, 17⟩⟩,
  ⟨⟨-350527, 17⟩, ⟨-310321, 17⟩⟩,
  ⟨⟨-310317, 17⟩, ⟨-275375, 17⟩⟩,
  ⟨⟨-68843, 15⟩, ⟨-61213, 15⟩⟩,
  ⟨⟨-122425, 16⟩, ⟨-436147, 18⟩⟩,
  ⟨⟨-436143, 18⟩, ⟨-388967, 18⟩⟩,
  ⟨⟨-388963, 18⟩, ⟨-347245, 18⟩⟩,
  ⟨⟨-347241, 18⟩, ⟨-310223, 18⟩⟩,
  ⟨⟨-310219, 18⟩, ⟨-277267, 18⟩⟩,
  ⟨⟨-17329, 14⟩, ⟨-30981, 15⟩⟩,
  ⟨⟨-123923, 17⟩, ⟨-221519, 18⟩⟩,
  ⟨⟨-221517, 18⟩, ⟨-197901, 18⟩⟩,
  ⟨⟨-395799, 19⟩, ⟨-176673, 18⟩⟩,
  ⟨⟨-353343, 19⟩, ⟨-78781, 17⟩⟩,
  ⟨⟨-19695, 15⟩, ⟨-280659, 19⟩⟩,
  ⟨⟨-17541, 15⟩, ⟨-499103, 20⟩⟩,
  ⟨⟨-499099, 20⟩, ⟨-442897, 20⟩⟩,
  ⟨⟨-442893, 20⟩, ⟨-196047, 19⟩⟩,
  ⟨⟨-196045, 19⟩, ⟨-21635, 16⟩⟩,
  ⟨⟨-86539, 18⟩, ⟨-595, 11⟩⟩,
  ⟨⟨-304637, 20⟩, ⟨-133561, 19⟩⟩,
  ⟨⟨-267119, 20⟩, ⟨-233257, 20⟩⟩,
  ⟨⟨-466509, 21⟩, ⟨-101363, 19⟩⟩,
  ⟨⟨-50681, 18⟩, ⟨-350507, 21⟩⟩,
  ⟨⟨-350503, 21⟩, ⟨-75295, 19⟩⟩,
  ⟨⟨-37647, 18⟩, ⟨-32129, 18⟩⟩,
  ⟨⟨-257029, 21⟩, ⟨-435317, 22⟩⟩,
  ⟨⟨-27207, 18⟩, ⟨-365413, 22⟩⟩,
  ⟨⟨-11419, 17⟩, ⟨-303683, 22⟩⟩,
  ⟨⟨-303679, 22⟩, ⟨-124761, 21⟩⟩,
  ⟨⟨-499037, 23⟩, ⟨-101185, 21⟩⟩,
  ⟨⟨-202367, 22⟩, ⟨-323385, 23⟩⟩,
  ⟨⟨-323379, 23⟩, ⟨-507925, 24⟩⟩,
  ⟨⟨-126979, 22⟩, ⟨-390985, 24⟩⟩,
  ⟨⟨-195489, 23⟩, ⟨-294017, 24⟩⟩,
  ⟨⟨-294011, 24⟩, ⟨-430211, 25⟩⟩,
  ⟨⟨-215101, 24⟩, ⟨-304663, 25⟩⟩,
  ⟨⟨-19041, 21⟩, ⟨-415013, 26⟩⟩,
  ⟨⟨-415003, 26⟩, ⟨-269651, 26⟩⟩,
  ⟨⟨-269643, 26⟩, ⟨-165381, 26⟩⟩,
  ⟨⟨-323, 17⟩, ⟨-377673, 28⟩⟩,
  ⟨⟨-94415, 26⟩, ⟨-98483, 27⟩⟩,
  ⟨⟨-393917, 29⟩, ⟨-365771, 30⟩⟩,
  ⟨⟨-365755, 30⟩, ⟨-145685, 30⟩⟩,
  ⟨⟨-72839, 29⟩, ⟨-188631, 32⟩⟩,
  ⟨⟨-377241, 33⟩, ⟨-11417, 30⟩⟩,
  ⟨⟨-365321, 35⟩, ⟨-28925, 34⟩⟩,
  ⟨⟨-462769, 38⟩, ⟨-304125, 41⟩⟩,
  ⟨⟨-152051, 40⟩, ⟨-267693, 46⟩⟩,
  ⟨⟨-33459, 43⟩, ⟨-122045, 53⟩⟩,
  ⟨⟨-122035, 53⟩, ⟨-141297, 68⟩⟩,
  ⟨⟨-282567, 69⟩, ⟨-262149, 105⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private def eulerianCoefficients : List ℤ := [
  0x1, 0x7fffffffffffffffffffa8, 0x3b5f838d9691f763e1c660a5960c4c8563f,
  0x3ffffffeb972ac7543d5895aa63cec7146bc5b25d190, 0x40582dcd6305b433fa62e1dbb30e84662074f082f6e89f9eb5b, 0x1dafaba87b4e91a7fbbf172e81be536f099604941032188fd96d0fb08,
  0x12e44cc1f089ead530230c20f60b49eb27ab49f6faa6ca1a492066c3d9f125, 0x1ff981693b9abdc23b78567af5da01b2718dfa3b6ec254a6a5ca4d6203a54467c0, 0xdba2b60ae526dcde8c071c95ae400bc356b8b290efc3a58b3d53e7da67fb3d84bc182,
  0x1fe07914356cf9152e7c9495fc278ebea66149637990215cc089477a436155be4f3e19910, 0x1eaa54cac4c0e9ca9796d1cb29ec7f0c3170a71f6fb643eb2659dc8fa80fd16bbc785be2bdbe, 0xe2d4ee944a19ec91169312b3de05bab7632aa3bd73a40f6528b6b904ac98d0b0fd9622d421aae0,
  0x385479549c4e5b387adf6a424ca4c2b02a8f951e6432a087d2c50baf528a254abed0f998ebd56bdde, 0x82ee24dbe040b1b180e1e28a8b895f8b426f498d526a7ef728032757f7d2ec6f6785750c4ba4b394610, 0xbe4c095021e64827f505295a7121376b26a35336a24453035435c064358827a82a64d45dd6d8f9b745762,
  0xb65bc7f5c779e9d67f251fc623d17ea11bac33071cbc0c6df4254ac1495702709fa2dbd8e241513e6b7b9c0, 0x7840b8d667d6fd558e8660b57cdbfaf99ec665bb9861b1a362ae0feafb64da039d888ccd4369f3d3ee7eaa8f1, 0x3882eafe5b66bda2547be2ed371d2e3f35eb6b6e74d1d2355a71a2e19b0a36d76110759bbc63bfa5591e8524ee8,
  0x137b63c2fddcf557bd6ed8e48283481b6df6452fb11537effcf12ee97ae9c8d2bedb3b6b60051cff958c280fbf08f, 0x50c4ba3d70b0fa5ed6fd2c684749a649fc0d10c791e7b5cdff0585535eec4e70f0f5589fa62f4b92c7e180253bd250, 0x100e36aab35c925ef736eb5279c2acf49a7f0a9461a87d2b443995ea7326dbc2b7944e1a8a3bce656eb26b729353b083,
  0x27ddd4055ecaa8ef64c7a1dd8165f44df5b074c77beafdbf0fb4ec8d48cd1891dacb7ec86d1c7aba30ce09fb79d080208, 0x4e72f2e88e7e5a1a5c82ec0b2531f822e913302567cc5b85171fec34c05eb0a7d79dbd8d90e8310f2f95689691dc4121bd, 0x7bef25ddd887920376ebb81af52793332b084f55857a36c38c7df0ccba057bf923d9f7ecc773a33af45c69da067fa3d0b00,
  0x9ef7dfc0461f0391f645e171db4b11ecb398049212e2c0a28ed006c80bbec8a6b08637911d0f7a9fff4f647c635ada16e4b8, 0xa73142e5ede0aa267790e428bd7edfee05c2d14e4e82e4a0f8ef026f52838f3549918d0212b2820d31d99235afd99ba84f3c0, 0x916e13a95af824d8690051a52842b53fd28e44185123db84d268620647a3a2942b15f06f06606a12184f0e5b89bfaf2232b448,
  0x696b12e908607d7b46757fdebfa94b53942aabd7b5ec0514ec9cfa1a9e60267d69a728d09e7c7f4ce6a6cfc688942a88b904a80, 0x401b6ada37e2f8b52c85b270eff78549068ce4fdb244dd074d7e6085a1950df873d7749de3a703f62b5a340358eca68c97b70d08, 0x20e6488eafc886be8fae78a3c994a9c40330d0e0c6be5649fc7a546881eaf2809e97870bb60aff100f820f61a69b39d6c4e15c1c0,
  0xe52b22a8c65f1433373630b64fe68f835ba2afc8559456deefa517302c398c629e4e4aab0510f46e0be775d4516bffb55e8414ff8, 0x550763f2ed76d9697c5f60e688a5d0505e5405115f04aba6c3b4bb19a075d98a336beaee906fa9a1a9d192f81c70fa57c3993e7700, 0x1aff3bb1e57e026b5d36532adb67313b5da61a6f9fe808b6635795dee576c67d0eaeeb981d6a42f9888e31c2b7971183168ca34a022,
  0x75c888e0c31111d8d3a12d99b65f57030bedcdc0827b28f9ff3394cabf305b9871d8960dbc050e97fcf934c3e6863b264c30e8c1b50, 0x1bab6b6f667cef1ad517e77155632349a22977662e0d55d435e0f5b27c513bfbe32a60e478775411d19214148a6c6e24edf1a8a9055e, 0x59d946188e108c3787c5c0f8d13bcbf668bab036dfa75565284787a5d684868ffacb01e942e7e2b8bca988a7b522db33428bf1c84c20,
  0xfca820c2259ec46357caa6309cfb60ca367fb0a80b34399f3dbd11e961f143e93da4a732296a37ad0bf48b1c496dab328076d0bd29f6, 0x26887625ebe6a05ad63894db9f9af620b5eaea3dd5c6653e0460e662a21a5589a310a875f4d8a16238ae0a1649aaf18eb79cb6bb5c910, 0x51bc88d0f93a8dd1a8de0bc133d8455d12ca80af2cca02f656b29f63fd31a25151608c62fff5b6866fb34d2fe404270a40fd4d54c520a,
  0x96eef97593dbfede7913394f7fe5f4e2630c9aac9d6adf8ec57b2a6206b1699fee0ef9a37bee0721893bfb8967c8432dfd1fb59485c80, 0xf2e94c7e8f4afed170bf953f55b28a8ac050baa04fc01ef9353ab7990322b7481ba0ef77c8d020683841ee0bdfbcd23d4f7511731046c, 0x1550723d4140cc695908417d1067fab1f353a14b5145e443d8860211fe94e9b22506ec8f0c3c3b711622714cdd746e1cf0e78521dd3b60,
  0x1a1e9d155f6555f3ae27eea8fbe608410c258ecad55737925f4f4c841583f24183956518535883fd2b9b46b2c87b0655560f95db94b114, 0x1bf32cb735779d53c59f01b3b889362d9fce4b0d9e37de53527cf9250f9c8e8a65cb0c05a1e486daecac405ee7ee7b9246f65b6ac83540, 0x1a1e9d155f6555f3ae27eea8fbe608410c258ecad55737925f4f4c841583f24183956518535883fd2b9b46b2c87b0655560f95db94b114,
  0x1550723d4140cc695908417d1067fab1f353a14b5145e443d8860211fe94e9b22506ec8f0c3c3b711622714cdd746e1cf0e78521dd3b60, 0xf2e94c7e8f4afed170bf953f55b28a8ac050baa04fc01ef9353ab7990322b7481ba0ef77c8d020683841ee0bdfbcd23d4f7511731046c, 0x96eef97593dbfede7913394f7fe5f4e2630c9aac9d6adf8ec57b2a6206b1699fee0ef9a37bee0721893bfb8967c8432dfd1fb59485c80,
  0x51bc88d0f93a8dd1a8de0bc133d8455d12ca80af2cca02f656b29f63fd31a25151608c62fff5b6866fb34d2fe404270a40fd4d54c520a, 0x26887625ebe6a05ad63894db9f9af620b5eaea3dd5c6653e0460e662a21a5589a310a875f4d8a16238ae0a1649aaf18eb79cb6bb5c910, 0xfca820c2259ec46357caa6309cfb60ca367fb0a80b34399f3dbd11e961f143e93da4a732296a37ad0bf48b1c496dab328076d0bd29f6,
  0x59d946188e108c3787c5c0f8d13bcbf668bab036dfa75565284787a5d684868ffacb01e942e7e2b8bca988a7b522db33428bf1c84c20, 0x1bab6b6f667cef1ad517e77155632349a22977662e0d55d435e0f5b27c513bfbe32a60e478775411d19214148a6c6e24edf1a8a9055e, 0x75c888e0c31111d8d3a12d99b65f57030bedcdc0827b28f9ff3394cabf305b9871d8960dbc050e97fcf934c3e6863b264c30e8c1b50,
  0x1aff3bb1e57e026b5d36532adb67313b5da61a6f9fe808b6635795dee576c67d0eaeeb981d6a42f9888e31c2b7971183168ca34a022, 0x550763f2ed76d9697c5f60e688a5d0505e5405115f04aba6c3b4bb19a075d98a336beaee906fa9a1a9d192f81c70fa57c3993e7700, 0xe52b22a8c65f1433373630b64fe68f835ba2afc8559456deefa517302c398c629e4e4aab0510f46e0be775d4516bffb55e8414ff8,
  0x20e6488eafc886be8fae78a3c994a9c40330d0e0c6be5649fc7a546881eaf2809e97870bb60aff100f820f61a69b39d6c4e15c1c0, 0x401b6ada37e2f8b52c85b270eff78549068ce4fdb244dd074d7e6085a1950df873d7749de3a703f62b5a340358eca68c97b70d08, 0x696b12e908607d7b46757fdebfa94b53942aabd7b5ec0514ec9cfa1a9e60267d69a728d09e7c7f4ce6a6cfc688942a88b904a80,
  0x916e13a95af824d8690051a52842b53fd28e44185123db84d268620647a3a2942b15f06f06606a12184f0e5b89bfaf2232b448, 0xa73142e5ede0aa267790e428bd7edfee05c2d14e4e82e4a0f8ef026f52838f3549918d0212b2820d31d99235afd99ba84f3c0, 0x9ef7dfc0461f0391f645e171db4b11ecb398049212e2c0a28ed006c80bbec8a6b08637911d0f7a9fff4f647c635ada16e4b8,
  0x7bef25ddd887920376ebb81af52793332b084f55857a36c38c7df0ccba057bf923d9f7ecc773a33af45c69da067fa3d0b00, 0x4e72f2e88e7e5a1a5c82ec0b2531f822e913302567cc5b85171fec34c05eb0a7d79dbd8d90e8310f2f95689691dc4121bd, 0x27ddd4055ecaa8ef64c7a1dd8165f44df5b074c77beafdbf0fb4ec8d48cd1891dacb7ec86d1c7aba30ce09fb79d080208,
  0x100e36aab35c925ef736eb5279c2acf49a7f0a9461a87d2b443995ea7326dbc2b7944e1a8a3bce656eb26b729353b083, 0x50c4ba3d70b0fa5ed6fd2c684749a649fc0d10c791e7b5cdff0585535eec4e70f0f5589fa62f4b92c7e180253bd250, 0x137b63c2fddcf557bd6ed8e48283481b6df6452fb11537effcf12ee97ae9c8d2bedb3b6b60051cff958c280fbf08f,
  0x3882eafe5b66bda2547be2ed371d2e3f35eb6b6e74d1d2355a71a2e19b0a36d76110759bbc63bfa5591e8524ee8, 0x7840b8d667d6fd558e8660b57cdbfaf99ec665bb9861b1a362ae0feafb64da039d888ccd4369f3d3ee7eaa8f1, 0xb65bc7f5c779e9d67f251fc623d17ea11bac33071cbc0c6df4254ac1495702709fa2dbd8e241513e6b7b9c0,
  0xbe4c095021e64827f505295a7121376b26a35336a24453035435c064358827a82a64d45dd6d8f9b745762, 0x82ee24dbe040b1b180e1e28a8b895f8b426f498d526a7ef728032757f7d2ec6f6785750c4ba4b394610, 0x385479549c4e5b387adf6a424ca4c2b02a8f951e6432a087d2c50baf528a254abed0f998ebd56bdde,
  0xe2d4ee944a19ec91169312b3de05bab7632aa3bd73a40f6528b6b904ac98d0b0fd9622d421aae0, 0x1eaa54cac4c0e9ca9796d1cb29ec7f0c3170a71f6fb643eb2659dc8fa80fd16bbc785be2bdbe, 0x1fe07914356cf9152e7c9495fc278ebea66149637990215cc089477a436155be4f3e19910,
  0xdba2b60ae526dcde8c071c95ae400bc356b8b290efc3a58b3d53e7da67fb3d84bc182, 0x1ff981693b9abdc23b78567af5da01b2718dfa3b6ec254a6a5ca4d6203a54467c0, 0x12e44cc1f089ead530230c20f60b49eb27ab49f6faa6ca1a492066c3d9f125,
  0x1dafaba87b4e91a7fbbf172e81be536f099604941032188fd96d0fb08, 0x40582dcd6305b433fa62e1dbb30e84662074f082f6e89f9eb5b, 0x3ffffffeb972ac7543d5895aa63cec7146bc5b25d190,
  0x3b5f838d9691f763e1c660a5960c4c8563f, 0x7fffffffffffffffffffa8, 0x1]

private theorem eulerianCoefficients_eq : descentCoeffs 87 = eulerianCoefficients := by
  decide +kernel

private theorem upper : upperOK (descentCoeffs 87) first gaps = true := by
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

private theorem lower (i : Fin (lastRepresentative 88 - 2)) :
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

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 88) :
    StrictNegativeInterlacing (originalQuotient 88 k) (eulerian 87) 85 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N088
