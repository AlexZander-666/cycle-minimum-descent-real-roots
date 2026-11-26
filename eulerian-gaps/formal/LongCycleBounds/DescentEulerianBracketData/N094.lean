import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentPackedData.C127L096.N094

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N094

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L096.N094 LongCycleBounds.DescentNecklace.Packed.C127L096.N094.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L096.N094 LongCycleBounds.DescentNecklace.Packed.C127L096.N094.rows

private theorem actual : RepresentativeChecks 94 previousNodes rows :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L096.N094 LongCycleBounds.DescentNecklace.Packed.C127L096.N094.dataChecks

private def first : LongCycleFinite.Dyadic := ⟨-9903520314283042199192993792, 0⟩

private def gaps : List Window := [
  ⟨⟨-9903199193362207063318462464, 0⟩, ⟨-24040959180275712, 0⟩⟩,
  ⟨⟨-23759484203565056, 0⟩, ⟨-415398625280, 0⟩⟩,
  ⟨⟨-414450712576, 0⟩, ⟨-1018984448, 0⟩⟩,
  ⟨⟨-1000032256, 0⟩, ⟨-21817472, 0⟩⟩,
  ⟨⟨-21769024, 0⟩, ⟨-1519524, 0⟩⟩,
  ⟨⟨-1518492, 0⟩, ⟨-213179, 0⟩⟩,
  ⟨⟨-213111, 0⟩, ⟨-47088, 0⟩⟩,
  ⟨⟨-47079, 0⟩, ⟨-226977, 4⟩⟩,
  ⟨⟨-453897, 5⟩, ⟨-85347, 4⟩⟩,
  ⟨⟨-85339, 4⟩, ⟨-151193, 6⟩⟩,
  ⟨⟨-75591, 5⟩, ⟨-303321, 8⟩⟩,
  ⟨⟨-303303, 8⟩, ⟨-335135, 9⟩⟩,
  ⟨⟨-335119, 9⟩, ⟨-12493, 5⟩⟩,
  ⟨⟨-24985, 6⟩, ⟨-253613, 10⟩⟩,
  ⟨⟨-63401, 8⟩, ⟨-338427, 11⟩⟩,
  ⟨⟨-21151, 7⟩, ⟨-470853, 12⟩⟩,
  ⟨⟨-470841, 12⟩, ⟨-10599, 7⟩⟩,
  ⟨⟨-42395, 9⟩, ⟨-503245, 13⟩⟩,
  ⟨⟨-251617, 12⟩, ⟨-382815, 13⟩⟩,
  ⟨⟨-382807, 13⟩, ⟨-297539, 13⟩⟩,
  ⟨⟨-297533, 13⟩, ⟨-471181, 14⟩⟩,
  ⟨⟨-471173, 14⟩, ⟨-379139, 14⟩⟩,
  ⟨⟨-379133, 14⟩, ⟨-309399, 14⟩⟩,
  ⟨⟨-154697, 13⟩, ⟨-127809, 13⟩⟩,
  ⟨⟨-511229, 15⟩, ⟨-106745, 13⟩⟩,
  ⟨⟨-213487, 14⟩, ⟨-180021, 14⟩⟩,
  ⟨⟨-360037, 15⟩, ⟨-153091, 14⟩⟩,
  ⟨⟨-153089, 14⟩, ⟨-262349, 15⟩⟩,
  ⟨⟨-131173, 14⟩, ⟨-452597, 16⟩⟩,
  ⟨⟨-28287, 12⟩, ⟨-98185, 14⟩⟩,
  ⟨⟨-12273, 11⟩, ⟨-342611, 16⟩⟩,
  ⟨⟨-342607, 16⟩, ⟨-300295, 16⟩⟩,
  ⟨⟨-75073, 14⟩, ⟨-66079, 14⟩⟩,
  ⟨⟨-264313, 16⟩, ⟨-58379, 14⟩⟩,
  ⟨⟨-467027, 17⟩, ⟨-51747, 14⟩⟩,
  ⟨⟨-103493, 15⟩, ⟨-368021, 17⟩⟩,
  ⟨⟨-368017, 17⟩, ⟨-328003, 17⟩⟩,
  ⟨⟨-5125, 11⟩, ⟨-292989, 17⟩⟩,
  ⟨⟨-146493, 16⟩, ⟨-32777, 14⟩⟩,
  ⟨⟨-131107, 16⟩, ⟨-235055, 17⟩⟩,
  ⟨⟨-235053, 17⟩, ⟨-105497, 16⟩⟩,
  ⟨⟨-13187, 13⟩, ⟨-379203, 18⟩⟩,
  ⟨⟨-5925, 12⟩, ⟨-21315, 14⟩⟩,
  ⟨⟨-85259, 16⟩, ⟨-76725, 16⟩⟩,
  ⟨⟨-306897, 18⟩, ⟨-276277, 18⟩⟩,
  ⟨⟨-138137, 17⟩, ⟨-497473, 19⟩⟩,
  ⟨⟨-497469, 19⟩, ⟨-447831, 19⟩⟩,
  ⟨⟨-111957, 17⟩, ⟨-100751, 17⟩⟩,
  ⟨⟨-50375, 16⟩, ⟨-362447, 19⟩⟩,
  ⟨⟨-90611, 17⟩, ⟨-325697, 19⟩⟩,
  ⟨⟨-162847, 18⟩, ⟨-292357, 19⟩⟩,
  ⟨⟨-146177, 18⟩, ⟨-524151, 20⟩⟩,
  ⟨⟨-262073, 19⟩, ⟨-469095, 20⟩⟩,
  ⟨⟨-469091, 20⟩, ⟨-209511, 19⟩⟩,
  ⟨⟨-209509, 19⟩, ⟨-186729, 19⟩⟩,
  ⟨⟨-186727, 19⟩, ⟨-166001, 19⟩⟩,
  ⟨⟨-165999, 19⟩, ⟨-147143, 19⟩⟩,
  ⟨⟨-147141, 19⟩, ⟨-519989, 21⟩⟩,
  ⟨⟨-32499, 17⟩, ⟨-457685, 21⟩⟩,
  ⟨⟨-457681, 21⟩, ⟨-401155, 21⟩⟩,
  ⟨⟨-401151, 21⟩, ⟨-174977, 20⟩⟩,
  ⟨⟨-174975, 20⟩, ⟨-303671, 21⟩⟩,
  ⟨⟨-75917, 19⟩, ⟨-130971, 20⟩⟩,
  ⟨⟨-523879, 22⟩, ⟨-112221, 20⟩⟩,
  ⟨⟨-448879, 22⟩, ⟨-47717, 19⟩⟩,
  ⟨⟨-381731, 22⟩, ⟨-160945, 21⟩⟩,
  ⟨⟨-160943, 21⟩, ⟨-268841, 22⟩⟩,
  ⟨⟨-268837, 22⟩, ⟨-111055, 21⟩⟩,
  ⟨⟨-222107, 22⟩, ⟨-181253, 22⟩⟩,
  ⟨⟨-90625, 21⟩, ⟨-18231, 19⟩⟩,
  ⟨⟨-291691, 23⟩, ⟨-230963, 23⟩⟩,
  ⟨⟨-230959, 23⟩, ⟨-359029, 24⟩⟩,
  ⟨⟨-179511, 23⟩, ⟨-273113, 24⟩⟩,
  ⟨⟨-68277, 22⟩, ⟨-405227, 25⟩⟩,
  ⟨⟨-405219, 25⟩, ⟨-4561, 19⟩⟩,
  ⟨⟨-145949, 24⟩, ⟨-406115, 26⟩⟩,
  ⟨⟨-406105, 26⟩, ⟨-33871, 23⟩⟩,
  ⟨⟨-270961, 26⟩, ⟨-343807, 27⟩⟩,
  ⟨⟨-343797, 27⟩, ⟨-205057, 27⟩⟩,
  ⟨⟨-410101, 28⟩, ⟨-113285, 27⟩⟩,
  ⟨⟨-113281, 27⟩, ⟨-56817, 27⟩⟩,
  ⟨⟨-227259, 29⟩, ⟨-100653, 29⟩⟩,
  ⟨⟨-402595, 31⟩, ⟨-302779, 32⟩⟩,
  ⟨⟨-75691, 30⟩, ⟨-91219, 32⟩⟩,
  ⟨⟨-45607, 31⟩, ⟨-322423, 36⟩⟩,
  ⟨⟨-322403, 36⟩, ⟨-181005, 38⟩⟩,
  ⟨⟨-361985, 39⟩, ⟨-403295, 43⟩⟩,
  ⟨⟨-403265, 43⟩, ⟨-279143, 48⟩⟩,
  ⟨⟨-17445, 44⟩, ⟨-347137, 57⟩⟩,
  ⟨⟨-86777, 55⟩, ⟨-396949, 73⟩⟩,
  ⟨⟨-24807, 69⟩, ⟨-262149, 111⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private def eulerianCoefficients : List ℤ := [
  0x1, 0x1fffffffffffffffffffffa2, 0xa912fd9e31ccc23b6dede937884905e5315a6,
  0x3fffffffc1eb06dfe9b6adcc2da2a45d9bf52fd5d82466a, 0xf57463ff930d65b537834a2d441c16046e395a67437698b074ab5b, 0x15225a11ba69d6077f0afeb0139f772e610ec2fc6a3402340bf3e73c5e62c,
  0x21eab1e113b6917b73179a31bfcbfde2b061050f5363b755a8f9ff86aabc1b9a9c, 0x7ff38bbba5965ce0ee55d12fe013f92d5ee09aafe6e9433411b3fe66a749a372fe8e8c, 0x6f7b1686a311e5666917e92184e64c8d628df185a9b3b7eedb03510d5584509df1b79d9a81,
  0x1e8594c4bc3795565c321c0e3676b8d48ad56ed7c9fc1e2ea1b5c2723c92b7e615ea4ac2dcae16, 0x3444e066afe73006601cb12fba8db560059092c3cd1ec926a47ca72450a07e4b2f006f56f4b4d594a, 0x290f957632c6e36e21bfd3ef4274fe7fb73d25730fc93080636e152eaee558877ae66d95a57a8561f7be,
  0x10af63ef5be87e3a7a894a00077039e5c85860e15d7137e04e3bf9d66ef5197752bbe3e5f20f30ffe109043, 0x3d88c07d89b12019df8e68ddbc33f4e474c24569faf97e388075487c6789540ca9f7e24b1a49598195f3a3fa8, 0x8a5b2f75eac13f7b2423462eaaa7e260d9ffa0265418f2bdd1b3fb936d39c843232ddaf8474eb237f12d0d4aba8,
  0xc8dc5d89d85ef252b212e27870e38b0912f51f5b5ab7933049dc2fa4c55399c853630d6e9a6473d0be806497e94a8, 0xc535445c0a6f3a5493af37bd15e9ee5039aa986ad59321cfc6247729185253fd32c428681027e341c808f9bcecae9ef, 0x8800b06aa6b98d70dd6e486eec2b8427795dcf2e82ddac9371f4bfb2c085308da795af78e8f8ec0731204d26a54d9b596,
  0x43fb5be6906b885cd8a0989335861e9965c5f10db8b3eeaec726064bad471a6fb5307c6316848a7d46f36013cf58e29c2d2, 0x19490b257aee8a97c3e985e8fba00929f45ab93bf7daf6eae50ef3aae56aa02ed1de3cf153a15af95a9b471265fbe5a4f7c4e, 0x727b1972ea511767e4c5c76160e25a9373b554a67a441d26e7e5f808f11a75b55491674b694e3384b4c1dd3e16f855a5eee8a5,
  0x191ddb0ee7de45ae9d82afc8a48d4d5a62d0125581eca1f415c0503b707eb49328eca581f800c75e66929fc00c9a8c9291502f1c, 0x457a70a9a21d556c2cc3dab27ac50b1ed04816a7bf238c881c64b033c4cef416dca224c0f6d8afeaee44c33a89e5ccacc386d036c, 0x99984db0a4143680bcd12ec09ebca1ac23e94b019b1f7dd35b3db6b64486d7bad2c9c9cc9d1a420a01381ad39745ddb2ebbf82c13c,
  0x112b20b0f1901a33e6803802a15bb3e959b43fd180d0065e9f9c639fcc9d0a8e1d0f93f40864fcec27611c4728ebd54fe086f8133047, 0x191b5fc6da0d172bff28b7e68f768f6a8fb160a3cddc9b2a580bc768d56141500fcaea34e6097db876ff11615276ea042789e57803cb2, 0x1e4e2ea9d26a38cc2b6b0b5f30bfa3bcb19fa57a1052bcfbbcbb980e784e23c50011be6ff4e725b8dc4341cc9165db0cfb90d9e2b200de,
  0x1e71bf926de917d333bdae83d9f001b87bf7d0d1ad6ddc828eaf00e5d86513d3c4f7c257a123f797b47171a86cc7a1f58c4ba908b247eca, 0x19a4175985ce64e02b02f51e8dd6d1dc5fbc9a5720a06077f7cebb02c3fa158037d8d05468d1af482e1b14e78dc1e1b15c9b2a2c8f9ac3c5, 0x12392ca7a42b613392619abe13761625d31f349d3c1e1b320ed340ecd8b447dad0a0cce0ec44f5804c5982bdeb2aafec184e6a15166f0dee0,
  0xafe1482c15559598f02c14ffe8c0a1386ffd0fd5c9ffc204558cb56f9cda511d15232611dab26e0954dfb3faa63c904702afe3f584d684fe0, 0x5a82812b6cd463cede29ecd13856880ceae38de1356babfed6c2fa3602d2593a34ae2efb356ad97ba6115be637c02dd9b8379894d690be1ce0, 0x27eb32dc0d1d10f10469b2599814fa8889c3d7c7d8f08e28c173948da6fefe4488c9488125bef54d6dce95c35d63e499be4f9e684c5cf08756a,
  0xf269ade1f4ea40274f5d1d7c5efdf7e7846cf38fc081cf7e442f4e63ac3e68e4488e9bad6ffdcd644e1e7ec7c00b8bc2eb41678c7dc4a860634, 0x4f76df7ed0d91ffa851afdf6c5ebd02576a0b1bc61db4edc4f8c4723ba3ac1ede1baecdc75e73cca8fb71dfd6a56708f8c53331292cf2981aadc, 0x169232939a0da17741f7eb0d4158cd7b7b304f2cfcad1b8f8fa15780b0394e3b6904327a74b7dbffa909a60626c232ccd1e88b7149c2bef2c0704,
  0x592344e155383570af624db847f5e28ee4289a2ad1815d1b778fcd62aa7c3c6fa5d98c9a9a8a22d96761dfed7635dae068f5273cd18352c9b08ee, 0x132ad3055492e59837a555ed23850e2b19b94368e17bc67cc98479f328bade2a6adb19b287ddd92e26f5e0ab86fee0d57bb098915aeafc7769e198, 0x3993e70829a2d45d13700d5f9763c323aa536838190531677f639262ba5da830530e6d31b43abbf36c8ad931bc8c6898c212ae3ffe9641bf68cdf8,
  0x974f2c2b48dff9a0182406734c45bc045baed2e8c63fbf557383faacdef755cdcd626efd222d5aae225a89afe0f652eeb906c9d2fd1616ceeb1158, 0x15c6ea937f2e4f25daf615e72417de3274fda28d2e8c6bd1d8861729a68653214c7fc3d23a0524f9d79e25780d4748d574a45ca09d2a17b55ecbc4a, 0x2c0175ba598cad2e7149fc644863d6cc08fbdf608eea5cb04eeaf472d070f1c597ee4aefc1695867b249fd2af40682bdc914a73feca12d9d1f3bb7c,
  0x4e1ff7bc9e7b721bac12ae884fa9a07aabedbdddbcae75fdf03fb2527b95ecb9f8fcf59066bf8f44f64f3c667c443acf0ea7502c08ad95354e22284, 0x79f847bf8f2b54c66829388f503724cbe7e07531b96eb68fd91f77831b901682d4df51f3c1f1db96e81fedde0e6f9689712d8e5ba252f992a8b5e0c, 0xa793dca3ad51c6c883bd4d476666466a854cdda21bdc6d4243773593a3e7c8b1970ac284059b058daba0d272852f8476b5a3f61b142274a4be5289e,
  0xcab946464dad9b4b1495fb4c2d24cf3805fd9ee5136437d7097ff50adf22ff00c95c58cba0f6995ba3e595dfb8053703c732664f10d11af73ebd7f0, 0xd7ffdaac54bee243a5e6f2653441eb9b88256beb4ab52dc44fb9d327dfffa5dd4af7989cfe658a651332599a00ae31a29dfb7d2aed34bd529e330f0, 0xcab946464dad9b4b1495fb4c2d24cf3805fd9ee5136437d7097ff50adf22ff00c95c58cba0f6995ba3e595dfb8053703c732664f10d11af73ebd7f0,
  0xa793dca3ad51c6c883bd4d476666466a854cdda21bdc6d4243773593a3e7c8b1970ac284059b058daba0d272852f8476b5a3f61b142274a4be5289e, 0x79f847bf8f2b54c66829388f503724cbe7e07531b96eb68fd91f77831b901682d4df51f3c1f1db96e81fedde0e6f9689712d8e5ba252f992a8b5e0c, 0x4e1ff7bc9e7b721bac12ae884fa9a07aabedbdddbcae75fdf03fb2527b95ecb9f8fcf59066bf8f44f64f3c667c443acf0ea7502c08ad95354e22284,
  0x2c0175ba598cad2e7149fc644863d6cc08fbdf608eea5cb04eeaf472d070f1c597ee4aefc1695867b249fd2af40682bdc914a73feca12d9d1f3bb7c, 0x15c6ea937f2e4f25daf615e72417de3274fda28d2e8c6bd1d8861729a68653214c7fc3d23a0524f9d79e25780d4748d574a45ca09d2a17b55ecbc4a, 0x974f2c2b48dff9a0182406734c45bc045baed2e8c63fbf557383faacdef755cdcd626efd222d5aae225a89afe0f652eeb906c9d2fd1616ceeb1158,
  0x3993e70829a2d45d13700d5f9763c323aa536838190531677f639262ba5da830530e6d31b43abbf36c8ad931bc8c6898c212ae3ffe9641bf68cdf8, 0x132ad3055492e59837a555ed23850e2b19b94368e17bc67cc98479f328bade2a6adb19b287ddd92e26f5e0ab86fee0d57bb098915aeafc7769e198, 0x592344e155383570af624db847f5e28ee4289a2ad1815d1b778fcd62aa7c3c6fa5d98c9a9a8a22d96761dfed7635dae068f5273cd18352c9b08ee,
  0x169232939a0da17741f7eb0d4158cd7b7b304f2cfcad1b8f8fa15780b0394e3b6904327a74b7dbffa909a60626c232ccd1e88b7149c2bef2c0704, 0x4f76df7ed0d91ffa851afdf6c5ebd02576a0b1bc61db4edc4f8c4723ba3ac1ede1baecdc75e73cca8fb71dfd6a56708f8c53331292cf2981aadc, 0xf269ade1f4ea40274f5d1d7c5efdf7e7846cf38fc081cf7e442f4e63ac3e68e4488e9bad6ffdcd644e1e7ec7c00b8bc2eb41678c7dc4a860634,
  0x27eb32dc0d1d10f10469b2599814fa8889c3d7c7d8f08e28c173948da6fefe4488c9488125bef54d6dce95c35d63e499be4f9e684c5cf08756a, 0x5a82812b6cd463cede29ecd13856880ceae38de1356babfed6c2fa3602d2593a34ae2efb356ad97ba6115be637c02dd9b8379894d690be1ce0, 0xafe1482c15559598f02c14ffe8c0a1386ffd0fd5c9ffc204558cb56f9cda511d15232611dab26e0954dfb3faa63c904702afe3f584d684fe0,
  0x12392ca7a42b613392619abe13761625d31f349d3c1e1b320ed340ecd8b447dad0a0cce0ec44f5804c5982bdeb2aafec184e6a15166f0dee0, 0x19a4175985ce64e02b02f51e8dd6d1dc5fbc9a5720a06077f7cebb02c3fa158037d8d05468d1af482e1b14e78dc1e1b15c9b2a2c8f9ac3c5, 0x1e71bf926de917d333bdae83d9f001b87bf7d0d1ad6ddc828eaf00e5d86513d3c4f7c257a123f797b47171a86cc7a1f58c4ba908b247eca,
  0x1e4e2ea9d26a38cc2b6b0b5f30bfa3bcb19fa57a1052bcfbbcbb980e784e23c50011be6ff4e725b8dc4341cc9165db0cfb90d9e2b200de, 0x191b5fc6da0d172bff28b7e68f768f6a8fb160a3cddc9b2a580bc768d56141500fcaea34e6097db876ff11615276ea042789e57803cb2, 0x112b20b0f1901a33e6803802a15bb3e959b43fd180d0065e9f9c639fcc9d0a8e1d0f93f40864fcec27611c4728ebd54fe086f8133047,
  0x99984db0a4143680bcd12ec09ebca1ac23e94b019b1f7dd35b3db6b64486d7bad2c9c9cc9d1a420a01381ad39745ddb2ebbf82c13c, 0x457a70a9a21d556c2cc3dab27ac50b1ed04816a7bf238c881c64b033c4cef416dca224c0f6d8afeaee44c33a89e5ccacc386d036c, 0x191ddb0ee7de45ae9d82afc8a48d4d5a62d0125581eca1f415c0503b707eb49328eca581f800c75e66929fc00c9a8c9291502f1c,
  0x727b1972ea511767e4c5c76160e25a9373b554a67a441d26e7e5f808f11a75b55491674b694e3384b4c1dd3e16f855a5eee8a5, 0x19490b257aee8a97c3e985e8fba00929f45ab93bf7daf6eae50ef3aae56aa02ed1de3cf153a15af95a9b471265fbe5a4f7c4e, 0x43fb5be6906b885cd8a0989335861e9965c5f10db8b3eeaec726064bad471a6fb5307c6316848a7d46f36013cf58e29c2d2,
  0x8800b06aa6b98d70dd6e486eec2b8427795dcf2e82ddac9371f4bfb2c085308da795af78e8f8ec0731204d26a54d9b596, 0xc535445c0a6f3a5493af37bd15e9ee5039aa986ad59321cfc6247729185253fd32c428681027e341c808f9bcecae9ef, 0xc8dc5d89d85ef252b212e27870e38b0912f51f5b5ab7933049dc2fa4c55399c853630d6e9a6473d0be806497e94a8,
  0x8a5b2f75eac13f7b2423462eaaa7e260d9ffa0265418f2bdd1b3fb936d39c843232ddaf8474eb237f12d0d4aba8, 0x3d88c07d89b12019df8e68ddbc33f4e474c24569faf97e388075487c6789540ca9f7e24b1a49598195f3a3fa8, 0x10af63ef5be87e3a7a894a00077039e5c85860e15d7137e04e3bf9d66ef5197752bbe3e5f20f30ffe109043,
  0x290f957632c6e36e21bfd3ef4274fe7fb73d25730fc93080636e152eaee558877ae66d95a57a8561f7be, 0x3444e066afe73006601cb12fba8db560059092c3cd1ec926a47ca72450a07e4b2f006f56f4b4d594a, 0x1e8594c4bc3795565c321c0e3676b8d48ad56ed7c9fc1e2ea1b5c2723c92b7e615ea4ac2dcae16,
  0x6f7b1686a311e5666917e92184e64c8d628df185a9b3b7eedb03510d5584509df1b79d9a81, 0x7ff38bbba5965ce0ee55d12fe013f92d5ee09aafe6e9433411b3fe66a749a372fe8e8c, 0x21eab1e113b6917b73179a31bfcbfde2b061050f5363b755a8f9ff86aabc1b9a9c,
  0x15225a11ba69d6077f0afeb0139f772e610ec2fc6a3402340bf3e73c5e62c, 0xf57463ff930d65b537834a2d441c16046e395a67437698b074ab5b, 0x3fffffffc1eb06dfe9b6adcc2da2a45d9bf52fd5d82466a,
  0xa912fd9e31ccc23b6dede937884905e5315a6, 0x1fffffffffffffffffffffa2, 0x1]

private theorem eulerianCoefficients_eq : descentCoeffs 93 = eulerianCoefficients := by
  decide +kernel

private theorem upper : upperOK (descentCoeffs 93) first gaps = true := by
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

private theorem lower (i : Fin (lastRepresentative 94 - 2)) :
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

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 94) :
    StrictNegativeInterlacing (originalQuotient 94 k) (eulerian 93) 91 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N094
