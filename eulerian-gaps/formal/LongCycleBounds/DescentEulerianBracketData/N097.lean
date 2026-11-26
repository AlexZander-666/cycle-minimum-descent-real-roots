import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentPackedData.C127L104.N097

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N097

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L104.N097 LongCycleBounds.DescentNecklace.Packed.C127L104.N097.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L104.N097 LongCycleBounds.DescentNecklace.Packed.C127L104.N097.rows

private theorem actual : RepresentativeChecks 97 previousNodes rows :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L104.N097 LongCycleBounds.DescentNecklace.Packed.C127L104.N097.dataChecks

private def first : LongCycleFinite.Dyadic := ⟨-79228162514264337593543950336, 0⟩

private def gaps : List Window := [
  ⟨⟨-79225593546897656506547699712, 0⟩, ⟨-81038954769416192, 0⟩⟩,
  ⟨⟨-78786880077824000, 0⟩, ⟨-986565312512, 0⟩⟩,
  ⟨⟨-983344087040, 0⟩, ⟨-1974800384, 0⟩⟩,
  ⟨⟨-1929809920, 0⟩, ⟨-37873152, 0⟩⟩,
  ⟨⟨-37779072, 0⟩, ⟨-2426840, 0⟩⟩,
  ⟨⟨-2425032, 0⟩, ⟨-320705, 0⟩⟩,
  ⟨⟨-320595, 0⟩, ⟨-67652, 0⟩⟩,
  ⟨⟨-135277, 1⟩, ⟨-314559, 4⟩⟩,
  ⟨⟨-78629, 2⟩, ⟨-14363, 1⟩⟩,
  ⟨⟨-114893, 4⟩, ⟨-198791, 6⟩⟩,
  ⟨⟨-397553, 7⟩, ⟨-391037, 8⟩⟩,
  ⟨⟨-195507, 7⟩, ⟨-424951, 9⟩⟩,
  ⟨⟨-212465, 8⟩, ⟨-124951, 8⟩⟩,
  ⟨⟨-499783, 10⟩, ⟨-313267, 10⟩⟩,
  ⟨⟨-313255, 10⟩, ⟨-103421, 9⟩⟩,
  ⟨⟨-413671, 11⟩, ⟨-142587, 10⟩⟩,
  ⟨⟨-285165, 11⟩, ⟨-50949, 9⟩⟩,
  ⟨⟨-203791, 11⟩, ⟨-1173, 4⟩⟩,
  ⟨⟨-300281, 12⟩, ⟨-227037, 12⟩⟩,
  ⟨⟨-28379, 9⟩, ⟨-87759, 11⟩⟩,
  ⟨⟨-351029, 13⟩, ⟨-69159, 11⟩⟩,
  ⟨⟨-138315, 12⟩, ⟨-443353, 14⟩⟩,
  ⟨⟨-221673, 13⟩, ⟨-360479, 14⟩⟩,
  ⟨⟨-360473, 14⟩, ⟨-296873, 14⟩⟩,
  ⟨⟨-74217, 12⟩, ⟨-123629, 13⟩⟩,
  ⟨⟨-494509, 15⟩, ⟨-207995, 14⟩⟩,
  ⟨⟨-25999, 11⟩, ⟨-353041, 15⟩⟩,
  ⟨⟨-88259, 13⟩, ⟨-150989, 14⟩⟩,
  ⟨⟨-150987, 14⟩, ⟨-260113, 15⟩⟩,
  ⟨⟨-520221, 16⟩, ⟨-112729, 14⟩⟩,
  ⟨⟨-450911, 16⟩, ⟨-196511, 15⟩⟩,
  ⟨⟨-196509, 15⟩, ⟨-172137, 15⟩⟩,
  ⟨⟨-172135, 15⟩, ⟨-302919, 16⟩⟩,
  ⟨⟨-75729, 14⟩, ⟨-33449, 13⟩⟩,
  ⟨⟨-267589, 16⟩, ⟨-237227, 16⟩⟩,
  ⟨⟨-474449, 17⟩, ⟨-52743, 14⟩⟩,
  ⟨⟨-105485, 15⟩, ⟨-188147, 16⟩⟩,
  ⟨⟨-376291, 17⟩, ⟨-336413, 17⟩⟩,
  ⟨⟨-336409, 17⟩, ⟨-301405, 17⟩⟩,
  ⟨⟨-150701, 16⟩, ⟨-270547, 17⟩⟩,
  ⟨⟨-270545, 17⟩, ⟨-243239, 17⟩⟩,
  ⟨⟨-486473, 18⟩, ⟨-437963, 18⟩⟩,
  ⟨⟨-54745, 15⟩, ⟨-394723, 18⟩⟩,
  ⟨⟨-394719, 18⟩, ⟨-11127, 13⟩⟩,
  ⟨⟨-89015, 16⟩, ⟨-321399, 18⟩⟩,
  ⟨⟨-80349, 16⟩, ⟨-290233, 18⟩⟩,
  ⟨⟨-290231, 18⟩, ⟨-262145, 18⟩⟩,
  ⟨⟨-524285, 19⟩, ⟨-29597, 15⟩⟩,
  ⟨⟨-118387, 17⟩, ⟨-427633, 19⟩⟩,
  ⟨⟨-427629, 19⟩, ⟨-24125, 15⟩⟩,
  ⟨⟨-385997, 19⟩, ⟨-348195, 19⟩⟩,
  ⟨⟨-348191, 19⟩, ⟨-39227, 16⟩⟩,
  ⟨⟨-313813, 19⟩, ⟨-35315, 16⟩⟩,
  ⟨⟨-282517, 19⟩, ⟨-508007, 20⟩⟩,
  ⟨⟨-508003, 20⟩, ⟨-227999, 19⟩⟩,
  ⟨⟨-227997, 19⟩, ⟨-102137, 18⟩⟩,
  ⟨⟨-408545, 20⟩, ⟨-365247, 20⟩⟩,
  ⟨⟨-365243, 20⟩, ⟨-81433, 18⟩⟩,
  ⟨⟨-10179, 15⟩, ⟨-18105, 16⟩⟩,
  ⟨⟨-289677, 20⟩, ⟨-256809, 20⟩⟩,
  ⟨⟨-513613, 21⟩, ⟨-453721, 21⟩⟩,
  ⟨⟨-113429, 19⟩, ⟨-199609, 20⟩⟩,
  ⟨⟨-199607, 20⟩, ⟨-174851, 20⟩⟩,
  ⟨⟨-174849, 20⟩, ⟨-304805, 21⟩⟩,
  ⟨⟨-304801, 21⟩, ⟨-129, 10⟩⟩,
  ⟨⟨-264189, 21⟩, ⟨-14223, 17⟩⟩,
  ⟨⟨-455131, 22⟩, ⟨-389307, 22⟩⟩,
  ⟨⟨-194651, 21⟩, ⟨-165197, 21⟩⟩,
  ⟨⟨-330389, 22⟩, ⟨-69483, 20⟩⟩,
  ⟨⟨-34741, 19⟩, ⟨-115741, 21⟩⟩,
  ⟨⟨-231479, 22⟩, ⟨-381271, 23⟩⟩,
  ⟨⟨-190633, 22⟩, ⟨-310005, 23⟩⟩,
  ⟨⟨-19375, 19⟩, ⟨-124207, 22⟩⟩,
  ⟨⟨-124205, 22⟩, ⟨-391535, 24⟩⟩,
  ⟨⟨-48941, 21⟩, ⟨-75671, 22⟩⟩,
  ⟨⟨-302679, 24⟩, ⟨-114427, 23⟩⟩,
  ⟨⟨-457699, 25⟩, ⟨-168603, 24⟩⟩,
  ⟨⟨-337199, 25⟩, ⟨-240983, 25⟩⟩,
  ⟨⟨-481955, 26⟩, ⟨-166121, 25⟩⟩,
  ⟨⟨-166117, 25⟩, ⟨-438749, 27⟩⟩,
  ⟨⟨-438737, 27⟩, ⟨-68749, 25⟩⟩,
  ⟨⟨-274987, 27⟩, ⟨-323441, 28⟩⟩,
  ⟨⟨-161715, 27⟩, ⟨-175747, 28⟩⟩,
  ⟨⟨-351481, 29⟩, ⟨-172851, 29⟩⟩,
  ⟨⟨-43211, 27⟩, ⟨-18691, 27⟩⟩,
  ⟨⟨-299043, 31⟩, ⟨-436975, 33⟩⟩,
  ⟨⟨-436953, 33⟩, ⟨-253979, 34⟩⟩,
  ⟨⟨-507929, 35⟩, ⟨-428695, 37⟩⟩,
  ⟨⟨-107167, 35⟩, ⟨-226575, 39⟩⟩,
  ⟨⟨-453119, 40⟩, ⟨-464685, 44⟩⟩,
  ⟨⟨-464651, 44⟩, ⟨-35647, 46⟩⟩,
  ⟨⟨-142577, 48⟩, ⟨-292771, 58⟩⟩,
  ⟨⟨-146373, 57⟩, ⟨-470437, 75⟩⟩,
  ⟨⟨-470393, 75⟩, ⟨-262165, 114⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private def eulerianCoefficients : List ℤ := [
  0x1, 0xffffffffffffffffffffff9f, 0x11d500bfaf40a64044981798db5fb39f2c18db1,
  0xffffffff93e4ab75e987fd896025f0f14e0bcf0b04adf42f, 0x77d9d52a62cd8a65a807ce8bb076a75d1529a2dc4241e02b0042a739, 0x11d4fde916a332494681621318c53df5423aefa2a71be8ed461c8bb88711ae7,
  0x2d71ae95630815527410431a838993fb4362180c3a1c0432a3c5db3c7e1626ec4609, 0xffeec7d8282c77ce7790efe4838d95f2dfa22565de7cc98bd02d76bb0c5f1521bc086857, 0x13d9a56eec98b93a3cb11c0d64ec09c288eb2d9c49d4627a0e96b9f896af99e092d98259e55bd,
  0x77616b80454354869ae186bba4d62d4aa1be0f0cc98792a5908d884cd572592a34287bea9c7f8263, 0x11093b0a13d20c908c1bd138d85cbb9eb949bbf521fc417d39c17ee9b5e366bf2bb24dd5e096bc10a26d, 0x116d2e12c093e0611f0eace29346daf5b6f6b402890458d347c94814cf8f79f727faf86b31ea9e80f048ef3,
  0x90b7f727794bc865d1566dc802d3e5a46434f97bb0d4039ec27b72650355e78df6628f1c4fdbdb60d1ea8f1a5, 0x29f05dc343d0dd4d031c6d8596ee6d0eb9c784f2b02f1e76d7f55e20d2582f4c19503733336e92f769f4436410fb, 0x75045b1c188314ed01fd545e295791ab4b323873c74d38bda52c68d61d8d9b2313df4c7c806ff8d36929f41b69e9f5,
  0xd088ca8468fc2fe6460566a50e87d90947b7cd4ab2676f04b742edabbcaa6113fdec6d0a68ccf3b392e458e9096907eb, 0xf90eca2cf7b4ff2595a41801d58d1c1c87f5feaba40a48297b71f1399c0e9e5edd256ac6475074e690e83ac29484a4ff97, 0xcf5af5ad24819dc85a5aef3abc4a099f94f8716d85c198214a1c8e511e685cdb8fca9539bfea8fbebd915292bed5fe2b91c9,
  0x7c54cc209eec505575e447c0c1ffeef28771d96c8e317c077797ba9e20b69fe2cc6c8c5eac2a5512e2c21a5ee3815a3c5adae7, 0x372cd5cef33084f72a7b95b3f818e156c2ce5085eb1966ac3b2873c60a19e1c2dcdc168182f3a4564a878d57b3ac51b660060a39, 0x128b6563d1805983f83388da5c8940c02a62976052fab59fa415c65d1d56878ec9b58003ce35c5261c0f6ad9faa54a795f9b6a123f,
  0x4d0725e03f11d7732d0cbf55ae6472355ae0f88253af1f399b6ba94ad748cb03ed3e25f3e5f584c9caade1395b680f53a062cef2ca1, 0xfb5528519be0cab435b60a30bbf4700ba6a8b9a7c8853202c7aef0c03d25a0dd3734f3d7ac136f46feca59c2d0b6940133a9be72b96f, 0x28da9e4dfbf2a3d028e949b3d8439bf5247c280e5a08173279cfa5c36319844fbb04e1acaf12e80963384be35d952f115128ddcf912731,
  0x55c6447d5839421c6009c352ab6d9e265af82df37170e7122bee64a6cd2a77f65bc96601e3f6e9dc704ee703f64fb31310a048e33451f93, 0x930090968045aba59e2348a3866405940098c67d8f8803f7e960d821b8343f7491168ebce50764e8e2fc82edf9fa23be545e7adbfc84ac4d, 0xcfab4ae127c492a326d1acc2290b8ea204c3ac31db52d1fdeb5e6671fd2de96bb562936c8988ffc78d7c1a4eef1e0d0b8dd68025ae6f39463,
  0xf3eb3a6d535415e4b32c9073c9e4d60e59c00efcfcfd86fefb178265dc39b685bb9103e6b30bb145efca57f17e112faa271254bc4364d3d23d, 0xf006f46332a6b8bb60e8a3d4cf5c0f8618bb01cf5ffe3385f10d9d9e7d7ddfe8b455e26f4af315552f1a3f87e34be190163db3767b714fad74b, 0xc73bedd6e53c857019863402485f791fdb2f9fae0c3b9b9aaa29a54a281cb3fc74dba6a961f9e2d46064feb0b0d00c57e5e034d24cf5c367b615,
  0x8c56ed7afcce7122efe78bf76bd937b7ba1dd11e24a68f736d42580ce11c3f89e6446f2a7458dd2df298bdbf2faa826700ebb15fac38863effc7b, 0x5457fa55e20350df5c91ee81997a32c9a3e6419aaf27b1f25db1a3acfe893fe2ca84a77b67a13eb7b9b40488cc52ead0bf59698a9d9766e2f05da5, 0x2b755da89382a7c996482e544410acfd5e4cfdb1fe06cbba39fe381864c3463ac0b720a6e2414ec4d3a7430e4e9d43e329927349516e63ac32b434a,
  0x1347ce43a81cb123d17739d669a925ce10678dab99025e142c35f7227a2889b8e277b7b364790d62aadaf570ed3ffaaf30544b7963c4e2f3301df8f6, 0x764c5932bfbc574a33397481965e0bb492a92cc33b0d5df7b60d3e4a6fa62121c0c485f270ee4fb12a527f4385a67cb50a1502bdd97b037aba8e3e2a, 0x2758d498d6625167a75134bfe1af9392cb8b324ef441ead31e9aab147c5cca3299512c0a7af7d1258bd80cc6606cf0ec9ed732c01ae6fc9a7cbd96496,
  0xb62d50bcf7692d3bfba0923996340f70ccf48f84d643f549fff61a6366104b709d06c4cd49c89dad387328be00d05fa83d68b196a097621621291d2fa, 0x2dfdb5e811e79a3c4a0e95d64d709407d2b60a8b69388c97ccbb2d2bdb8af88ce3203e75af188b01846778077e798da42f8cf91587096c90df2ac4d246, 0xa275ae75e1a71f72ec8346d5e26f3a0382c389752bf2858ee9335d2e680d3434f6967e84ab1583aea04a00a08ae5adf22a3c8e32e46e0dc119a66ff91a,
  0x1f6f21644cad3092c73b4f2d9bda140ee25d0832ee5928d4eaf4c1a380ccefe67302dc00b2819ae8e761e2f2971cb92dd16d73d4523ea518649238f96a6, 0x55725c5e492b771d1c83c409f49c6dc2f6cc57f847f83b44da2ce08d730d3e0ad3ea840ec982fc95e6e04356902759000963d2388da8ff7537addb06082, 0xcc46987c85a51280ec386370cfc0e65fa29398d966d22b54930e949bca392506d7d55b8e87ef7ae5714724328e36f86a12d027c9317a81dd38554675cbe,
  0x1ae1a5bf4442b8236ead137081342856398d77fa92bef0992046e7a66c8f9b76aa521dcb33ab7af9c4188ea402fb7a9487ec646c9a88eb15ecbbfb786b62, 0x31e7f45ae5880bd84c0b6fb08eb5b0b5c265ee8aea338a3b9c21774d3616036363cb2983227f5747f59bb76326f593706fc791be8a124440130b37b5d65e, 0x51c657bbb07f1c64051e869ff562a0cd9aa12cee6ad3b0bff63718da9c7546c64eefdadc5c40c5570d5e3200ab2ae1782ca469e3c312d3c5457ab1c21012,
  0x765a905d933140d09c7949923c79f5f1f997126264d040cd27ead6065b7a36b2eb0f298cd979a63d9baa19c0be18259164795f9a7a70da4a2aede927d62e, 0x976304eb6a8e1dee8d6dc5cd504b3cd335f0a01ac816363232216bec9f44695bd4210703a5afa668773013d189d5c4af65b6038881e13f1c2e5f80e20b32, 0xab32da04bd5f66df402cc288ab67ecdd3b7a5395993332b5398d2f73da47bad21a7fa2b4b4b3f5270226d1eff005cbde0aae5bcceeafdc801b2b76595b8e,
  0xab32da04bd5f66df402cc288ab67ecdd3b7a5395993332b5398d2f73da47bad21a7fa2b4b4b3f5270226d1eff005cbde0aae5bcceeafdc801b2b76595b8e, 0x976304eb6a8e1dee8d6dc5cd504b3cd335f0a01ac816363232216bec9f44695bd4210703a5afa668773013d189d5c4af65b6038881e13f1c2e5f80e20b32, 0x765a905d933140d09c7949923c79f5f1f997126264d040cd27ead6065b7a36b2eb0f298cd979a63d9baa19c0be18259164795f9a7a70da4a2aede927d62e,
  0x51c657bbb07f1c64051e869ff562a0cd9aa12cee6ad3b0bff63718da9c7546c64eefdadc5c40c5570d5e3200ab2ae1782ca469e3c312d3c5457ab1c21012, 0x31e7f45ae5880bd84c0b6fb08eb5b0b5c265ee8aea338a3b9c21774d3616036363cb2983227f5747f59bb76326f593706fc791be8a124440130b37b5d65e, 0x1ae1a5bf4442b8236ead137081342856398d77fa92bef0992046e7a66c8f9b76aa521dcb33ab7af9c4188ea402fb7a9487ec646c9a88eb15ecbbfb786b62,
  0xcc46987c85a51280ec386370cfc0e65fa29398d966d22b54930e949bca392506d7d55b8e87ef7ae5714724328e36f86a12d027c9317a81dd38554675cbe, 0x55725c5e492b771d1c83c409f49c6dc2f6cc57f847f83b44da2ce08d730d3e0ad3ea840ec982fc95e6e04356902759000963d2388da8ff7537addb06082, 0x1f6f21644cad3092c73b4f2d9bda140ee25d0832ee5928d4eaf4c1a380ccefe67302dc00b2819ae8e761e2f2971cb92dd16d73d4523ea518649238f96a6,
  0xa275ae75e1a71f72ec8346d5e26f3a0382c389752bf2858ee9335d2e680d3434f6967e84ab1583aea04a00a08ae5adf22a3c8e32e46e0dc119a66ff91a, 0x2dfdb5e811e79a3c4a0e95d64d709407d2b60a8b69388c97ccbb2d2bdb8af88ce3203e75af188b01846778077e798da42f8cf91587096c90df2ac4d246, 0xb62d50bcf7692d3bfba0923996340f70ccf48f84d643f549fff61a6366104b709d06c4cd49c89dad387328be00d05fa83d68b196a097621621291d2fa,
  0x2758d498d6625167a75134bfe1af9392cb8b324ef441ead31e9aab147c5cca3299512c0a7af7d1258bd80cc6606cf0ec9ed732c01ae6fc9a7cbd96496, 0x764c5932bfbc574a33397481965e0bb492a92cc33b0d5df7b60d3e4a6fa62121c0c485f270ee4fb12a527f4385a67cb50a1502bdd97b037aba8e3e2a, 0x1347ce43a81cb123d17739d669a925ce10678dab99025e142c35f7227a2889b8e277b7b364790d62aadaf570ed3ffaaf30544b7963c4e2f3301df8f6,
  0x2b755da89382a7c996482e544410acfd5e4cfdb1fe06cbba39fe381864c3463ac0b720a6e2414ec4d3a7430e4e9d43e329927349516e63ac32b434a, 0x5457fa55e20350df5c91ee81997a32c9a3e6419aaf27b1f25db1a3acfe893fe2ca84a77b67a13eb7b9b40488cc52ead0bf59698a9d9766e2f05da5, 0x8c56ed7afcce7122efe78bf76bd937b7ba1dd11e24a68f736d42580ce11c3f89e6446f2a7458dd2df298bdbf2faa826700ebb15fac38863effc7b,
  0xc73bedd6e53c857019863402485f791fdb2f9fae0c3b9b9aaa29a54a281cb3fc74dba6a961f9e2d46064feb0b0d00c57e5e034d24cf5c367b615, 0xf006f46332a6b8bb60e8a3d4cf5c0f8618bb01cf5ffe3385f10d9d9e7d7ddfe8b455e26f4af315552f1a3f87e34be190163db3767b714fad74b, 0xf3eb3a6d535415e4b32c9073c9e4d60e59c00efcfcfd86fefb178265dc39b685bb9103e6b30bb145efca57f17e112faa271254bc4364d3d23d,
  0xcfab4ae127c492a326d1acc2290b8ea204c3ac31db52d1fdeb5e6671fd2de96bb562936c8988ffc78d7c1a4eef1e0d0b8dd68025ae6f39463, 0x930090968045aba59e2348a3866405940098c67d8f8803f7e960d821b8343f7491168ebce50764e8e2fc82edf9fa23be545e7adbfc84ac4d, 0x55c6447d5839421c6009c352ab6d9e265af82df37170e7122bee64a6cd2a77f65bc96601e3f6e9dc704ee703f64fb31310a048e33451f93,
  0x28da9e4dfbf2a3d028e949b3d8439bf5247c280e5a08173279cfa5c36319844fbb04e1acaf12e80963384be35d952f115128ddcf912731, 0xfb5528519be0cab435b60a30bbf4700ba6a8b9a7c8853202c7aef0c03d25a0dd3734f3d7ac136f46feca59c2d0b6940133a9be72b96f, 0x4d0725e03f11d7732d0cbf55ae6472355ae0f88253af1f399b6ba94ad748cb03ed3e25f3e5f584c9caade1395b680f53a062cef2ca1,
  0x128b6563d1805983f83388da5c8940c02a62976052fab59fa415c65d1d56878ec9b58003ce35c5261c0f6ad9faa54a795f9b6a123f, 0x372cd5cef33084f72a7b95b3f818e156c2ce5085eb1966ac3b2873c60a19e1c2dcdc168182f3a4564a878d57b3ac51b660060a39, 0x7c54cc209eec505575e447c0c1ffeef28771d96c8e317c077797ba9e20b69fe2cc6c8c5eac2a5512e2c21a5ee3815a3c5adae7,
  0xcf5af5ad24819dc85a5aef3abc4a099f94f8716d85c198214a1c8e511e685cdb8fca9539bfea8fbebd915292bed5fe2b91c9, 0xf90eca2cf7b4ff2595a41801d58d1c1c87f5feaba40a48297b71f1399c0e9e5edd256ac6475074e690e83ac29484a4ff97, 0xd088ca8468fc2fe6460566a50e87d90947b7cd4ab2676f04b742edabbcaa6113fdec6d0a68ccf3b392e458e9096907eb,
  0x75045b1c188314ed01fd545e295791ab4b323873c74d38bda52c68d61d8d9b2313df4c7c806ff8d36929f41b69e9f5, 0x29f05dc343d0dd4d031c6d8596ee6d0eb9c784f2b02f1e76d7f55e20d2582f4c19503733336e92f769f4436410fb, 0x90b7f727794bc865d1566dc802d3e5a46434f97bb0d4039ec27b72650355e78df6628f1c4fdbdb60d1ea8f1a5,
  0x116d2e12c093e0611f0eace29346daf5b6f6b402890458d347c94814cf8f79f727faf86b31ea9e80f048ef3, 0x11093b0a13d20c908c1bd138d85cbb9eb949bbf521fc417d39c17ee9b5e366bf2bb24dd5e096bc10a26d, 0x77616b80454354869ae186bba4d62d4aa1be0f0cc98792a5908d884cd572592a34287bea9c7f8263,
  0x13d9a56eec98b93a3cb11c0d64ec09c288eb2d9c49d4627a0e96b9f896af99e092d98259e55bd, 0xffeec7d8282c77ce7790efe4838d95f2dfa22565de7cc98bd02d76bb0c5f1521bc086857, 0x2d71ae95630815527410431a838993fb4362180c3a1c0432a3c5db3c7e1626ec4609,
  0x11d4fde916a332494681621318c53df5423aefa2a71be8ed461c8bb88711ae7, 0x77d9d52a62cd8a65a807ce8bb076a75d1529a2dc4241e02b0042a739, 0xffffffff93e4ab75e987fd896025f0f14e0bcf0b04adf42f,
  0x11d500bfaf40a64044981798db5fb39f2c18db1, 0xffffffffffffffffffffff9f, 0x1]

private theorem eulerianCoefficients_eq : descentCoeffs 96 = eulerianCoefficients := by
  decide +kernel

private theorem upper : upperOK (descentCoeffs 96) first gaps = true := by
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

private theorem lower (i : Fin (lastRepresentative 97 - 2)) :
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

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 97) :
    StrictNegativeInterlacing (originalQuotient 97 k) (eulerian 96) 94 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N097
