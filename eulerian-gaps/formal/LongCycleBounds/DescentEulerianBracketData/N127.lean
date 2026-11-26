import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentPackedData.C127L127.N127

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N127

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L127.N127 LongCycleBounds.DescentNecklace.Packed.C127L127.N127.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L127.N127 LongCycleBounds.DescentNecklace.Packed.C127L127.N127.rows

private theorem actual : RepresentativeChecks 127 previousNodes rows :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L127.N127 LongCycleBounds.DescentNecklace.Packed.C127L127.N127.dataChecks

private def first : LongCycleFinite.Dyadic := ⟨-85070591730234615865843651857942052864, 0⟩

private def gaps : List Window := [
  ⟨⟨-85067833322528519238665995031767154688, 0⟩, ⟨-17119983623486203494400, 0⟩⟩,
  ⟨⟨-14758800382051380887552, 0⟩, ⟨-5849401859768320, 0⟩⟩,
  ⟨⟨-5251147275173888, 0⟩, ⟨-1807484977152, 0⟩⟩,
  ⟨⟨-1560079761408, 0⟩, ⟨-9307652096, 0⟩⟩,
  ⟨⟨-9227993088, 0⟩, ⟨-258789888, 0⟩⟩,
  ⟨⟨-258332160, 0⟩, ⟨-18603264, 0⟩⟩,
  ⟨⟨-18590656, 0⟩, ⟨-2471560, 0⟩⟩,
  ⟨⟨-2470696, 0⟩, ⟨-499557, 0⟩⟩,
  ⟨⟨-499450, 0⟩, ⟨-272475, 1⟩⟩,
  ⟨⟨-136217, 0⟩, ⟨-46350, 0⟩⟩,
  ⟨⟨-46345, 0⟩, ⟨-298555, 4⟩⟩,
  ⟨⟨-298529, 4⟩, ⟨-273987, 5⟩⟩,
  ⟨⟨-17123, 1⟩, ⟨-139453, 5⟩⟩,
  ⟨⟨-139445, 5⟩, ⟨-308685, 7⟩⟩,
  ⟨⟨-154335, 6⟩, ⟨-91457, 6⟩⟩,
  ⟨⟨-365813, 8⟩, ⟨-458803, 9⟩⟩,
  ⟨⟨-458787, 9⟩, ⟨-301691, 9⟩⟩,
  ⟨⟨-301681, 9⟩, ⟨-412979, 10⟩⟩,
  ⟨⟨-412967, 10⟩, ⟨-36563, 7⟩⟩,
  ⟨⟨-18281, 6⟩, ⟨-426715, 11⟩⟩,
  ⟨⟨-26669, 7⟩, ⟨-159641, 10⟩⟩,
  ⟨⟨-159637, 10⟩, ⟨-61063, 9⟩⟩,
  ⟨⟨-244247, 11⟩, ⟨-381049, 12⟩⟩,
  ⟨⟨-190521, 11⟩, ⟨-302365, 12⟩⟩,
  ⟨⟨-302359, 12⟩, ⟨-243591, 12⟩⟩,
  ⟨⟨-243587, 12⟩, ⟨-198907, 12⟩⟩,
  ⟨⟨-397807, 13⟩, ⟨-164383, 12⟩⟩,
  ⟨⟨-328761, 13⟩, ⟨-137323, 12⟩⟩,
  ⟨⟨-137321, 12⟩, ⟨-231669, 13⟩⟩,
  ⟨⟨-115833, 12⟩, ⟨-197129, 13⟩⟩,
  ⟨⟨-394253, 14⟩, ⟨-42267, 11⟩⟩,
  ⟨⟨-338131, 14⟩, ⟨-292083, 14⟩⟩,
  ⟨⟨-292079, 14⟩, ⟨-507895, 15⟩⟩,
  ⟨⟨-507889, 15⟩, ⟨-55525, 12⟩⟩,
  ⟨⟨-444195, 15⟩, ⟨-390593, 15⟩⟩,
  ⟨⟨-390589, 15⟩, ⟨-345151, 15⟩⟩,
  ⟨⟨-86287, 13⟩, ⟨-76593, 13⟩⟩,
  ⟨⟨-4787, 9⟩, ⟨-136537, 14⟩⟩,
  ⟨⟨-273071, 15⟩, ⟨-122159, 14⟩⟩,
  ⟨⟨-61079, 13⟩, ⟨-219347, 15⟩⟩,
  ⟨⟨-219345, 15⟩, ⟨-395115, 16⟩⟩,
  ⟨⟨-49389, 13⟩, ⟨-44613, 13⟩⟩,
  ⟨⟨-89225, 14⟩, ⟨-80813, 14⟩⟩,
  ⟨⟨-323249, 16⟩, ⟨-293495, 16⟩⟩,
  ⟨⟨-73373, 14⟩, ⟨-267079, 16⟩⟩,
  ⟨⟨-66769, 14⟩, ⟨-487085, 17⟩⟩,
  ⟨⟨-487081, 17⟩, ⟨-444999, 17⟩⟩,
  ⟨⟨-444995, 17⟩, ⟨-203625, 16⟩⟩,
  ⟨⟨-407247, 17⟩, ⟨-186645, 16⟩⟩,
  ⟨⟨-373287, 17⟩, ⟨-342647, 17⟩⟩,
  ⟨⟨-342645, 17⟩, ⟨-157463, 16⟩⟩,
  ⟨⟨-78731, 15⟩, ⟨-36223, 14⟩⟩,
  ⟨⟨-289781, 17⟩, ⟨-266923, 17⟩⟩,
  ⟨⟨-33365, 14⟩, ⟨-246091, 17⟩⟩,
  ⟨⟨-492179, 18⟩, ⟨-454135, 18⟩⟩,
  ⟨⟨-113533, 16⟩, ⟨-419319, 18⟩⟩,
  ⟨⟨-104829, 16⟩, ⟨-387401, 18⟩⟩,
  ⟨⟨-193699, 17⟩, ⟨-358085, 18⟩⟩,
  ⟨⟨-179041, 17⟩, ⟨-82779, 16⟩⟩,
  ⟨⟨-331113, 18⟩, ⟨-153133, 17⟩⟩,
  ⟨⟨-306263, 18⟩, ⟨-283335, 18⟩⟩,
  ⟨⟨-283333, 18⟩, ⟨-262145, 18⟩⟩,
  ⟨⟨-262143, 18⟩, ⟨-242541, 18⟩⟩,
  ⟨⟨-242539, 18⟩, ⟨-224381, 18⟩⟩,
  ⟨⟨-448759, 19⟩, ⟨-207541, 18⟩⟩,
  ⟨⟨-415079, 19⟩, ⟨-383819, 19⟩⟩,
  ⟨⟨-47977, 16⟩, ⟨-177387, 18⟩⟩,
  ⟨⟨-88693, 17⟩, ⟨-327769, 19⟩⟩,
  ⟨⟨-327767, 19⟩, ⟨-302641, 19⟩⟩,
  ⟨⟨-151319, 18⟩, ⟨-139623, 18⟩⟩,
  ⟨⟨-279243, 19⟩, ⟨-514905, 20⟩⟩,
  ⟨⟨-257451, 19⟩, ⟨-237143, 19⟩⟩,
  ⟨⟨-237141, 19⟩, ⟨-436419, 20⟩⟩,
  ⟨⟨-6819, 14⟩, ⟨-401111, 20⟩⟩,
  ⟨⟨-100277, 18⟩, ⟨-184093, 19⟩⟩,
  ⟨⟨-368183, 20⟩, ⟨-84371, 18⟩⟩,
  ⟨⟨-337481, 20⟩, ⟨-154427, 19⟩⟩,
  ⟨⟨-77213, 18⟩, ⟨-141085, 19⟩⟩,
  ⟨⟨-282167, 20⟩, ⟨-257303, 20⟩⟩,
  ⟨⟨-257301, 20⟩, ⟨-7317, 15⟩⟩,
  ⟨⟨-117071, 19⟩, ⟨-212589, 20⟩⟩,
  ⟨⟨-212587, 20⟩, ⟨-96273, 19⟩⟩,
  ⟨⟨-6017, 15⟩, ⟨-347849, 21⟩⟩,
  ⟨⟨-173923, 20⟩, ⟨-313293, 21⟩⟩,
  ⟨⟨-156645, 20⟩, ⟨-281275, 21⟩⟩,
  ⟨⟨-35159, 18⟩, ⟨-125827, 20⟩⟩,
  ⟨⟨-503303, 22⟩, ⟨-448605, 22⟩⟩,
  ⟨⟨-448601, 22⟩, ⟨-99551, 20⟩⟩,
  ⟨⟨-49775, 19⟩, ⟨-351877, 22⟩⟩,
  ⟨⟨-351873, 22⟩, ⟨-77353, 20⟩⟩,
  ⟨⟨-309409, 22⟩, ⟨-16913, 18⟩⟩,
  ⟨⟨-270605, 22⟩, ⟨-235277, 22⟩⟩,
  ⟨⟨-117637, 21⟩, ⟨-406465, 23⟩⟩,
  ⟨⟨-406461, 23⟩, ⟨-5447, 17⟩⟩,
  ⟨⟨-87151, 21⟩, ⟨-296633, 23⟩⟩,
  ⟨⟨-296629, 23⟩, ⟨-125107, 22⟩⟩,
  ⟨⟨-250211, 23⟩, ⟨-209025, 23⟩⟩,
  ⟨⟨-104511, 22⟩, ⟨-345491, 24⟩⟩,
  ⟨⟨-172743, 23⟩, ⟨-141057, 23⟩⟩,
  ⟨⟨-141055, 23⟩, ⟨-56819, 22⟩⟩,
  ⟨⟨-454545, 25⟩, ⟨-180347, 24⟩⟩,
  ⟨⟨-22543, 21⟩, ⟨-281353, 25⟩⟩,
  ⟨⟨-281347, 25⟩, ⟨-430473, 26⟩⟩,
  ⟨⟨-430465, 26⟩, ⟨-20131, 22⟩⟩,
  ⟨⟨-161045, 25⟩, ⟨-234939, 26⟩⟩,
  ⟨⟨-117467, 25⟩, ⟨-166403, 26⟩⟩,
  ⟨⟨-166399, 26⟩, ⟨-227789, 27⟩⟩,
  ⟨⟨-455567, 28⟩, ⟨-74891, 26⟩⟩,
  ⟨⟨-74889, 26⟩, ⟨-375701, 29⟩⟩,
  ⟨⟨-187845, 28⟩, ⟨-445245, 30⟩⟩,
  ⟨⟨-445231, 30⟩, ⟨-246395, 30⟩⟩,
  ⟨⟨-246387, 30⟩, ⟨-501645, 32⟩⟩,
  ⟨⟨-250813, 31⟩, ⟨-460363, 33⟩⟩,
  ⟨⟨-57543, 30⟩, ⟨-92669, 32⟩⟩,
  ⟨⟨-370659, 34⟩, ⟨-252249, 35⟩⟩,
  ⟨⟨-504473, 36⟩, ⟨-17197, 33⟩⟩,
  ⟨⟨-4299, 31⟩, ⟨-444883, 40⟩⟩,
  ⟨⟨-55607, 37⟩, ⟨-118239, 41⟩⟩,
  ⟨⟨-118231, 41⟩, ⟨-272393, 46⟩⟩,
  ⟨⟨-272373, 46⟩, ⟨-486633, 52⟩⟩,
  ⟨⟨-121649, 50⟩, ⟨-356917, 59⟩⟩,
  ⟨⟨-44611, 56⟩, ⟨-106889, 69⟩⟩,
  ⟨⟨-835, 62⟩, ⟨-321569, 92⟩⟩,
  ⟨⟨-160769, 91⟩, ⟨-262165, 144⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private def eulerianCoefficients : List ℤ := [
  0x1, 0x3fffffffffffffffffffffffffffff81, 0xd0b2c448fbd1250517595f2c63386319440e403b2ad680d77a,
  0xfffffffffff9877509fcb133ea2717aa9c8fac706d6773cee22a5bf961f857a, 0x17a2ecc40cb03f7ff6ca362fcaa128194e2ddbd7d157adae4ee12f43e28e96a25f8a59a943, 0x342cb1068520d3fd0656d74faa85b5472df502ecdea26b0c9e4444334eb1c553126bacbb499bd2b4c3,
  0x34f4b5d258e39efc2ffb565b55e68616413ba4c67bea59df5db226686ab9afac33f51d6aa508ad6c879ac8d74, 0x3fffe5ba99651d37c34fdcfadcd81a850e76797236b0b4406af6cead3bf1599605d0888c36c0a4e360c312f6f298574, 0xaa20ffcc8ca325f0932d00e7775aac87dacff5e58bcf1e97f6cb80a4598e05057f40ab95027190793dfcfaf31d40966585f5,
  0x5e866ca2741b89624adb49c00b0f122348b4640d3ece9eb3e47d7d65188bd63482f1280cb8821115787ad2e074c7874ccf79c1175, 0xecc1fe4050abffdb679a72b719879cd026b69bc99c41f7f718cdc561aad3b3688a54ec0a1a5ccc494bfa59f94d5a938e76811e360994e, 0xd03d4452753b06b36b44bce4f2b5b151df77bc3eb4876d23e4e511e9cd1120d8c5b5996d1f95c750f0cd5232cfe38d355bd77e3825d3ed74e,
  0x4bfdac9d39c36f85f5c2bdddb74eb69177dac8c25df6cab1b25ccd1d01d67c1d7a1baed61a082b2e8b4634872d80139b456bb98621d682491c497, 0xd17612af4cdc927fe8d6b4ba2ffa09f8d311074116c8821ff49d0c3ececdac1ae90b5de6267b7886dbe2705c5cd8625d6105c15ddcaf9f74f3363417, 0x12dc6123514144b31530374b8a85120f7e2ac42c67582ad0e726aad6986228abd2cb9b906759d1a64e5e43af095c7467878f8a4fc6a58fbabad18a50a2a8,
  0xf68a980daf15ab04c4339db1033a38b1a47760cd9f6b7095417aadf9b55c108cd099ec8a4fb9743fa92e2c9ac9845f45af9e0535a2214c1ac9c390e57102a8, 0x7a06203571e5ff22b4a725d3286c11fb805facc66f86698b0e9ddcaaf0f4369c840b36cfcb457f7addbd00d37465ff8b55974f703a7fac5142d2b10f3e319e371, 0x26a1357f179fb18f8700d4adf98d885bd827d998fa2d3ec232109054694b7ae947d6fef02a4e13891af33a17d0e71ff865992502cfbdb87897147510357101f386f1,
  0x82eb13e1d681cc9e663ebb900d6af7fa42ca375f69c176185911e7dfe9afaee89dc47aa511e7dda7b8a3274975b8250a91338ef947afab752a818d09508325ef8c4e32, 0x134485ab3fdd1223e847fd7e696e5e45b7f90090e1c0173acdf70f6a266ac9470415fe7a485b8ceaa97a1e7841f47a55ca154e51b548f75563fdd024641b35ec2e315fc32, 0x208bd31dac8c454e0d5b3146f2cbe809256bde29e9ae8f97c166857c69935d495acdfd6b93b562933de4a059299c88077c3bb999fdc875dde867e59929aee4ba49e67ab0c03,
  0x2885cdbb4dcfc28da74b3546c2ea5ce80c65b0dd6ac438af1406030649fc2efbc64848edc8a1b1ed62dd7265c4417237f3a0c6724c88aa19258da453cfb89df7283d1b996cb83, 0x26115dec7d5f81d1b2e524eecc8ac2003b6c952c3806e43f89e3591cb7a4f91fc3c29d8b96028afaabcac1ab52ed1941f5d5893bd6b3f3ecda4baa3d6d1c973ad2353c3fdcf043c, 0x1b88491f2c271f3a5eb4fc377b9d65dbad1c46f5cc636ae1549c9cdd9e97393291ffaf1e947bf0a8c3ac53acf52dbeda878c20b2924836a358bba6eac1dee2e3844ebd8f5d221fc3c,
  0xf9a18f5a0c027c7985505ff0063f2409f60517c3c873060a8dbab137b2202e4bd606b9c54bb1a9a67e780c8657e2b5f9c92979b4865ca0982042a561d6147fe116795692f5cf2b1f65, 0x708d9639be75333b96b2bcc896a6af054bec599c5ad34cf9d553e9ee3ae00a35d8a42bbf9b2fd55e5f6e20868e311e24d6b0a5659b9adc7d6c047f439e60779504bc2832f7fffbe99ee5, 0x28ed6047c287b5151af213a7be6bc69aade13175b283d2b94d858ec7d96136a667f48b5e30f9f004e7861361de8c6c9dc37f90f0b238bed7d3f088f7ac77ac18a920083db39946997a27e6,
  0xc258ecacf6275c2720c3cbb2dec03cee10c6841f1ab97b14da181074cf54d3af617c81fb2395a791bdd8599190e57ddb79aa21f86d4375ac483559ff39fe753d0202d9ceddcd373084d05e6, 0x2f94a9a3a3a66d358441b34f19319dfd0b3116a8fff2d4a37b80f9e2986f08ad51154a721f86feca05d4c4702ae9d9812b4f215e8fe1b913d139b462337f453626d043b1aad62c4ee62c4d017, 0x9b367c748f109b9bdfb38c7db7fb046d8f081c4e622b32ff1615d28296e27c826de86d544ebe7886dc4cccc1d742c24eb4ac35656a88e8e6c9f908d2372b73449c2c6eb937541490cf394a8397,
  0x1a93e524c9f181fe864ac5adaf24857e6d69896947800053691a5679700abbab8a800b0afc1ba90f81b9029b624b648a8dae4e03ff8d0df7d720b5561197ca2ae4b1aa3a071633a2543bfaf30d10, 0x3da0010f53bb77e9ea4e619e900973cf3668ae01806684e5aa737012b714f090a206f1f026c3eb0a34be0e409cf5a15773517e71237478f57bb1fee5e58152aff47bc27356688f412dd2511398d10, 0x79c369a34c435e1de66d373b176a4ecea1bbeadcabb8fd723331727104097f54d70c3fa760e090eb9ed6eeb445569eca69ca7e1333809903658b4a478eddd3852c71a9e13c1c2ecb94a3f233362b25,
  0xce4d090fb2b29b01f042241cbff15aa4a8f63c01157d3e7fc3f43f0153187051675fed62631a0fed80033d1822612e2c73a2767c850b81e3c5c6ead6443d427b85ac948c72c1a29989e517e64d5b0a5, 0x12d6a24da8696b69f43c1be754859bb9f384bc7921339934f1c65040bd7da905f0412e1b937d42d0aebdcbf968893316a2e4d8771d9b604241f4e56b6cb31698d209eb0d581d199ce61fb91db5cd1e192, 0x17db663e1d378b3a5ea6f45caf6adb46c2a0ae0bbceefa6b101bb32a8ff046176088b08d8e6c762a9f80822152c7c64253fa25aa13e49a9731eda3fb403fc79e2e151001cc7f391172768716afe1628792,
  0x1a4f7d4bec146c17715d92ab235df2d738fcabbaebefac61e9ac387cee1f85291f0f937cfeda9ab38a903f612c30f170ecee2c2868df995b6fe843c38d8b098ac841e1dd9961806982651d7819ad4fa870f, 0x196078a9ea34f3894e7f03a13ce365874baa52febb7cf4e3712fa7877b2c8aa5986417ec0a576ca68a867e582f3d14b8c77f83b1f265adb75f0ffa2ae2fdbf2f89c9bc7124f1f32df0608dd0c4c8b2d1e88f, 0x157d730076848595e8262910e69cdb952176166c7c676874f71c8aafa0249e6c1db7663a993636a8d71fdfeec79dd6e57fe08ad9699ab0580c7a7d5a62223c26ac4ea6854aef9f88fed0afaa07a19c4353e94,
  0x10091166e1a14c251cd13f279f0949b2061fe7ad6d139ef8ce7e40cdb740763c38c572885cfc2011c83f4388edfe02f8ce7171cdbd67409971020fcedd2553a450f587ddf66731e8e48d998b97d56e8928d694, 0xa93e2815050b630934163a632adfbbce02696ee4e023b7db2b1279e97a4c15d96ad3ccf5b89d8e93449cc1176c908a5da0109740efa3f0e22cbff1931caba7c706dd8e2d83a525cb3e6d4ab77620e59fafc669, 0x62fd7a45d3be003e66e794f86520b9d7453970c3d8547b991fd61154ff8f0492cd0248d000bf54afcb005b7c9986c615bd2ebab943cc338ae46250c522174aa390473e69ae045c258a0aadfbbc10ca72701e7e9,
  0x337b0b167c016724f7578a2c796a4c34e401f96b619f3923454180c459c6c4d83225acb8acf5f81fa6e08d188985df9d6c571b18801ec7723006b3086b467e07c090b594d95e4e3b377a6efa3049e49ff07feb76, 0x17dd824dcc5b569f86ea3f837760f59d54e7975fc6c653dfd9fabc77a08a00b6faa578e47b0adc8293e42ededc2688037437e2f74c67f8d649ec86d4a6d2e8c0b131a846f46f263c25767fcb0bab84fb47b97a176, 0x9e284dd433520c760407058e4ce85a22277cb361e1c1b311fc4adc2f0583a5def78059610ab2c2dad9b58db0b5e9e4550bec7d47e52e61f4bb10bc431c78f80bdb28d710c9a7e5a5c1dabfbc8f62dcc0c955cd1b3,
  0x3aa78db562d93a54d56df210d27c675fc57faea4bde912c7a524364f477ae550fd9ca7877340f51a22d9abcffcf22cb59da960150784ef4e4a40db3ef8af39b1f2ed2394a331d0df46606caa72254d833f8bd18733, 0x1383e327683e6d73614a1eb18ae6637664f8a89cdd37c535e18ab4da60dd8802214077b0476a6b21432e03b28c0a498497e42d687953e9d4af79d09e83c76e8a22e94ffb206d6bb4a874d2d42e9b3066221f4dc1bd8, 0x5d5e82235d2156cd59412b57b61ac5cbcf45337c7eff565af6d39a6587fa4012ecd9bc265eefb22fe5dd614c89f684c3c4a774161bfcb662a66819c5bfd7567c6d7156963298f8931a11fdc36bdedb84896430dfbd8,
  0x1922659a3dd589adabd907831deeb7370fa2b8814ebadfb17fecaaba33c7527991199308541a053b1f71606e9e4d90a74832d86dcd93feb870ffdb4dab1324c9638e6d73495c57807c05a16510ab310a9bd1f6503a05, 0x619a1052a70982b03abc7cb139f39a478274078994afe5ce586f0eb34ff8bc626f4a1566b875661e738060293ef2a21ff05867bfda1867a5c5fb11892cc6f7b64cd147b284dde711b70e57b3671d4988a25225cedb85, 0x1562cafcaf272d9e8ec00231946d14c9ebfd402efe8626e88c87d7858c3735e0d84d8846c869964f8691738affe5e11039a169472c10144b9ea5326876704d0005ca65897520ed751cee4753ed13d5aa37bcbdb03c78a,
  0x43c5e69021b90d6b10b26da1a60292ff8386606dc5797d7a8f71830b89e65d32d85bbb1711f637882df593aeec88efb0176d606c7e999c135cd8a60e8b1f1190e817f3bfe8a253bc07ce19f92d7f369b0e24677928d8a, 0xc25cf497989ba33296d1986a358c70ecb8717644b13ba95e0e3c04ea128ce424ae5202b4e442f27d39d8948899897a296274913bbec5c3297f4d3c3ed2b3a86db0025815134385401859f23b5ae7100dc4b45d187b2df, 0x1f8efe535d895663ae29a2bde392c88750849af09598151ee00ff1de68643df42802c4aa9de7fd14aff114359d9fc32a67cfce00b68146a653ac2bfe833f647f383299bc75b5d58f6a5aa0bd981c84951c315d2736c05f,
  0x4a560bda05a704ff252d2a558b8a17a87dc7dbe8b9c6c93bf633fe439d2e248843048d40d5b20601a219f6f804f2e1ea11c6aef7d082b49e1cca807303bf8cfcdbe28e05a961125f9f84474e50ebc3755c07111cd2dfbc, 0x9ee32edfb72f0bf2db300ed33e6f560ff0057032285a0b81b283f2065b29dba4b8d7ab3ae9c780fc43f81941689b3a44b5ac79216fd7b7aecbfeb9bea2074f271c400575b1b55aebbff47b8f0ee50ecb5da287d9ae77bc, 0x134623adf385f2bc5392e542b296756c50bbed94c9fafebbeb04cdd83aa5614fec904b432602cb017db67a42d584b9ac3df1b7b995a1c7b3398fd2008dd2905c7edc3c460d0b14d1067a80bc06461904b8e09d34eb1ab09,
  0x21fd6769f638fe69db62346a835a5aad56b4964179d7e8589df079a9081a1be85b1dd8e18f56de71887aa0c8e2fa85e25207532a7655cf0eca1c99d5cae99e5a09c875848eeb4e1152e4a866986f7af9649762f2ff5b889, 0x367dc5c6d849e393c2c8dd000a4c856c63c699b2273d009bea6ab808d3a6c2cc5a32ef31821cffbe7808c7b4aadb1f4fa559fcd9237ebcaf42db4a46906ba3529a5b619f05404cd614e510ae30181f2ddbe62500ababc8e, 0x4f730193b5b942b8a7fb1471e63835c3a678bc4b92652b8917a654eef3f5ff4841d46c756262e1373d48afcd8a5be1ba6a7366aa1b4b240570fcbb0fc6345bb896a0049eb5f635e5cea81d4d755fa3df598ac5e16b9b28e,
  0x6962e3339d34500f708559f8545e784954d3bbb4fd446ff871ba7453fb3ca2df5f731d5fffa90480e3b211e63f441f5a1eb3e864cf57b5e5b77624988119ea8574c177a5c07c6f207eacd9e1a1635f2e16d44e973b04703, 0x7f35a41fa2c180a38125171ffe2ac76a78fd64cd5eae3832d26cb4e66cc89806a3b9a41f4edbc41a174556097f0d6250a9b4ee3005cdf77f973c13a111a43b6022673ced0e1cde5daca15a6d5a9d950efe6cb83b7a93883, 0x8bc17107a9d86dc57eecd329e5c7f6d149c8832d63b3a776b743390827ca9ecc1053d595d58861d10b90a202fcd204f520ed932d587650f3e03a4f1ad62677041219e5a6475114ee03a57b99847bd5b28e8b2f00f8128e0,
  0x8bc17107a9d86dc57eecd329e5c7f6d149c8832d63b3a776b743390827ca9ecc1053d595d58861d10b90a202fcd204f520ed932d587650f3e03a4f1ad62677041219e5a6475114ee03a57b99847bd5b28e8b2f00f8128e0, 0x7f35a41fa2c180a38125171ffe2ac76a78fd64cd5eae3832d26cb4e66cc89806a3b9a41f4edbc41a174556097f0d6250a9b4ee3005cdf77f973c13a111a43b6022673ced0e1cde5daca15a6d5a9d950efe6cb83b7a93883, 0x6962e3339d34500f708559f8545e784954d3bbb4fd446ff871ba7453fb3ca2df5f731d5fffa90480e3b211e63f441f5a1eb3e864cf57b5e5b77624988119ea8574c177a5c07c6f207eacd9e1a1635f2e16d44e973b04703,
  0x4f730193b5b942b8a7fb1471e63835c3a678bc4b92652b8917a654eef3f5ff4841d46c756262e1373d48afcd8a5be1ba6a7366aa1b4b240570fcbb0fc6345bb896a0049eb5f635e5cea81d4d755fa3df598ac5e16b9b28e, 0x367dc5c6d849e393c2c8dd000a4c856c63c699b2273d009bea6ab808d3a6c2cc5a32ef31821cffbe7808c7b4aadb1f4fa559fcd9237ebcaf42db4a46906ba3529a5b619f05404cd614e510ae30181f2ddbe62500ababc8e, 0x21fd6769f638fe69db62346a835a5aad56b4964179d7e8589df079a9081a1be85b1dd8e18f56de71887aa0c8e2fa85e25207532a7655cf0eca1c99d5cae99e5a09c875848eeb4e1152e4a866986f7af9649762f2ff5b889,
  0x134623adf385f2bc5392e542b296756c50bbed94c9fafebbeb04cdd83aa5614fec904b432602cb017db67a42d584b9ac3df1b7b995a1c7b3398fd2008dd2905c7edc3c460d0b14d1067a80bc06461904b8e09d34eb1ab09, 0x9ee32edfb72f0bf2db300ed33e6f560ff0057032285a0b81b283f2065b29dba4b8d7ab3ae9c780fc43f81941689b3a44b5ac79216fd7b7aecbfeb9bea2074f271c400575b1b55aebbff47b8f0ee50ecb5da287d9ae77bc, 0x4a560bda05a704ff252d2a558b8a17a87dc7dbe8b9c6c93bf633fe439d2e248843048d40d5b20601a219f6f804f2e1ea11c6aef7d082b49e1cca807303bf8cfcdbe28e05a961125f9f84474e50ebc3755c07111cd2dfbc,
  0x1f8efe535d895663ae29a2bde392c88750849af09598151ee00ff1de68643df42802c4aa9de7fd14aff114359d9fc32a67cfce00b68146a653ac2bfe833f647f383299bc75b5d58f6a5aa0bd981c84951c315d2736c05f, 0xc25cf497989ba33296d1986a358c70ecb8717644b13ba95e0e3c04ea128ce424ae5202b4e442f27d39d8948899897a296274913bbec5c3297f4d3c3ed2b3a86db0025815134385401859f23b5ae7100dc4b45d187b2df, 0x43c5e69021b90d6b10b26da1a60292ff8386606dc5797d7a8f71830b89e65d32d85bbb1711f637882df593aeec88efb0176d606c7e999c135cd8a60e8b1f1190e817f3bfe8a253bc07ce19f92d7f369b0e24677928d8a,
  0x1562cafcaf272d9e8ec00231946d14c9ebfd402efe8626e88c87d7858c3735e0d84d8846c869964f8691738affe5e11039a169472c10144b9ea5326876704d0005ca65897520ed751cee4753ed13d5aa37bcbdb03c78a, 0x619a1052a70982b03abc7cb139f39a478274078994afe5ce586f0eb34ff8bc626f4a1566b875661e738060293ef2a21ff05867bfda1867a5c5fb11892cc6f7b64cd147b284dde711b70e57b3671d4988a25225cedb85, 0x1922659a3dd589adabd907831deeb7370fa2b8814ebadfb17fecaaba33c7527991199308541a053b1f71606e9e4d90a74832d86dcd93feb870ffdb4dab1324c9638e6d73495c57807c05a16510ab310a9bd1f6503a05,
  0x5d5e82235d2156cd59412b57b61ac5cbcf45337c7eff565af6d39a6587fa4012ecd9bc265eefb22fe5dd614c89f684c3c4a774161bfcb662a66819c5bfd7567c6d7156963298f8931a11fdc36bdedb84896430dfbd8, 0x1383e327683e6d73614a1eb18ae6637664f8a89cdd37c535e18ab4da60dd8802214077b0476a6b21432e03b28c0a498497e42d687953e9d4af79d09e83c76e8a22e94ffb206d6bb4a874d2d42e9b3066221f4dc1bd8, 0x3aa78db562d93a54d56df210d27c675fc57faea4bde912c7a524364f477ae550fd9ca7877340f51a22d9abcffcf22cb59da960150784ef4e4a40db3ef8af39b1f2ed2394a331d0df46606caa72254d833f8bd18733,
  0x9e284dd433520c760407058e4ce85a22277cb361e1c1b311fc4adc2f0583a5def78059610ab2c2dad9b58db0b5e9e4550bec7d47e52e61f4bb10bc431c78f80bdb28d710c9a7e5a5c1dabfbc8f62dcc0c955cd1b3, 0x17dd824dcc5b569f86ea3f837760f59d54e7975fc6c653dfd9fabc77a08a00b6faa578e47b0adc8293e42ededc2688037437e2f74c67f8d649ec86d4a6d2e8c0b131a846f46f263c25767fcb0bab84fb47b97a176, 0x337b0b167c016724f7578a2c796a4c34e401f96b619f3923454180c459c6c4d83225acb8acf5f81fa6e08d188985df9d6c571b18801ec7723006b3086b467e07c090b594d95e4e3b377a6efa3049e49ff07feb76,
  0x62fd7a45d3be003e66e794f86520b9d7453970c3d8547b991fd61154ff8f0492cd0248d000bf54afcb005b7c9986c615bd2ebab943cc338ae46250c522174aa390473e69ae045c258a0aadfbbc10ca72701e7e9, 0xa93e2815050b630934163a632adfbbce02696ee4e023b7db2b1279e97a4c15d96ad3ccf5b89d8e93449cc1176c908a5da0109740efa3f0e22cbff1931caba7c706dd8e2d83a525cb3e6d4ab77620e59fafc669, 0x10091166e1a14c251cd13f279f0949b2061fe7ad6d139ef8ce7e40cdb740763c38c572885cfc2011c83f4388edfe02f8ce7171cdbd67409971020fcedd2553a450f587ddf66731e8e48d998b97d56e8928d694,
  0x157d730076848595e8262910e69cdb952176166c7c676874f71c8aafa0249e6c1db7663a993636a8d71fdfeec79dd6e57fe08ad9699ab0580c7a7d5a62223c26ac4ea6854aef9f88fed0afaa07a19c4353e94, 0x196078a9ea34f3894e7f03a13ce365874baa52febb7cf4e3712fa7877b2c8aa5986417ec0a576ca68a867e582f3d14b8c77f83b1f265adb75f0ffa2ae2fdbf2f89c9bc7124f1f32df0608dd0c4c8b2d1e88f, 0x1a4f7d4bec146c17715d92ab235df2d738fcabbaebefac61e9ac387cee1f85291f0f937cfeda9ab38a903f612c30f170ecee2c2868df995b6fe843c38d8b098ac841e1dd9961806982651d7819ad4fa870f,
  0x17db663e1d378b3a5ea6f45caf6adb46c2a0ae0bbceefa6b101bb32a8ff046176088b08d8e6c762a9f80822152c7c64253fa25aa13e49a9731eda3fb403fc79e2e151001cc7f391172768716afe1628792, 0x12d6a24da8696b69f43c1be754859bb9f384bc7921339934f1c65040bd7da905f0412e1b937d42d0aebdcbf968893316a2e4d8771d9b604241f4e56b6cb31698d209eb0d581d199ce61fb91db5cd1e192, 0xce4d090fb2b29b01f042241cbff15aa4a8f63c01157d3e7fc3f43f0153187051675fed62631a0fed80033d1822612e2c73a2767c850b81e3c5c6ead6443d427b85ac948c72c1a29989e517e64d5b0a5,
  0x79c369a34c435e1de66d373b176a4ecea1bbeadcabb8fd723331727104097f54d70c3fa760e090eb9ed6eeb445569eca69ca7e1333809903658b4a478eddd3852c71a9e13c1c2ecb94a3f233362b25, 0x3da0010f53bb77e9ea4e619e900973cf3668ae01806684e5aa737012b714f090a206f1f026c3eb0a34be0e409cf5a15773517e71237478f57bb1fee5e58152aff47bc27356688f412dd2511398d10, 0x1a93e524c9f181fe864ac5adaf24857e6d69896947800053691a5679700abbab8a800b0afc1ba90f81b9029b624b648a8dae4e03ff8d0df7d720b5561197ca2ae4b1aa3a071633a2543bfaf30d10,
  0x9b367c748f109b9bdfb38c7db7fb046d8f081c4e622b32ff1615d28296e27c826de86d544ebe7886dc4cccc1d742c24eb4ac35656a88e8e6c9f908d2372b73449c2c6eb937541490cf394a8397, 0x2f94a9a3a3a66d358441b34f19319dfd0b3116a8fff2d4a37b80f9e2986f08ad51154a721f86feca05d4c4702ae9d9812b4f215e8fe1b913d139b462337f453626d043b1aad62c4ee62c4d017, 0xc258ecacf6275c2720c3cbb2dec03cee10c6841f1ab97b14da181074cf54d3af617c81fb2395a791bdd8599190e57ddb79aa21f86d4375ac483559ff39fe753d0202d9ceddcd373084d05e6,
  0x28ed6047c287b5151af213a7be6bc69aade13175b283d2b94d858ec7d96136a667f48b5e30f9f004e7861361de8c6c9dc37f90f0b238bed7d3f088f7ac77ac18a920083db39946997a27e6, 0x708d9639be75333b96b2bcc896a6af054bec599c5ad34cf9d553e9ee3ae00a35d8a42bbf9b2fd55e5f6e20868e311e24d6b0a5659b9adc7d6c047f439e60779504bc2832f7fffbe99ee5, 0xf9a18f5a0c027c7985505ff0063f2409f60517c3c873060a8dbab137b2202e4bd606b9c54bb1a9a67e780c8657e2b5f9c92979b4865ca0982042a561d6147fe116795692f5cf2b1f65,
  0x1b88491f2c271f3a5eb4fc377b9d65dbad1c46f5cc636ae1549c9cdd9e97393291ffaf1e947bf0a8c3ac53acf52dbeda878c20b2924836a358bba6eac1dee2e3844ebd8f5d221fc3c, 0x26115dec7d5f81d1b2e524eecc8ac2003b6c952c3806e43f89e3591cb7a4f91fc3c29d8b96028afaabcac1ab52ed1941f5d5893bd6b3f3ecda4baa3d6d1c973ad2353c3fdcf043c, 0x2885cdbb4dcfc28da74b3546c2ea5ce80c65b0dd6ac438af1406030649fc2efbc64848edc8a1b1ed62dd7265c4417237f3a0c6724c88aa19258da453cfb89df7283d1b996cb83,
  0x208bd31dac8c454e0d5b3146f2cbe809256bde29e9ae8f97c166857c69935d495acdfd6b93b562933de4a059299c88077c3bb999fdc875dde867e59929aee4ba49e67ab0c03, 0x134485ab3fdd1223e847fd7e696e5e45b7f90090e1c0173acdf70f6a266ac9470415fe7a485b8ceaa97a1e7841f47a55ca154e51b548f75563fdd024641b35ec2e315fc32, 0x82eb13e1d681cc9e663ebb900d6af7fa42ca375f69c176185911e7dfe9afaee89dc47aa511e7dda7b8a3274975b8250a91338ef947afab752a818d09508325ef8c4e32,
  0x26a1357f179fb18f8700d4adf98d885bd827d998fa2d3ec232109054694b7ae947d6fef02a4e13891af33a17d0e71ff865992502cfbdb87897147510357101f386f1, 0x7a06203571e5ff22b4a725d3286c11fb805facc66f86698b0e9ddcaaf0f4369c840b36cfcb457f7addbd00d37465ff8b55974f703a7fac5142d2b10f3e319e371, 0xf68a980daf15ab04c4339db1033a38b1a47760cd9f6b7095417aadf9b55c108cd099ec8a4fb9743fa92e2c9ac9845f45af9e0535a2214c1ac9c390e57102a8,
  0x12dc6123514144b31530374b8a85120f7e2ac42c67582ad0e726aad6986228abd2cb9b906759d1a64e5e43af095c7467878f8a4fc6a58fbabad18a50a2a8, 0xd17612af4cdc927fe8d6b4ba2ffa09f8d311074116c8821ff49d0c3ececdac1ae90b5de6267b7886dbe2705c5cd8625d6105c15ddcaf9f74f3363417, 0x4bfdac9d39c36f85f5c2bdddb74eb69177dac8c25df6cab1b25ccd1d01d67c1d7a1baed61a082b2e8b4634872d80139b456bb98621d682491c497,
  0xd03d4452753b06b36b44bce4f2b5b151df77bc3eb4876d23e4e511e9cd1120d8c5b5996d1f95c750f0cd5232cfe38d355bd77e3825d3ed74e, 0xecc1fe4050abffdb679a72b719879cd026b69bc99c41f7f718cdc561aad3b3688a54ec0a1a5ccc494bfa59f94d5a938e76811e360994e, 0x5e866ca2741b89624adb49c00b0f122348b4640d3ece9eb3e47d7d65188bd63482f1280cb8821115787ad2e074c7874ccf79c1175,
  0xaa20ffcc8ca325f0932d00e7775aac87dacff5e58bcf1e97f6cb80a4598e05057f40ab95027190793dfcfaf31d40966585f5, 0x3fffe5ba99651d37c34fdcfadcd81a850e76797236b0b4406af6cead3bf1599605d0888c36c0a4e360c312f6f298574, 0x34f4b5d258e39efc2ffb565b55e68616413ba4c67bea59df5db226686ab9afac33f51d6aa508ad6c879ac8d74,
  0x342cb1068520d3fd0656d74faa85b5472df502ecdea26b0c9e4444334eb1c553126bacbb499bd2b4c3, 0x17a2ecc40cb03f7ff6ca362fcaa128194e2ddbd7d157adae4ee12f43e28e96a25f8a59a943, 0xfffffffffff9877509fcb133ea2717aa9c8fac706d6773cee22a5bf961f857a,
  0xd0b2c448fbd1250517595f2c63386319440e403b2ad680d77a, 0x3fffffffffffffffffffffffffffff81, 0x1]

private theorem eulerianCoefficients_eq : descentCoeffs 126 = eulerianCoefficients := by
  decide +kernel

private theorem upper : upperOK (descentCoeffs 126) first gaps = true := by
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

private theorem lower_054 : lowerOK (rows.getD 54 []) gaps = true := by
  decide +kernel

private theorem lower_055 : lowerOK (rows.getD 55 []) gaps = true := by
  decide +kernel

private theorem lower_056 : lowerOK (rows.getD 56 []) gaps = true := by
  decide +kernel

private theorem lower_057 : lowerOK (rows.getD 57 []) gaps = true := by
  decide +kernel

private theorem lower_058 : lowerOK (rows.getD 58 []) gaps = true := by
  decide +kernel

private theorem lower_059 : lowerOK (rows.getD 59 []) gaps = true := by
  decide +kernel

private theorem lower_060 : lowerOK (rows.getD 60 []) gaps = true := by
  decide +kernel

private theorem lower_061 : lowerOK (rows.getD 61 []) gaps = true := by
  decide +kernel

private theorem lower (i : Fin (lastRepresentative 127 - 2)) :
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
  · exact lower_054
  · exact lower_055
  · exact lower_056
  · exact lower_057
  · exact lower_058
  · exact lower_059
  · exact lower_060
  · exact lower_061

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 127) :
    StrictNegativeInterlacing (originalQuotient 127 k) (eulerian 126) 124 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N127
