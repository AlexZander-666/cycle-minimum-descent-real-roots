import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentPackedData.C127L127.N122

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N122

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L127.N122 LongCycleBounds.DescentNecklace.Packed.C127L127.N122.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L127.N122 LongCycleBounds.DescentNecklace.Packed.C127L127.N122.rows

private theorem actual : RepresentativeChecks 122 previousNodes rows :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L127.N122 LongCycleBounds.DescentNecklace.Packed.C127L127.N122.dataChecks

private def first : LongCycleFinite.Dyadic := ⟨-2658455991569831745807614120560689152, 0⟩

private def gaps : List Window := [
  ⟨⟨-2658369791329016226208312344742723584, 0⟩, ⟨-2030754136774649315328, 0⟩⟩,
  ⟨⟨-1956962656880183738368, 0⟩, ⟨-1316952937070592, 0⟩⟩,
  ⟨⟨-1235490292367360, 0⟩, ⟨-582729334784, 0⟩⟩,
  ⟨⟨-522259005440, 0⟩, ⟨-3728187392, 0⟩⟩,
  ⟨⟨-3703873536, 0⟩, ⟨-118919168, 0⟩⟩,
  ⟨⟨-118736128, 0⟩, ⟨-9476288, 0⟩⟩,
  ⟨⟨-9470560, 0⟩, ⟨-1360148, 0⟩⟩,
  ⟨⟨-1359712, 0⟩, ⟨-292166, 0⟩⟩,
  ⟨⟨-292107, 0⟩, ⟨-83662, 0⟩⟩,
  ⟨⟨-167301, 1⟩, ⟨-237091, 3⟩⟩,
  ⟨⟨-237067, 3⟩, ⟨-98721, 3⟩⟩,
  ⟨⟨-98713, 3⟩, ⟨-372843, 6⟩⟩,
  ⟨⟨-372819, 6⟩, ⟨-194463, 6⟩⟩,
  ⟨⟨-388905, 7⟩, ⟨-109905, 6⟩⟩,
  ⟨⟨-27475, 4⟩, ⟨-265339, 8⟩⟩,
  ⟨⟨-16583, 4⟩, ⟨-338185, 9⟩⟩,
  ⟨⟨-338173, 9⟩, ⟨-451123, 10⟩⟩,
  ⟨⟨-225555, 9⟩, ⟨-78175, 8⟩⟩,
  ⟨⟨-312691, 10⟩, ⟨-447973, 11⟩⟩,
  ⟨⟨-223981, 10⟩, ⟨-165037, 10⟩⟩,
  ⟨⟨-165033, 10⟩, ⟨-249221, 11⟩⟩,
  ⟨⟨-1947, 4⟩, ⟨-192217, 11⟩⟩,
  ⟨⟨-192213, 11⟩, ⟨-302087, 12⟩⟩,
  ⟨⟨-151041, 11⟩, ⟨-482617, 13⟩⟩,
  ⟨⟨-482609, 13⟩, ⟨-195581, 12⟩⟩,
  ⟨⟨-97789, 11⟩, ⟨-321155, 13⟩⟩,
  ⟨⟨-160575, 12⟩, ⟨-133365, 12⟩⟩,
  ⟨⟨-133363, 12⟩, ⟨-447649, 14⟩⟩,
  ⟨⟨-447643, 14⟩, ⟨-189569, 13⟩⟩,
  ⟨⟨-379133, 14⟩, ⟨-80951, 12⟩⟩,
  ⟨⟨-40475, 11⟩, ⟨-69659, 12⟩⟩,
  ⟨⟨-34829, 11⟩, ⟨-241407, 14⟩⟩,
  ⟨⟨-482809, 15⟩, ⟨-420905, 15⟩⟩,
  ⟨⟨-420901, 15⟩, ⟨-23063, 11⟩⟩,
  ⟨⟨-92251, 13⟩, ⟨-20323, 11⟩⟩,
  ⟨⟨-81291, 13⟩, ⟨-143939, 14⟩⟩,
  ⟨⟨-287875, 15⟩, ⟨-511909, 16⟩⟩,
  ⟨⟨-511905, 16⟩, ⟨-57115, 13⟩⟩,
  ⟨⟨-456915, 16⟩, ⟨-102323, 14⟩⟩,
  ⟨⟨-51161, 13⟩, ⟨-22989, 12⟩⟩,
  ⟨⟨-367821, 16⟩, ⟨-41443, 13⟩⟩,
  ⟨⟨-331541, 16⟩, ⟨-299657, 16⟩⟩,
  ⟨⟨-149827, 15⟩, ⟨-271513, 16⟩⟩,
  ⟨⟨-135755, 15⟩, ⟨-246571, 16⟩⟩,
  ⟨⟨-246569, 16⟩, ⟨-224385, 16⟩⟩,
  ⟨⟨-224383, 16⟩, ⟨-204581, 16⟩⟩,
  ⟨⟨-409159, 17⟩, ⟨-373687, 17⟩⟩,
  ⟨⟨-93421, 15⟩, ⟨-170907, 16⟩⟩,
  ⟨⟨-341811, 17⟩, ⟨-39137, 14⟩⟩,
  ⟨⟨-313093, 17⟩, ⟨-143573, 16⟩⟩,
  ⟨⟨-35893, 14⟩, ⟨-263639, 17⟩⟩,
  ⟨⟨-263637, 17⟩, ⟨-484585, 18⟩⟩,
  ⟨⟨-484581, 18⟩, ⟨-222863, 17⟩⟩,
  ⟨⟨-445723, 18⟩, ⟨-51285, 15⟩⟩,
  ⟨⟨-410277, 18⟩, ⟨-188941, 17⟩⟩,
  ⟨⟨-377879, 18⟩, ⟨-87053, 16⟩⟩,
  ⟨⟨-348209, 18⟩, ⟨-320995, 18⟩⟩,
  ⟨⟨-10031, 13⟩, ⟨-18499, 14⟩⟩,
  ⟨⟨-147991, 17⟩, ⟨-272967, 18⟩⟩,
  ⟨⟨-272965, 18⟩, ⟨-251753, 18⟩⟩,
  ⟨⟨-251751, 18⟩, ⟨-232175, 18⟩⟩,
  ⟨⟨-232173, 18⟩, ⟨-214085, 18⟩⟩,
  ⟨⟨-428167, 19⟩, ⟨-394701, 19⟩⟩,
  ⟨⟨-197349, 18⟩, ⟨-363713, 19⟩⟩,
  ⟨⟨-181855, 18⟩, ⟨-20937, 15⟩⟩,
  ⟨⟨-334989, 19⟩, ⟨-308351, 19⟩⟩,
  ⟨⟨-308349, 19⟩, ⟨-35453, 16⟩⟩,
  ⟨⟨-283621, 19⟩, ⟨-521317, 20⟩⟩,
  ⟨⟨-260657, 19⟩, ⟨-239321, 19⟩⟩,
  ⟨⟨-239319, 19⟩, ⟨-109743, 18⟩⟩,
  ⟨⟨-54871, 17⟩, ⟨-402091, 20⟩⟩,
  ⟨⟨-50261, 17⟩, ⟨-91949, 18⟩⟩,
  ⟨⟨-367793, 20⟩, ⟨-83977, 18⟩⟩,
  ⟨⟨-335905, 20⟩, ⟨-76565, 18⟩⟩,
  ⟨⟨-306257, 20⟩, ⟨-278703, 20⟩⟩,
  ⟨⟨-69675, 18⟩, ⟨-506201, 21⟩⟩,
  ⟨⟨-506197, 21⟩, ⟨-14333, 16⟩⟩,
  ⟨⟨-114663, 19⟩, ⟨-414545, 21⟩⟩,
  ⟨⟨-207271, 20⟩, ⟨-186829, 20⟩⟩,
  ⟨⟨-373655, 21⟩, ⟨-335801, 21⟩⟩,
  ⟨⟨-167899, 20⟩, ⟨-150399, 20⟩⟩,
  ⟨⟨-300795, 21⟩, ⟨-268485, 21⟩⟩,
  ⟨⟨-134241, 20⟩, ⟨-477425, 22⟩⟩,
  ⟨⟨-477421, 22⟩, ⟨-105669, 20⟩⟩,
  ⟨⟨-422671, 22⟩, ⟨-372459, 22⟩⟩,
  ⟨⟨-372455, 22⟩, ⟨-163267, 21⟩⟩,
  ⟨⟨-163265, 21⟩, ⟨-35583, 19⟩⟩,
  ⟨⟨-284661, 22⟩, ⟨-246633, 22⟩⟩,
  ⟨⟨-493261, 23⟩, ⟨-53057, 20⟩⟩,
  ⟨⟨-424451, 23⟩, ⟨-181253, 22⟩⟩,
  ⟨⟨-362501, 23⟩, ⟨-307025, 23⟩⟩,
  ⟨⟨-307021, 23⟩, ⟨-515279, 24⟩⟩,
  ⟨⟨-64409, 21⟩, ⟨-427961, 24⟩⟩,
  ⟨⟨-427955, 24⟩, ⟨-175683, 23⟩⟩,
  ⟨⟨-351361, 24⟩, ⟨-284783, 24⟩⟩,
  ⟨⟨-142389, 23⟩, ⟨-454969, 25⟩⟩,
  ⟨⟨-227481, 24⟩, ⟨-89379, 23⟩⟩,
  ⟨⟨-357509, 25⟩, ⟨-275743, 25⟩⟩,
  ⟨⟨-137869, 24⟩, ⟨-26025, 22⟩⟩,
  ⟨⟨-52049, 23⟩, ⟨-153403, 25⟩⟩,
  ⟨⟨-306799, 26⟩, ⟨-439533, 27⟩⟩,
  ⟨⟨-109881, 25⟩, ⟨-304671, 27⟩⟩,
  ⟨⟨-38083, 24⟩, ⟨-203209, 27⟩⟩,
  ⟨⟨-406407, 28⟩, ⟨-259001, 28⟩⟩,
  ⟨⟨-129497, 27⟩, ⟨-312637, 29⟩⟩,
  ⟨⟨-312627, 29⟩, ⟨-22087, 26⟩⟩,
  ⟨⟨-88345, 28⟩, ⟨-92157, 29⟩⟩,
  ⟨⟨-184307, 30⟩, ⟨-174035, 31⟩⟩,
  ⟨⟨-43507, 29⟩, ⟨-289847, 33⟩⟩,
  ⟨⟨-289833, 33⟩, ⟨-102679, 33⟩⟩,
  ⟨⟨-410695, 35⟩, ⟨-235261, 36⟩⟩,
  ⟨⟨-14703, 32⟩, ⟨-50531, 36⟩⟩,
  ⟨⟨-404223, 39⟩, ⟨-464293, 42⟩⟩,
  ⟨⟨-232131, 41⟩, ⟨-9249, 40⟩⟩,
  ⟨⟨-295947, 45⟩, ⟨-303765, 50⟩⟩,
  ⟨⟨-151871, 49⟩, ⟨-272631, 57⟩⟩,
  ⟨⟨-136305, 56⟩, ⟨-112621, 67⟩⟩,
  ⟨⟨-225223, 68⟩, ⟨-152617, 88⟩⟩,
  ⟨⟨-305205, 89⟩, ⟨-262149, 139⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private def eulerianCoefficients : List ℤ := [
  0x1, 0x1ffffffffffffffffffffffffffff86, 0xdbdcfd23cd3d4155a9135ac892ab131122d2f6c312cae9f8,
  0x3ffffffffff9738af5cf030cedcf2cec6bc6a1a78e9d5677667090b55bc0a, 0x1efb117829c134aca3e5d7813e0bdc0c4fc2f0eb983870c248b0bc27a4ddad37b64c4e2, 0x1b7b9f95b60154df99cf5112f74b96b2ad32d6dcd308987ca08600b9490f4c7b96300f265bfcdc2,
  0xce7e0759ddd1c3c209d793e5a2a6bdea9e799d98c62b1b7b33c6518b57ada60ce8a62c523ba8f8449ce18, 0x7fff9d97ed59b00f414978b9cce8cfe47a7de90d206b24931171141b17ffd1e5a2858ce9134cfe60907f661618e, 0xbcd007e0c518e23b719368ec8ff0f86962b6a2989ce658bd6356e4b8f1fdd450336d96543dba26926f18977cd751a433,
  0x3df0832facf7fd7e6b8a5cda6ac32754e02cba7ed2b500b8cd4ce9deb2ca0a488fceeedf0ea35bc2366d69cfcd614da967c24, 0x604d674cb5f7274162b3b90b5a56b1138ff93541be710306de18c271d481ba4a5f73be991d002b66a4350ab573f5ff4da118687d0, 0x36c9534e24d3b07db6049e5e20278b41627ddb3bbfc735015eb40c99e07940407a3e17587c73154e5425340eb6a7bcb5969d8ee2ba73c,
  0xd61d260a1ee1eb2dcb985bbe670131f6ca7dbb66c2ac7990392a7d65643ad51bf7955be503cba199323d802e8e42ff878d47fe8c4e6ff924, 0x196954325177a0a2c1df692395400ef17a0d04eae7ea1f9b83365f9aad758e99fc0a943dbb0f1dcf531a6e6a741243d9ae5ebbea199faec03c9c, 0x19d839fbe0f1a81df3fe27b13a8f6ae791a4b1a1216eb5bb44ae6e07684e6a8bdf2a050e1e53455824f3c990440a71d026e3d9c5e8fc0c986478a50,
  0xf380288a3d3491fef0e2a55ed9f393187791b4d0837e1c19954783d8b0d2b70038d64d9f2671cbe0ad6501cd33e7460675ba59915719e90837c3a71c4, 0x586e2697245ce5294f80721916be7e7e90b231b164caec90d9d7b8e872e4676d6f82f77cd495acfe797d5c73fc5379d63c3e68732d2e3727ef95a872778d, 0x14dbd73423f95b97ce127626ad474a09dbd07d93e14d4a6184aa80e817baeff3e090a52e3bb6249eac08e7a954bc1df4a3fdeaa2457f762ff4eb2b7f1c9cb0a,
  0x355fef5684e794d76035b64592a928ab9768db72170e384e02001830ab891ea8a73b0c4fa18a80293e115a79e79a148c672244f3603577ea246c4262ca114d2c8, 0x5ffe8110f7d07f0ad86ce2e682ffbb35f350546e436a5d5ef5429a6cbe50dca639b157505e205a88d1762eff30ab8e1ba895adbf3748e21caaf93fea2d95f725de6, 0x7d1687c6b63e150ee2273046afb19e56457801e3534fb5b23ef2f19d16db9d9f9cad9e53019bd74006edb240a9492d26ffb342e40926f4a9ac93471150b635c273656,
  0x7932b82b31965d5fe6706b5ee5b41f58387aa524b79d497f2436beadd294f240862beab2a0787328dace748ad17d7535afb9255934ef47298858c09a35aef4a780d299e, 0x59470a8c51adbf241501530bb627c5b464b73ade4290071a28a97e5c2ffcef3f3a4d079c92c5a47c390a8cced95835a83b40176cc0e1990d6e8dbfee055fe49150db6f6e8, 0x32f7f9a3eba430c3a7451471fe956584a507834238ca2278734bcbbba02a3733454fe3d59f4ef7a99d887a8e83f17597f3e467c5ba701bec0e6cb0703c089c186da48c53312,
  0x16ee9fcb16d9aa971595363bebdcc7cb35ddff871f2bda40a7aafd5b7743ce9da491f8ff73ad1eace85c53c1254d304e064e63e746bc51151a958dec0e803f95b4693bd040e6f, 0x840584a00bde3f6992256a1e8c486f5f8b783ae4f1bf981a0e809c64bab625aa80f39540c46160c2f566ac5717115c56fb1c637e3b80cd690e959213089d26a29f87b9a5a7c008, 0x267b7b3308ecf11b15afc36589eb6161975a921cc05d10f7eb92d8222df9e8b7e1d84f866777a18c208a54a4e93e3c3c07ce72c31ca12844dbbc1966de950fed8125f9c0c02fdca0,
  0x930e812640e08f2226e406741ce197fee48709082ad41821911dd538ce20977b69d27d925d805619fc0e34b0e55f9617b53b2766782446840cabcfe451d9255fd8d675cb9f224e4b8, 0x1d126469f6abd8ac901dfec35b583b331ad67bdf873a61d7c75c98860eb2de3cbc46044a0b823c0880a195e2f84d9ea0cf92dfb562e68eb9bf66b135d0bc182a5459ba798d3a87991a8, 0x4cce148138039bf8429a5aa14826e1f201a5c9b35bf49a93baac59afa841e5912c11dd5ad908bb5e9eaa8e726405e1dd31911ab3382383a4913c24fc2192ad5ad4e7400b585fbcf53738,
  0xaadb1d2de50fd9db85077686ec398fdec92652281416f0fe05c324c5e4617337e1f499c385a20e6973088f3339fa043a470e860b79caac617d81cf42e21442d4286433fa0f192187f72a0, 0x1425e5a6fb6113e9329cdcef36fe29104cc239a7f6aba4055b1975cf4193c1c41486d2b4aa496b3205601283d1366d5ea8e14a62eb2eccab5ed917c9d8c7598e7d6f71ad14bcba21f540188, 0x20748b37380e28faf1a4ed5d2f21fe27fffa2bbff15f25f3b9fcf79f612b99e2ab329f3e433e10a7b54694502701562b0eb2e2e5bea1b8c57ef8da6ca3ff103299a5e60da5bf8e417a59a5fd,
  0x2ce641944fcb9db9428f4c344a722466b8ded4feb7c67d3f409755e7b61e43a42a03996526f33f17721da6c649b2bccab7d89bf78142908bab63a55b619af43f9d0251de09e3fdc4cbd0457e6, 0x35a217d218095b8eb30363109cadc21b36080e320111b9f7fc12de5792d57d4d5cdbaa98ba879195d5fe0d2b521ba884a78b2f66adafb730a2b7734ae84c1577ed1126a22c2396b5c3dc9e7878, 0x37968d5b28c41b44e4234044c269e68675da1f9b39efd1734344d857999b51636d40f9938b3a25d75bd5cac09cb2478a2fb7418a4495a4461412a8bd6a005dbef7086ad76aabeeb93359a3edaaa,
  0x323677ce534cc010a226c451f079f1471d24d986ef05e50d4185379f119c9ec501d1e5d1f7fa7d30e3e12ae0ddba03f0aeb483409b61f05f3fc18baf67e4e549c383cc17e927a4a336b22839e9b2, 0x27b0cfde2ffe2fd818c3e184a88da0670fba0160c7ba193104c800c397724ac3573d28c1ac1133aef70afe73ed7447c92a7e300d88c56916c0bf847aa02383a6476e77eef9277ae09f1a911acd002, 0x1b8e397175909e7a75f21d8a99ed9fe9038effbc00b8ab8af8caa464089f7aa24da79a84267d5cd9180eac9e825405fb10670ddfb1ae1ccd72f59bace119ee89b0b154a63e8a2542f247d723e72a18,
  0x10dc03d5e5733da7784a0049668468e7a80fa227adc7d1266fa12a8200df5a7667c619e08a85faf83462d1e8ff5101afe33910eaa90736e4504a6c89990e93011da95e3f33b437b0f174a6d34974b4e, 0x91e5fa709ae110ebc1ea76b612480c5aba8fe5ddbe5f3bb2bceae658c8c75e9df55316ce4f49608092086e0c1b66aecd54c7105a3047f6d6edbe3144407c9b521a14b0977e8eed3b4e5c77f25a9aad7, 0x45f477e2bc2d73ffdfa713bf479c08fb27d1d973f199313938db42799b4e471dc8a8a568f1069c274b9a78c09a3903cbeb7c0f91ea3af735cca18333c5ccc61c3b82ca9a2ee2dff2f5affc12c0b2043c,
  0x1dcfda2c33ee30a68902feba842f82710ed3d715e4785c4011033989a7aa935d3de255257d091dee5cef3dfb7a40cf1654c3b2ec264472ed105efbfaf89f2164e4b23778600b0796f0bfc9fbd320579b0, 0xb518edd416fdc431dabbc93bc1df5f793cd993cb57d07fa2f31a16f1f3814f680d7fa1567343ce7f5043df8973302253c2dc2a61f5422d8c024048b910d5bbb250d3a044422ed4636f0bd9b8847205564, 0x3d635c67dc40b2a863d0b90a4c6601da2dc95091bee14e13de9163dd9be82d4e73a7884d8d8b038dae906df5d7f8554a3f67599c808ad83a5670e0e9fce7361f42abff4de183146df2bfb3204f40289b1c,
  0x129dadb1bbbd34ed00fcd8c8b904b1034ca372304c13235a849783298575e8ef71d98b504ae1039ae171710cfa585fba037b3260722861eeb7f11527a0422ce6df4a9b02202f183b8e0f5155167e5a91044, 0x50f3291dae7eb291997a5ef9de1cd2005fddd411482d8f4c7c6576a59731eda8cad49b0fb875d6d8e0d5c8573da2473e1e1cee65f0bd4353f06b3a8339bb8f2f423f03272bbdde9cdf34224cbd5aef6c630, 0x13bfcf32bf9c51fb141c5e806cde6234054af235fca3e5fc6937e55c2c4feae3a3398cc2f846dc070831b8c0227c4d7b02c36ae95b57600e0698bc30ad374c9688f66d0caf863b5d42f797f5ac125f4f805c,
  0x454e891190a887bfd98a06581b1d8430f72698e95a60da1d5fa2eefebd91b1eb92252c3a07c0e710a4d2ad3d73673f88e9761850175f543dd9c876b62640bd2e2ac5c8656991630ecb555ccb4101cb5911a9, 0xdaf4a8a6e99c86f31fcb59f5a9019b2caaaf20b44d940c2973b3e7bddf997c14c68d238c62d109ba4f4efd5193f8d2003da061d3cf78925f2929c576e22dfa529c49f6a425e2269f216f7e8826fa4dec471a, 0x26f79bf3b9be11b82e3840748255695d37da8e42c1a6ef5d226af875c300f0ba457ff7a7cc0aaf62ed7117e2be522e911145a706efb2dd25e03e0946459ef1303b041b89a8a3cb504af6a64f769b206d97108,
  0x641e840259157a9eb9d396c877415ed0f12ec0b8e8a31c7d7643fa4fb6493740dee3f87f6e2ab8104dde1518606e20bb1d6de56a47dbf3c43f8e358fefb8780a3913ad54a0244aab13db9e3eb8e8afc1a4d56, 0xe855175358c3254243393b0002416e31f3700fc6da22f17e701954fb236e33b9572ee46329acf0b7b7d0450931079715a1d8aadba514109477949bd625c6cedb1ae2f28525e4d6dbe26f49bef384ab9de3b16, 0x1e75b23fa04109e3355cde637cd4ae21f0f4653fe309abf513a5f8805b1747edf549595e2cc9a760cf0543a821ce0e8131044815a3761b5355345afc44f5bd5d43c1c8bcbf6cd4b2a672d8978cf6f0fe15b6ae,
  0x39ccd6287ead951fea5f2b9c82f42789526108d013b80fe3b90b805e50875e59d921d208b3c4d6cb96b20bc60672d9bfc2726002718681e6dca6c2facf865b3782f995d43e44d3e3d9d13e2640330b3fb56aa8, 0x63485674f98357369fdcb7bbad263ff35d3be6a5c58f2448600edeb9b3c4db78c6c5bf44e0d476100022b72fe59dbfac0bfe665d53e49f7b5313ae85c738627dc542234d5e705d76dd60480f63033781dcf682, 0x9a7356682cd61a626ab216bbd746a2310be3f445a9c286ce8a677579f801345936558e76507d3202d6ffbea4f7636eecc03648b5d4e5bf911bd5820401b78af0831c7d3ffded0aaeec977fe8267559e7db7353,
  0xd9b417b9f263b5210829c88af8121b43259d46da5c8a1eaa50e0317f702abeaa82399737b02abc1d9824f3a70e884b75b9b822f3cc15635701d0a3877afd9aef7094444bcf3212a4b022d889b05b2a31dc8bf0, 0x11620e6ea480e781f2c1bf8291edbedd7079e2960bd9e44e72cc10675baddfb8ed491110563166d2f0223ccf553e951d4c034780a3ee0af03ef70c238ad0af69189bf6df4a4cf899fde7188dcae388a21915ec0, 0x142218f5a17d48a63876c293303bfe5e7f04179f5c4b9a0df3c7406fcca482686da50179dbedc8f4edbd6a674362c43d166877dd3b947fbf7bd39509cb47f0851f61e60a0dcbddb989384c156c0853a387fda90,
  0x1524a0c7eeb2c3ff83beb5a63f4a795f338168fc90eb7e348ec9c76a13c0c3face26d3e4a4bfebac1c14379dc2b0837df47bc1c4e67bd657b5719647cb50fae5f9ceee35b08d7a7b7632963586a32b4fe937430, 0x142218f5a17d48a63876c293303bfe5e7f04179f5c4b9a0df3c7406fcca482686da50179dbedc8f4edbd6a674362c43d166877dd3b947fbf7bd39509cb47f0851f61e60a0dcbddb989384c156c0853a387fda90, 0x11620e6ea480e781f2c1bf8291edbedd7079e2960bd9e44e72cc10675baddfb8ed491110563166d2f0223ccf553e951d4c034780a3ee0af03ef70c238ad0af69189bf6df4a4cf899fde7188dcae388a21915ec0,
  0xd9b417b9f263b5210829c88af8121b43259d46da5c8a1eaa50e0317f702abeaa82399737b02abc1d9824f3a70e884b75b9b822f3cc15635701d0a3877afd9aef7094444bcf3212a4b022d889b05b2a31dc8bf0, 0x9a7356682cd61a626ab216bbd746a2310be3f445a9c286ce8a677579f801345936558e76507d3202d6ffbea4f7636eecc03648b5d4e5bf911bd5820401b78af0831c7d3ffded0aaeec977fe8267559e7db7353, 0x63485674f98357369fdcb7bbad263ff35d3be6a5c58f2448600edeb9b3c4db78c6c5bf44e0d476100022b72fe59dbfac0bfe665d53e49f7b5313ae85c738627dc542234d5e705d76dd60480f63033781dcf682,
  0x39ccd6287ead951fea5f2b9c82f42789526108d013b80fe3b90b805e50875e59d921d208b3c4d6cb96b20bc60672d9bfc2726002718681e6dca6c2facf865b3782f995d43e44d3e3d9d13e2640330b3fb56aa8, 0x1e75b23fa04109e3355cde637cd4ae21f0f4653fe309abf513a5f8805b1747edf549595e2cc9a760cf0543a821ce0e8131044815a3761b5355345afc44f5bd5d43c1c8bcbf6cd4b2a672d8978cf6f0fe15b6ae, 0xe855175358c3254243393b0002416e31f3700fc6da22f17e701954fb236e33b9572ee46329acf0b7b7d0450931079715a1d8aadba514109477949bd625c6cedb1ae2f28525e4d6dbe26f49bef384ab9de3b16,
  0x641e840259157a9eb9d396c877415ed0f12ec0b8e8a31c7d7643fa4fb6493740dee3f87f6e2ab8104dde1518606e20bb1d6de56a47dbf3c43f8e358fefb8780a3913ad54a0244aab13db9e3eb8e8afc1a4d56, 0x26f79bf3b9be11b82e3840748255695d37da8e42c1a6ef5d226af875c300f0ba457ff7a7cc0aaf62ed7117e2be522e911145a706efb2dd25e03e0946459ef1303b041b89a8a3cb504af6a64f769b206d97108, 0xdaf4a8a6e99c86f31fcb59f5a9019b2caaaf20b44d940c2973b3e7bddf997c14c68d238c62d109ba4f4efd5193f8d2003da061d3cf78925f2929c576e22dfa529c49f6a425e2269f216f7e8826fa4dec471a,
  0x454e891190a887bfd98a06581b1d8430f72698e95a60da1d5fa2eefebd91b1eb92252c3a07c0e710a4d2ad3d73673f88e9761850175f543dd9c876b62640bd2e2ac5c8656991630ecb555ccb4101cb5911a9, 0x13bfcf32bf9c51fb141c5e806cde6234054af235fca3e5fc6937e55c2c4feae3a3398cc2f846dc070831b8c0227c4d7b02c36ae95b57600e0698bc30ad374c9688f66d0caf863b5d42f797f5ac125f4f805c, 0x50f3291dae7eb291997a5ef9de1cd2005fddd411482d8f4c7c6576a59731eda8cad49b0fb875d6d8e0d5c8573da2473e1e1cee65f0bd4353f06b3a8339bb8f2f423f03272bbdde9cdf34224cbd5aef6c630,
  0x129dadb1bbbd34ed00fcd8c8b904b1034ca372304c13235a849783298575e8ef71d98b504ae1039ae171710cfa585fba037b3260722861eeb7f11527a0422ce6df4a9b02202f183b8e0f5155167e5a91044, 0x3d635c67dc40b2a863d0b90a4c6601da2dc95091bee14e13de9163dd9be82d4e73a7884d8d8b038dae906df5d7f8554a3f67599c808ad83a5670e0e9fce7361f42abff4de183146df2bfb3204f40289b1c, 0xb518edd416fdc431dabbc93bc1df5f793cd993cb57d07fa2f31a16f1f3814f680d7fa1567343ce7f5043df8973302253c2dc2a61f5422d8c024048b910d5bbb250d3a044422ed4636f0bd9b8847205564,
  0x1dcfda2c33ee30a68902feba842f82710ed3d715e4785c4011033989a7aa935d3de255257d091dee5cef3dfb7a40cf1654c3b2ec264472ed105efbfaf89f2164e4b23778600b0796f0bfc9fbd320579b0, 0x45f477e2bc2d73ffdfa713bf479c08fb27d1d973f199313938db42799b4e471dc8a8a568f1069c274b9a78c09a3903cbeb7c0f91ea3af735cca18333c5ccc61c3b82ca9a2ee2dff2f5affc12c0b2043c, 0x91e5fa709ae110ebc1ea76b612480c5aba8fe5ddbe5f3bb2bceae658c8c75e9df55316ce4f49608092086e0c1b66aecd54c7105a3047f6d6edbe3144407c9b521a14b0977e8eed3b4e5c77f25a9aad7,
  0x10dc03d5e5733da7784a0049668468e7a80fa227adc7d1266fa12a8200df5a7667c619e08a85faf83462d1e8ff5101afe33910eaa90736e4504a6c89990e93011da95e3f33b437b0f174a6d34974b4e, 0x1b8e397175909e7a75f21d8a99ed9fe9038effbc00b8ab8af8caa464089f7aa24da79a84267d5cd9180eac9e825405fb10670ddfb1ae1ccd72f59bace119ee89b0b154a63e8a2542f247d723e72a18, 0x27b0cfde2ffe2fd818c3e184a88da0670fba0160c7ba193104c800c397724ac3573d28c1ac1133aef70afe73ed7447c92a7e300d88c56916c0bf847aa02383a6476e77eef9277ae09f1a911acd002,
  0x323677ce534cc010a226c451f079f1471d24d986ef05e50d4185379f119c9ec501d1e5d1f7fa7d30e3e12ae0ddba03f0aeb483409b61f05f3fc18baf67e4e549c383cc17e927a4a336b22839e9b2, 0x37968d5b28c41b44e4234044c269e68675da1f9b39efd1734344d857999b51636d40f9938b3a25d75bd5cac09cb2478a2fb7418a4495a4461412a8bd6a005dbef7086ad76aabeeb93359a3edaaa, 0x35a217d218095b8eb30363109cadc21b36080e320111b9f7fc12de5792d57d4d5cdbaa98ba879195d5fe0d2b521ba884a78b2f66adafb730a2b7734ae84c1577ed1126a22c2396b5c3dc9e7878,
  0x2ce641944fcb9db9428f4c344a722466b8ded4feb7c67d3f409755e7b61e43a42a03996526f33f17721da6c649b2bccab7d89bf78142908bab63a55b619af43f9d0251de09e3fdc4cbd0457e6, 0x20748b37380e28faf1a4ed5d2f21fe27fffa2bbff15f25f3b9fcf79f612b99e2ab329f3e433e10a7b54694502701562b0eb2e2e5bea1b8c57ef8da6ca3ff103299a5e60da5bf8e417a59a5fd, 0x1425e5a6fb6113e9329cdcef36fe29104cc239a7f6aba4055b1975cf4193c1c41486d2b4aa496b3205601283d1366d5ea8e14a62eb2eccab5ed917c9d8c7598e7d6f71ad14bcba21f540188,
  0xaadb1d2de50fd9db85077686ec398fdec92652281416f0fe05c324c5e4617337e1f499c385a20e6973088f3339fa043a470e860b79caac617d81cf42e21442d4286433fa0f192187f72a0, 0x4cce148138039bf8429a5aa14826e1f201a5c9b35bf49a93baac59afa841e5912c11dd5ad908bb5e9eaa8e726405e1dd31911ab3382383a4913c24fc2192ad5ad4e7400b585fbcf53738, 0x1d126469f6abd8ac901dfec35b583b331ad67bdf873a61d7c75c98860eb2de3cbc46044a0b823c0880a195e2f84d9ea0cf92dfb562e68eb9bf66b135d0bc182a5459ba798d3a87991a8,
  0x930e812640e08f2226e406741ce197fee48709082ad41821911dd538ce20977b69d27d925d805619fc0e34b0e55f9617b53b2766782446840cabcfe451d9255fd8d675cb9f224e4b8, 0x267b7b3308ecf11b15afc36589eb6161975a921cc05d10f7eb92d8222df9e8b7e1d84f866777a18c208a54a4e93e3c3c07ce72c31ca12844dbbc1966de950fed8125f9c0c02fdca0, 0x840584a00bde3f6992256a1e8c486f5f8b783ae4f1bf981a0e809c64bab625aa80f39540c46160c2f566ac5717115c56fb1c637e3b80cd690e959213089d26a29f87b9a5a7c008,
  0x16ee9fcb16d9aa971595363bebdcc7cb35ddff871f2bda40a7aafd5b7743ce9da491f8ff73ad1eace85c53c1254d304e064e63e746bc51151a958dec0e803f95b4693bd040e6f, 0x32f7f9a3eba430c3a7451471fe956584a507834238ca2278734bcbbba02a3733454fe3d59f4ef7a99d887a8e83f17597f3e467c5ba701bec0e6cb0703c089c186da48c53312, 0x59470a8c51adbf241501530bb627c5b464b73ade4290071a28a97e5c2ffcef3f3a4d079c92c5a47c390a8cced95835a83b40176cc0e1990d6e8dbfee055fe49150db6f6e8,
  0x7932b82b31965d5fe6706b5ee5b41f58387aa524b79d497f2436beadd294f240862beab2a0787328dace748ad17d7535afb9255934ef47298858c09a35aef4a780d299e, 0x7d1687c6b63e150ee2273046afb19e56457801e3534fb5b23ef2f19d16db9d9f9cad9e53019bd74006edb240a9492d26ffb342e40926f4a9ac93471150b635c273656, 0x5ffe8110f7d07f0ad86ce2e682ffbb35f350546e436a5d5ef5429a6cbe50dca639b157505e205a88d1762eff30ab8e1ba895adbf3748e21caaf93fea2d95f725de6,
  0x355fef5684e794d76035b64592a928ab9768db72170e384e02001830ab891ea8a73b0c4fa18a80293e115a79e79a148c672244f3603577ea246c4262ca114d2c8, 0x14dbd73423f95b97ce127626ad474a09dbd07d93e14d4a6184aa80e817baeff3e090a52e3bb6249eac08e7a954bc1df4a3fdeaa2457f762ff4eb2b7f1c9cb0a, 0x586e2697245ce5294f80721916be7e7e90b231b164caec90d9d7b8e872e4676d6f82f77cd495acfe797d5c73fc5379d63c3e68732d2e3727ef95a872778d,
  0xf380288a3d3491fef0e2a55ed9f393187791b4d0837e1c19954783d8b0d2b70038d64d9f2671cbe0ad6501cd33e7460675ba59915719e90837c3a71c4, 0x19d839fbe0f1a81df3fe27b13a8f6ae791a4b1a1216eb5bb44ae6e07684e6a8bdf2a050e1e53455824f3c990440a71d026e3d9c5e8fc0c986478a50, 0x196954325177a0a2c1df692395400ef17a0d04eae7ea1f9b83365f9aad758e99fc0a943dbb0f1dcf531a6e6a741243d9ae5ebbea199faec03c9c,
  0xd61d260a1ee1eb2dcb985bbe670131f6ca7dbb66c2ac7990392a7d65643ad51bf7955be503cba199323d802e8e42ff878d47fe8c4e6ff924, 0x36c9534e24d3b07db6049e5e20278b41627ddb3bbfc735015eb40c99e07940407a3e17587c73154e5425340eb6a7bcb5969d8ee2ba73c, 0x604d674cb5f7274162b3b90b5a56b1138ff93541be710306de18c271d481ba4a5f73be991d002b66a4350ab573f5ff4da118687d0,
  0x3df0832facf7fd7e6b8a5cda6ac32754e02cba7ed2b500b8cd4ce9deb2ca0a488fceeedf0ea35bc2366d69cfcd614da967c24, 0xbcd007e0c518e23b719368ec8ff0f86962b6a2989ce658bd6356e4b8f1fdd450336d96543dba26926f18977cd751a433, 0x7fff9d97ed59b00f414978b9cce8cfe47a7de90d206b24931171141b17ffd1e5a2858ce9134cfe60907f661618e,
  0xce7e0759ddd1c3c209d793e5a2a6bdea9e799d98c62b1b7b33c6518b57ada60ce8a62c523ba8f8449ce18, 0x1b7b9f95b60154df99cf5112f74b96b2ad32d6dcd308987ca08600b9490f4c7b96300f265bfcdc2, 0x1efb117829c134aca3e5d7813e0bdc0c4fc2f0eb983870c248b0bc27a4ddad37b64c4e2,
  0x3ffffffffff9738af5cf030cedcf2cec6bc6a1a78e9d5677667090b55bc0a, 0xdbdcfd23cd3d4155a9135ac892ab131122d2f6c312cae9f8, 0x1ffffffffffffffffffffffffffff86,
  0x1]

private theorem eulerianCoefficients_eq : descentCoeffs 121 = eulerianCoefficients := by
  decide +kernel

private theorem upper : upperOK (descentCoeffs 121) first gaps = true := by
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

private theorem lower (i : Fin (lastRepresentative 122 - 2)) :
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

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 122) :
    StrictNegativeInterlacing (originalQuotient 122 k) (eulerian 121) 119 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N122
