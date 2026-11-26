import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentPackedData.C127L120.N115

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N115

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L120.N115 LongCycleBounds.DescentNecklace.Packed.C127L120.N115.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L120.N115 LongCycleBounds.DescentNecklace.Packed.C127L120.N115.rows

private theorem actual : RepresentativeChecks 115 previousNodes rows :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L120.N115 LongCycleBounds.DescentNecklace.Packed.C127L120.N115.dataChecks

private def first : LongCycleFinite.Dyadic := ⟨-20769187434139310514121985316880384, 0⟩

private def gaps : List Window := [
  ⟨⟨-20768513994757939267252440193302528, 0⟩, ⟨-118948510408156119040, 0⟩⟩,
  ⟨⟨-118371768180875984896, 0⟩, ⟨-178380729221120, 0⟩⟩,
  ⟨⟨-173661097033728, 0⟩, ⟨-111498756096, 0⟩⟩,
  ⟨⟨-103496548352, 0⟩, ⟨-1029056512, 0⟩⟩,
  ⟨⟨-1023766528, 0⟩, ⟨-40084224, 0⟩⟩,
  ⟨⟨-40034048, 0⟩, ⟨-3679864, 0⟩⟩,
  ⟨⟨-3677960, 0⟩, ⟨-588616, 0⟩⟩,
  ⟨⟨-588450, 0⟩, ⟨-137646, 0⟩⟩,
  ⟨⟨-137621, 0⟩, ⟨-337691, 3⟩⟩,
  ⟨⟨-42206, 0⟩, ⟨-506155, 5⟩⟩,
  ⟨⟨-126527, 3⟩, ⟨-441753, 6⟩⟩,
  ⟨⟨-55215, 3⟩, ⟨-434017, 7⟩⟩,
  ⟨⟨-433991, 7⟩, ⟨-234183, 7⟩⟩,
  ⟨⟨-468343, 8⟩, ⟨-136297, 7⟩⟩,
  ⟨⟨-136291, 7⟩, ⟨-42195, 6⟩⟩,
  ⟨⟨-337547, 9⟩, ⟨-439983, 10⟩⟩,
  ⟨⟨-13749, 5⟩, ⟨-74827, 8⟩⟩,
  ⟨⟨-299299, 10⟩, ⟨-422259, 11⟩⟩,
  ⟨⟨-52781, 8⟩, ⟨-307211, 11⟩⟩,
  ⟨⟨-307203, 11⟩, ⟨-459053, 12⟩⟩,
  ⟨⟨-459043, 12⟩, ⟨-43869, 9⟩⟩,
  ⟨⟨-350945, 12⟩, ⟨-4277, 6⟩⟩,
  ⟨⟨-273723, 12⟩, ⟨-434539, 13⟩⟩,
  ⟨⟨-108633, 11⟩, ⟨-43785, 10⟩⟩,
  ⟨⟨-350275, 13⟩, ⟨-143117, 12⟩⟩,
  ⟨⟨-286229, 13⟩, ⟨-236747, 13⟩⟩,
  ⟨⟨-473487, 14⟩, ⟨-49485, 11⟩⟩,
  ⟨⟨-395875, 14⟩, ⟨-167099, 13⟩⟩,
  ⟨⟨-334193, 14⟩, ⟨-284583, 14⟩⟩,
  ⟨⟨-71145, 12⟩, ⟨-488453, 15⟩⟩,
  ⟨⟨-488447, 15⟩, ⟨-422139, 15⟩⟩,
  ⟨⟨-211067, 14⟩, ⟨-22947, 11⟩⟩,
  ⟨⟨-91787, 13⟩, ⟨-321167, 15⟩⟩,
  ⟨⟨-321163, 15⟩, ⟨-282407, 15⟩⟩,
  ⟨⟨-70601, 13⟩, ⟨-7797, 10⟩⟩,
  ⟨⟨-499003, 16⟩, ⟨-221385, 15⟩⟩,
  ⟨⟨-221383, 15⟩, ⟨-49301, 13⟩⟩,
  ⟨⟨-98601, 14⟩, ⟨-352579, 16⟩⟩,
  ⟨⟨-352575, 16⟩, ⟨-316207, 16⟩⟩,
  ⟨⟨-79051, 14⟩, ⟨-284421, 16⟩⟩,
  ⟨⟨-142209, 15⟩, ⟨-64129, 14⟩⟩,
  ⟨⟨-128257, 15⟩, ⟨-115955, 15⟩⟩,
  ⟨⟨-57977, 14⟩, ⟨-210123, 16⟩⟩,
  ⟨⟨-420243, 17⟩, ⟨-95381, 15⟩⟩,
  ⟨⟨-23845, 13⟩, ⟨-173493, 16⟩⟩,
  ⟨⟨-346983, 17⟩, ⟨-79019, 15⟩⟩,
  ⟨⟨-316073, 17⟩, ⟨-288329, 17⟩⟩,
  ⟨⟨-288327, 17⟩, ⟨-65837, 15⟩⟩,
  ⟨⟨-131673, 16⟩, ⟨-120397, 16⟩⟩,
  ⟨⟨-481585, 18⟩, ⟨-220379, 17⟩⟩,
  ⟨⟨-220377, 17⟩, ⟨-1577, 10⟩⟩,
  ⟨⟨-403709, 18⟩, ⟨-185011, 17⟩⟩,
  ⟨⟨-370019, 18⟩, ⟨-42415, 15⟩⟩,
  ⟨⟨-169659, 17⟩, ⟨-311287, 18⟩⟩,
  ⟨⟨-77821, 16⟩, ⟨-285643, 18⟩⟩,
  ⟨⟨-285641, 18⟩, ⟨-262145, 18⟩⟩,
  ⟨⟨-524285, 19⟩, ⟨-240581, 18⟩⟩,
  ⟨⟨-240579, 18⟩, ⟨-441523, 19⟩⟩,
  ⟨⟨-27595, 15⟩, ⟨-405045, 19⟩⟩,
  ⟨⟨-202521, 18⟩, ⟨-185719, 18⟩⟩,
  ⟨⟨-371435, 19⟩, ⟨-170221, 18⟩⟩,
  ⟨⟨-42555, 16⟩, ⟨-311827, 19⟩⟩,
  ⟨⟨-19489, 15⟩, ⟨-142695, 18⟩⟩,
  ⟨⟨-285387, 19⟩, ⟨-260947, 19⟩⟩,
  ⟨⟨-260945, 19⟩, ⟨-119169, 18⟩⟩,
  ⟨⟨-476673, 20⟩, ⟨-27177, 16⟩⟩,
  ⟨⟨-108707, 18⟩, ⟨-396099, 20⟩⟩,
  ⟨⟨-6189, 14⟩, ⟨-360239, 20⟩⟩,
  ⟨⟨-90059, 18⟩, ⟨-327045, 20⟩⟩,
  ⟨⟨-163521, 19⟩, ⟨-148161, 19⟩⟩,
  ⟨⟨-296319, 20⟩, ⟨-267899, 20⟩⟩,
  ⟨⟨-33487, 17⟩, ⟨-483227, 21⟩⟩,
  ⟨⟨-483223, 21⟩, ⟨-217327, 20⟩⟩,
  ⟨⟨-217325, 20⟩, ⟨-48727, 18⟩⟩,
  ⟨⟨-389813, 21⟩, ⟨-174237, 20⟩⟩,
  ⟨⟨-174235, 20⟩, ⟨-155205, 20⟩⟩,
  ⟨⟨-310407, 21⟩, ⟨-137713, 20⟩⟩,
  ⟨⟨-275423, 21⟩, ⟨-486673, 22⟩⟩,
  ⟨⟨-121667, 20⟩, ⟨-427941, 22⟩⟩,
  ⟨⟨-427937, 22⟩, ⟨-46793, 19⟩⟩,
  ⟨⟨-93585, 20⟩, ⟨-325581, 22⟩⟩,
  ⟨⟨-325577, 22⟩, ⟨-281381, 22⟩⟩,
  ⟨⟨-281377, 22⟩, ⟨-482957, 23⟩⟩,
  ⟨⟨-482951, 23⟩, ⟨-411253, 23⟩⟩,
  ⟨⟨-25703, 19⟩, ⟨-347179, 23⟩⟩,
  ⟨⟨-173587, 22⟩, ⟨-290269, 23⟩⟩,
  ⟨⟨-290265, 23⟩, ⟨-240085, 23⟩⟩,
  ⟨⟨-120041, 22⟩, ⟨-392375, 24⟩⟩,
  ⟨⟨-196185, 23⟩, ⟨-2471, 17⟩⟩,
  ⟨⟨-316283, 24⟩, ⟨-125527, 23⟩⟩,
  ⟨⟨-125525, 23⟩, ⟨-195815, 24⟩⟩,
  ⟨⟨-391623, 25⟩, ⟨-299403, 25⟩⟩,
  ⟨⟨-299397, 25⟩, ⟨-447383, 26⟩⟩,
  ⟨⟨-223687, 25⟩, ⟨-162745, 25⟩⟩,
  ⟨⟨-325483, 26⟩, ⟨-114801, 25⟩⟩,
  ⟨⟨-229597, 26⟩, ⟨-312385, 27⟩⟩,
  ⟨⟨-312377, 27⟩, ⟨-407173, 28⟩⟩,
  ⟨⟨-203581, 27⟩, ⟨-504199, 29⟩⟩,
  ⟨⟨-63023, 26⟩, ⟨-146725, 28⟩⟩,
  ⟨⟨-4585, 23⟩, ⟨-316685, 30⟩⟩,
  ⟨⟨-158337, 29⟩, ⟨-155567, 30⟩⟩,
  ⟨⟨-311121, 31⟩, ⟨-135777, 31⟩⟩,
  ⟨⟨-135771, 31⟩, ⟨-407055, 34⟩⟩,
  ⟨⟨-407035, 34⟩, ⟨-499343, 36⟩⟩,
  ⟨⟨-124829, 34⟩, ⟨-467079, 38⟩⟩,
  ⟨⟨-467051, 38⟩, ⟨-74715, 38⟩⟩,
  ⟨⟨-37355, 37⟩, ⟨-219561, 43⟩⟩,
  ⟨⟨-439091, 44⟩, ⟨-68407, 46⟩⟩,
  ⟨⟨-273607, 48⟩, ⟨-325717, 55⟩⟩,
  ⟨⟨-325691, 55⟩, ⟨-421937, 66⟩⟩,
  ⟨⟨-210951, 65⟩, ⟨-81489, 83⟩⟩,
  ⟨⟨-325925, 85⟩, ⟨-262165, 132⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private def eulerianCoefficients : List ℤ := [
  0x1, 0x3ffffffffffffffffffffffffff8d, 0x19bc753052157372faa6d868f2d9d94334a7807fb76264,
  0xffffffffff470575b4b205d22f12f0cc8dae82366cf58c146a0a6893c, 0x19fd0fef2ae8dfe2dceb7c4bd7715000aac95790c43bca3f6fa6a473b3ee3d56448, 0x66f1d4067d73452dd0d23310b5eba3c45e99b983719ac35b18f5367b4001c06aa158f754d0,
  0x106ea745d8347f8b112d508729a238b16bb559377112264d00d6c6691f3233b182c84b442c8aa1814, 0x3fff89e4a33fcd3df7b335998b00587200d3b18e232af1ec0a2d5c393007ee1474ce85d9dbd917347725cc, 0x2963cdfdef20ca2bd227ae11ba010bb1084551be0cdc6f78fb343c96c02c190eab56976f47e2b5e5ae328c8869e,
  0x67e1a780b7102e45ca08d7b419af17d2dca338ff646aee682fa947116e468719c5befe36ace2ede0355d3df37455dce, 0x52d3bfeab84e34b2409331c1df2908cb87b53032f11f52d9a108afcb64a44624facca08dc76b3f4718222c7b01c7fc7a05c, 0x1997357dddfeff8b4bb130ed9b84a5098cb6749b13ca6b210ad2be2eceb44a5195adc2d50ed0bcbb1ad2ff2533181f87b44b804,
  0x38f6efae1d35138329f543e64c5c992ae8ea7d9053fba427551f7ebf927dcc672fd878ddfdd99699bcd15556f3242ecd302db8f0b0, 0x401e9dc1af5d8dec5922ba3b21f4341e2a0de33e35eeaacefbdbc39b2ae197eb5321eea59120c9f5f0bc28b77077de7c0d5409fe0d148, 0x27fad61f57cb352785594e24c74190e72207abe85c826a5f1a216a38cab2f50050344fe7a2eedb10b6f4e994656042b9432f96e3f0b09d8c,
  0xeda1051dae69fa4e0aa91a9eaed6a2d37ebac6a822d668e5a25b76dd77ef706bfb5a1109b083fad328dc53ea17f32246d89875d9da8ed44194, 0x37c942268ddd7aadb66f3f70ce3ae3ae8e5939174e02b7c1bdc6c3ad2052efa30537c7a72aa70ac1845e47386f8e52ce4608ecb3dbb8b241bf217, 0x8afa011cbddd415fc79e35385ec3b628ff8dbf3b4c230765e1a02ce5dbf86dffb884c1cac2f5ab94712cecad8e89227b10d64975532dfa798c29b23,
  0xef0194ba76c453732bf093c73059bb1d6615c07be35cab8350103308898752c00ec75b20316902c78a692a8691d9c8526fafb8675c6885da485b62c78, 0x12569f6c2e52b75f77e4d706781c9c25c58436485eebf7db8572a30d985b5854e396c24330baf404968d85ce717a0368f1cd85c0921ace7f24995e5c6a48, 0x10883c90191f783efdf9d2123f63a08a46af8191ad5ab210c0d8e17b51244519bb7d245b5e452a331be5dd7d4542adde9a9b4ea5669ebe56a6d94140267f10,
  0xb3630c82fd6d43b389a6fbba773bb359a0834a8c4bd8ba6dc71a0cccc8f78d514ae6d87e219a088b174160429134e5fef18f960a02441c4e98ef8326b139600, 0x5d6e9b3bbf4e67b0a8939a07852253ea6dd07fc2a2555ee07b0c02c03b3701e319ed5b861e9eda17fdfd32cadcdf2c778f21644ac12a15089bd98956af59c1898, 0x260c800f35d15292ce44965854793870ebf87526db3fa0501929d497ecd4c4958350d52eb884ad100091b3ab2374522dece78879bb7f627fe428132de6cf65191a8,
  0xc4e2b910dad8d1b9ae8d09c9946c83de6c57d9c27630034999ec556c9be5842a02a348b949c42ecc1c8d0a7a8db5fe38ad88be3285a1d75a5f116cffb99742bc4f9c, 0x334326f2cb8cae79ed407b8818ce952033d28503e2c726f7bfee88d897a183bc21a397903e40c5b3b24f20e5cce73e377682c3bece8b205cc1ade0a8c188b3fb03fadc, 0xadffd5f5cf0cdff7364bc21ec1f78f5ab694a14eb8be2b0857ceb630bb43b7f96333f62886e615a29786d43fa0313b55dc3bacb535934310d4fb33346483831fcabdf68,
  0x1e65af9cfb9be4ad844ad6b7a64c7c6b034b77e90ef9e8916bb539cabd1e9be936c754ca7c7f9b39b64f1806ba64487d554555a296607a804db1e1772814bda9ad125e0d8, 0x46a16f4f48b2411d3499803b1992a38a2c2910192744129af46a25ebfdaea6171002ccd45d7309033b64a3c0a6b6dc4edd0104087e694fa6064f180851472b02293e483a80, 0x8994c706086c320b45b1835acde1c0d0cf54d6670b8cdad1630a30ddf33daaa84f83ccc8758de2e28817317dee96ebfe9a8711b8f4d3514e96f187bd47a11c45590fd073f10,
  0xe25c8941b909d4e7daf0331af616bf3354320a7c3e6514423e4db2b3c347976757792355e7c992d3ebf07b5637b1e3176d655b0c426ed8d2c32133e8b641e2d7a4e8181c4108, 0x13cb58d4d17910c7fcb398406b2c85e891f3a71424671951e01a7d459ef10ff60a896e941d326cf7a2bdeee466098cafbbfbca916039be4b6fa1d6bccd161e40560006c1f487b8, 0x17b1f2a15fda65f41d3586f81557a2372d8f6d1beb29b4f9e53058082ae30cb805289a2feaa0df97375e298773b71df4ce2cb88f0dd5b802d78088f97bc5f621812c51a550bd5f1,
  0x1866e7b63ea4f22cf82252ea4a24b4e2af290881475edb2ede408879a3d3f8dc0b93c2fc54e07d4da225f21d648e447e2beca99a2553ca919911208f12f7a514651a3a3d023f1b0d, 0x15ba1f320370603b876ac0818742685cf245345d8018142c78934b17a578efe51952745db1fb502b06a61b0b724c12117487b9a2b99c81b5e8d231f7ddbbaecf8502257c1170533cc, 0x10cd2652dba3726d713db1e5d6ad2601bf90a60175e4af0f58c75758446a0f68934f2a9ff691b8d1bc1b6bbc3de398fdaeda8c69c42b3f65124b68fc67a1f7f5eda5c0dd70b90b3c14,
  0xb5484f71a9c676efbbc89a5b0b333f37910586f0fdf6489c2882611350f3f43093cd98501c3f40116895eb4e99feac1be8c1dca2670b37328ff89b635bd825d4063fe51acdb6aaae38, 0x6b01b63cb33be03a41ccf885e942447b6140c9397420fab496c6ac158be259a922407fada09147f09222e748385888b2424a96149cafc47862d59e685c20288983450ddb53131789490, 0x3779b62a0031b40f780eba58cecff1463e03a7a2aaf4d7650db3773e3b56f8a0776ae96bd4f965288a866ad55bd6ac31b48a0dd47f7e2c05b4e461adcb372ea8bea97a2348b362d3a0dc,
  0x19566669d7789b03e7f382e7820668c42915a5ce32d2e45906fe84fefe5b3eee8b0261d8d01254397c83b0e569b6f668e34bfcfbbe8cb18725059b5dd7f8ec93534048beb121cd68b83c4, 0xa3954363a17340c40f7a1118dabee00e2799d60ce51e444922b9f4062456ca0fe3150155e2e1504f1c5a399b5d8789bfdef2dd2f09ad1e2a06acdd16a3ac3ee06f0af25bb39c37a777332, 0x3a76ef010f684bee149b5701bfd6ac3fba3ffe83500bbea1c1e9a4f425341c1d50e6f8e921860eb6543c97e2acfe4055e4e611a23bf77a845dda992bafc30956db6610c4edf118a9072722,
  0x128cebbccc2c33a007c78205775d63ac4e743e2fd398cca3d9da2ad4d041fbf768b635f10096b3b5bbff1a815449d70ef954fa7a486a6fc67af9333a7664785f165b68184492e9465bd2894, 0x53c89d32398a47225de4deda76efabb7e1dd24ee9dab209e202126f1a6469de97cd9cbed03e1f3f8d8a5263a65de75bac63c2ff19f975e03efd5e6ee958258e920a3c8343d54c85dbf8008c, 0x1514c6ade30925047163925d1a76b3fa9241f9d44316d5b8fcf3eb7a65bbfb162ab7ae923ce1b9bf890346ae5e5c3f6c83a95dba291f136790231a1bc0c6c786588cf944ef5cd09cd80497f0,
  0x4bc76e716b97c0c8013e94f7b50342cc73fecb603c2d2a0407f2d70178aa5c2b3b333d9e2109026ea9c414bfda1d7bf224e8284bdff3c36d4e6fabda5f16c135ca74099b43f9b879eea26738, 0xf3998d4a4317084d0edd79bc6201497915e6806581e86998af800af46d2de9c35e9e9b815e5608e6ae805a9de946de8b25a2c6392f080c6489f0b273b33e95609b8a633c217ed9e1322c41a4, 0x2bd43b86d71cfa6aa5c648738ec56da6150657ac7f59bda4295054725d93db1f29f661d95015b468ffec9b3c711a6c64cb7283f519661af871fbd6b47ff38c0c5095d5c3323579e04268d6fbc,
  0x712184e30f7c070108fa7186de84319f0f847ff018ddb8d0a2bcb362e303e8d9fa7d5b4eec543079a9cd94e0f0271dbdc79a24db1d568a560704938717c4a6b3064b78909978bfd672b5a6dcf, 0x1061d30cf73fccbff104e6f01ffc4fb668062fb4c3325cf2b78e995c4d34f255b1da5006d69ed37642d5e4d9013e1b7bdf1432e106cb6a2e48c14fe61136123edf7df4bec6659fade16354346b, 0x221a30a6d1050058c4b5aa43d0bd8a75c3b87ca62fa1631c1a05e359655a6bb8825a08090b8187154f3c43a94d706cd5903d1aad89010c4f812c96dad173b2d5206b96f3b7ffdefd14bf3ec450,
  0x3fd5cb57291d2957a013bf2abc45ae27f1a1f041c7c14d9545de16218dbb8074533c3d1ed16195c554a1d1e4ef0d2bd367a4f793911514fa8750003f03c26797b99bb6e366582ed6c9d266f030, 0x6b85e4bbe1d6a4e75876c97bbfe36397bd026103df45a670865c55d9c747c19e8806d771316c902e61fddf069e869483cd10626f85a5ef23a860b48a24637b3a6f930ffb23589f94067f11b6e0, 0xa31070e977ddcd80b6860d516beea433021e3dedf5c85f5400354c399498a6932aefdd8555a4917c2515c6a07484234fec4172c23616e83b1873bd24659775506ac6981775fc0b2e8c0933fd80,
  0xdec1916b9785a2fcd6f4251752fd749ccfbe229f58d4ce80d5ef6f013952e8d540387e72766dc323311a50639271536324409d1f4cc63703d490d37d490da4d24b98f9a5e2abc3ea5361155510, 0x11232531410a81d602f7a437efa8363034e7bda79a6d67503cf7f015663fb22760cc63f0db416cd7139c4bea33988695a68060fc0acd799bc41d4c0f762689a0c1c14b2116821a6780659735c70, 0x130323ad31627a328750d3200e60e4827a9b5f6566714e4f830749a2e9f6b369f5c621eec2d63c941225db33e1e1c5b7949f9af1c7a9db20bf547d6e4b1642f7f29752b111eb4b7911c73db16c8,
  0x130323ad31627a328750d3200e60e4827a9b5f6566714e4f830749a2e9f6b369f5c621eec2d63c941225db33e1e1c5b7949f9af1c7a9db20bf547d6e4b1642f7f29752b111eb4b7911c73db16c8, 0x11232531410a81d602f7a437efa8363034e7bda79a6d67503cf7f015663fb22760cc63f0db416cd7139c4bea33988695a68060fc0acd799bc41d4c0f762689a0c1c14b2116821a6780659735c70, 0xdec1916b9785a2fcd6f4251752fd749ccfbe229f58d4ce80d5ef6f013952e8d540387e72766dc323311a50639271536324409d1f4cc63703d490d37d490da4d24b98f9a5e2abc3ea5361155510,
  0xa31070e977ddcd80b6860d516beea433021e3dedf5c85f5400354c399498a6932aefdd8555a4917c2515c6a07484234fec4172c23616e83b1873bd24659775506ac6981775fc0b2e8c0933fd80, 0x6b85e4bbe1d6a4e75876c97bbfe36397bd026103df45a670865c55d9c747c19e8806d771316c902e61fddf069e869483cd10626f85a5ef23a860b48a24637b3a6f930ffb23589f94067f11b6e0, 0x3fd5cb57291d2957a013bf2abc45ae27f1a1f041c7c14d9545de16218dbb8074533c3d1ed16195c554a1d1e4ef0d2bd367a4f793911514fa8750003f03c26797b99bb6e366582ed6c9d266f030,
  0x221a30a6d1050058c4b5aa43d0bd8a75c3b87ca62fa1631c1a05e359655a6bb8825a08090b8187154f3c43a94d706cd5903d1aad89010c4f812c96dad173b2d5206b96f3b7ffdefd14bf3ec450, 0x1061d30cf73fccbff104e6f01ffc4fb668062fb4c3325cf2b78e995c4d34f255b1da5006d69ed37642d5e4d9013e1b7bdf1432e106cb6a2e48c14fe61136123edf7df4bec6659fade16354346b, 0x712184e30f7c070108fa7186de84319f0f847ff018ddb8d0a2bcb362e303e8d9fa7d5b4eec543079a9cd94e0f0271dbdc79a24db1d568a560704938717c4a6b3064b78909978bfd672b5a6dcf,
  0x2bd43b86d71cfa6aa5c648738ec56da6150657ac7f59bda4295054725d93db1f29f661d95015b468ffec9b3c711a6c64cb7283f519661af871fbd6b47ff38c0c5095d5c3323579e04268d6fbc, 0xf3998d4a4317084d0edd79bc6201497915e6806581e86998af800af46d2de9c35e9e9b815e5608e6ae805a9de946de8b25a2c6392f080c6489f0b273b33e95609b8a633c217ed9e1322c41a4, 0x4bc76e716b97c0c8013e94f7b50342cc73fecb603c2d2a0407f2d70178aa5c2b3b333d9e2109026ea9c414bfda1d7bf224e8284bdff3c36d4e6fabda5f16c135ca74099b43f9b879eea26738,
  0x1514c6ade30925047163925d1a76b3fa9241f9d44316d5b8fcf3eb7a65bbfb162ab7ae923ce1b9bf890346ae5e5c3f6c83a95dba291f136790231a1bc0c6c786588cf944ef5cd09cd80497f0, 0x53c89d32398a47225de4deda76efabb7e1dd24ee9dab209e202126f1a6469de97cd9cbed03e1f3f8d8a5263a65de75bac63c2ff19f975e03efd5e6ee958258e920a3c8343d54c85dbf8008c, 0x128cebbccc2c33a007c78205775d63ac4e743e2fd398cca3d9da2ad4d041fbf768b635f10096b3b5bbff1a815449d70ef954fa7a486a6fc67af9333a7664785f165b68184492e9465bd2894,
  0x3a76ef010f684bee149b5701bfd6ac3fba3ffe83500bbea1c1e9a4f425341c1d50e6f8e921860eb6543c97e2acfe4055e4e611a23bf77a845dda992bafc30956db6610c4edf118a9072722, 0xa3954363a17340c40f7a1118dabee00e2799d60ce51e444922b9f4062456ca0fe3150155e2e1504f1c5a399b5d8789bfdef2dd2f09ad1e2a06acdd16a3ac3ee06f0af25bb39c37a777332, 0x19566669d7789b03e7f382e7820668c42915a5ce32d2e45906fe84fefe5b3eee8b0261d8d01254397c83b0e569b6f668e34bfcfbbe8cb18725059b5dd7f8ec93534048beb121cd68b83c4,
  0x3779b62a0031b40f780eba58cecff1463e03a7a2aaf4d7650db3773e3b56f8a0776ae96bd4f965288a866ad55bd6ac31b48a0dd47f7e2c05b4e461adcb372ea8bea97a2348b362d3a0dc, 0x6b01b63cb33be03a41ccf885e942447b6140c9397420fab496c6ac158be259a922407fada09147f09222e748385888b2424a96149cafc47862d59e685c20288983450ddb53131789490, 0xb5484f71a9c676efbbc89a5b0b333f37910586f0fdf6489c2882611350f3f43093cd98501c3f40116895eb4e99feac1be8c1dca2670b37328ff89b635bd825d4063fe51acdb6aaae38,
  0x10cd2652dba3726d713db1e5d6ad2601bf90a60175e4af0f58c75758446a0f68934f2a9ff691b8d1bc1b6bbc3de398fdaeda8c69c42b3f65124b68fc67a1f7f5eda5c0dd70b90b3c14, 0x15ba1f320370603b876ac0818742685cf245345d8018142c78934b17a578efe51952745db1fb502b06a61b0b724c12117487b9a2b99c81b5e8d231f7ddbbaecf8502257c1170533cc, 0x1866e7b63ea4f22cf82252ea4a24b4e2af290881475edb2ede408879a3d3f8dc0b93c2fc54e07d4da225f21d648e447e2beca99a2553ca919911208f12f7a514651a3a3d023f1b0d,
  0x17b1f2a15fda65f41d3586f81557a2372d8f6d1beb29b4f9e53058082ae30cb805289a2feaa0df97375e298773b71df4ce2cb88f0dd5b802d78088f97bc5f621812c51a550bd5f1, 0x13cb58d4d17910c7fcb398406b2c85e891f3a71424671951e01a7d459ef10ff60a896e941d326cf7a2bdeee466098cafbbfbca916039be4b6fa1d6bccd161e40560006c1f487b8, 0xe25c8941b909d4e7daf0331af616bf3354320a7c3e6514423e4db2b3c347976757792355e7c992d3ebf07b5637b1e3176d655b0c426ed8d2c32133e8b641e2d7a4e8181c4108,
  0x8994c706086c320b45b1835acde1c0d0cf54d6670b8cdad1630a30ddf33daaa84f83ccc8758de2e28817317dee96ebfe9a8711b8f4d3514e96f187bd47a11c45590fd073f10, 0x46a16f4f48b2411d3499803b1992a38a2c2910192744129af46a25ebfdaea6171002ccd45d7309033b64a3c0a6b6dc4edd0104087e694fa6064f180851472b02293e483a80, 0x1e65af9cfb9be4ad844ad6b7a64c7c6b034b77e90ef9e8916bb539cabd1e9be936c754ca7c7f9b39b64f1806ba64487d554555a296607a804db1e1772814bda9ad125e0d8,
  0xadffd5f5cf0cdff7364bc21ec1f78f5ab694a14eb8be2b0857ceb630bb43b7f96333f62886e615a29786d43fa0313b55dc3bacb535934310d4fb33346483831fcabdf68, 0x334326f2cb8cae79ed407b8818ce952033d28503e2c726f7bfee88d897a183bc21a397903e40c5b3b24f20e5cce73e377682c3bece8b205cc1ade0a8c188b3fb03fadc, 0xc4e2b910dad8d1b9ae8d09c9946c83de6c57d9c27630034999ec556c9be5842a02a348b949c42ecc1c8d0a7a8db5fe38ad88be3285a1d75a5f116cffb99742bc4f9c,
  0x260c800f35d15292ce44965854793870ebf87526db3fa0501929d497ecd4c4958350d52eb884ad100091b3ab2374522dece78879bb7f627fe428132de6cf65191a8, 0x5d6e9b3bbf4e67b0a8939a07852253ea6dd07fc2a2555ee07b0c02c03b3701e319ed5b861e9eda17fdfd32cadcdf2c778f21644ac12a15089bd98956af59c1898, 0xb3630c82fd6d43b389a6fbba773bb359a0834a8c4bd8ba6dc71a0cccc8f78d514ae6d87e219a088b174160429134e5fef18f960a02441c4e98ef8326b139600,
  0x10883c90191f783efdf9d2123f63a08a46af8191ad5ab210c0d8e17b51244519bb7d245b5e452a331be5dd7d4542adde9a9b4ea5669ebe56a6d94140267f10, 0x12569f6c2e52b75f77e4d706781c9c25c58436485eebf7db8572a30d985b5854e396c24330baf404968d85ce717a0368f1cd85c0921ace7f24995e5c6a48, 0xef0194ba76c453732bf093c73059bb1d6615c07be35cab8350103308898752c00ec75b20316902c78a692a8691d9c8526fafb8675c6885da485b62c78,
  0x8afa011cbddd415fc79e35385ec3b628ff8dbf3b4c230765e1a02ce5dbf86dffb884c1cac2f5ab94712cecad8e89227b10d64975532dfa798c29b23, 0x37c942268ddd7aadb66f3f70ce3ae3ae8e5939174e02b7c1bdc6c3ad2052efa30537c7a72aa70ac1845e47386f8e52ce4608ecb3dbb8b241bf217, 0xeda1051dae69fa4e0aa91a9eaed6a2d37ebac6a822d668e5a25b76dd77ef706bfb5a1109b083fad328dc53ea17f32246d89875d9da8ed44194,
  0x27fad61f57cb352785594e24c74190e72207abe85c826a5f1a216a38cab2f50050344fe7a2eedb10b6f4e994656042b9432f96e3f0b09d8c, 0x401e9dc1af5d8dec5922ba3b21f4341e2a0de33e35eeaacefbdbc39b2ae197eb5321eea59120c9f5f0bc28b77077de7c0d5409fe0d148, 0x38f6efae1d35138329f543e64c5c992ae8ea7d9053fba427551f7ebf927dcc672fd878ddfdd99699bcd15556f3242ecd302db8f0b0,
  0x1997357dddfeff8b4bb130ed9b84a5098cb6749b13ca6b210ad2be2eceb44a5195adc2d50ed0bcbb1ad2ff2533181f87b44b804, 0x52d3bfeab84e34b2409331c1df2908cb87b53032f11f52d9a108afcb64a44624facca08dc76b3f4718222c7b01c7fc7a05c, 0x67e1a780b7102e45ca08d7b419af17d2dca338ff646aee682fa947116e468719c5befe36ace2ede0355d3df37455dce,
  0x2963cdfdef20ca2bd227ae11ba010bb1084551be0cdc6f78fb343c96c02c190eab56976f47e2b5e5ae328c8869e, 0x3fff89e4a33fcd3df7b335998b00587200d3b18e232af1ec0a2d5c393007ee1474ce85d9dbd917347725cc, 0x106ea745d8347f8b112d508729a238b16bb559377112264d00d6c6691f3233b182c84b442c8aa1814,
  0x66f1d4067d73452dd0d23310b5eba3c45e99b983719ac35b18f5367b4001c06aa158f754d0, 0x19fd0fef2ae8dfe2dceb7c4bd7715000aac95790c43bca3f6fa6a473b3ee3d56448, 0xffffffffff470575b4b205d22f12f0cc8dae82366cf58c146a0a6893c,
  0x19bc753052157372faa6d868f2d9d94334a7807fb76264, 0x3ffffffffffffffffffffffffff8d, 0x1]

private theorem eulerianCoefficients_eq : descentCoeffs 114 = eulerianCoefficients := by
  decide +kernel

private theorem upper : upperOK (descentCoeffs 114) first gaps = true := by
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

private theorem lower (i : Fin (lastRepresentative 115 - 2)) :
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

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 115) :
    StrictNegativeInterlacing (originalQuotient 115 k) (eulerian 114) 112 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N115
