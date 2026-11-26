import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentPackedData.C127L112.N111

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N111

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L112.N111 LongCycleBounds.DescentNecklace.Packed.C127L112.N111.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L112.N111 LongCycleBounds.DescentNecklace.Packed.C127L112.N111.rows

private theorem actual : RepresentativeChecks 111 previousNodes rows :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L112.N111 LongCycleBounds.DescentNecklace.Packed.C127L112.N111.dataChecks

private def first : LongCycleFinite.Dyadic := ⟨-1298074214633706907132624082305024, 0⟩

private def gaps : List Window := [
  ⟨⟨-1298032124672371204203277512081408, 0⟩, ⟨-23455520915531497472, 0⟩⟩,
  ⟨⟨-23419421749768355840, 0⟩, ⟨-55660091801600, 0⟩⟩,
  ⟨⟨-54727949680640, 0⟩, ⟨-46210875392, 0⟩⟩,
  ⟨⟨-43668996096, 0⟩, ⟨-495980544, 0⟩⟩,
  ⟨⟨-493804544, 0⟩, ⟨-21506240, 0⟩⟩,
  ⟨⟨-21482176, 0⟩, ⟨-2141992, 0⟩⟩,
  ⟨⟨-2140976, 0⟩, ⟨-364370, 0⟩⟩,
  ⟨⟨-364274, 0⟩, ⟨-89441, 0⟩⟩,
  ⟨⟨-89426, 0⟩, ⟨-456365, 4⟩⟩,
  ⟨⟨-456311, 4⟩, ⟨-353151, 5⟩⟩,
  ⟨⟨-353119, 5⟩, ⟨-316577, 6⟩⟩,
  ⟨⟨-158277, 5⟩, ⟨-79533, 5⟩⟩,
  ⟨⟨-159057, 6⟩, ⟨-175005, 7⟩⟩,
  ⟨⟨-349993, 8⟩, ⟨-207129, 8⟩⟩,
  ⟨⟨-414241, 9⟩, ⟨-520461, 10⟩⟩,
  ⟨⟨-260221, 9⟩, ⟨-343513, 10⟩⟩,
  ⟨⟨-343501, 10⟩, ⟨-236305, 10⟩⟩,
  ⟨⟨-472597, 11⟩, ⟨-84171, 9⟩⟩,
  ⟨⟨-336675, 11⟩, ⟨-123555, 10⟩⟩,
  ⟨⟨-494209, 12⟩, ⟨-372143, 12⟩⟩,
  ⟨⟨-372135, 12⟩, ⟨-71625, 10⟩⟩,
  ⟨⟨-143247, 11⟩, ⟨-449719, 13⟩⟩,
  ⟨⟨-449711, 13⟩, ⟨-179485, 12⟩⟩,
  ⟨⟨-89741, 11⟩, ⟨-290823, 13⟩⟩,
  ⟨⟨-145409, 12⟩, ⟨-477445, 14⟩⟩,
  ⟨⟨-238719, 13⟩, ⟨-396501, 14⟩⟩,
  ⟨⟨-396495, 14⟩, ⟨-332715, 14⟩⟩,
  ⟨⟨-166355, 13⟩, ⟨-70447, 12⟩⟩,
  ⟨⟨-35223, 11⟩, ⟨-240647, 14⟩⟩,
  ⟨⟨-481289, 15⟩, ⟨-414105, 15⟩⟩,
  ⟨⟨-103525, 13⟩, ⟨-44837, 12⟩⟩,
  ⟨⟨-89673, 13⟩, ⟨-312593, 15⟩⟩,
  ⟨⟨-312589, 15⟩, ⟨-273911, 15⟩⟩,
  ⟨⟨-273907, 15⟩, ⟨-482421, 16⟩⟩,
  ⟨⟨-30151, 12⟩, ⟨-426739, 16⟩⟩,
  ⟨⟨-426735, 16⟩, ⟨-23689, 12⟩⟩,
  ⟨⟨-379021, 16⟩, ⟨-337893, 16⟩⟩,
  ⟨⟨-337889, 16⟩, ⟨-302231, 16⟩⟩,
  ⟨⟨-75557, 14⟩, ⟨-271155, 16⟩⟩,
  ⟨⟨-271153, 16⟩, ⟨-243943, 16⟩⟩,
  ⟨⟨-243941, 16⟩, ⟨-440009, 17⟩⟩,
  ⟨⟨-220003, 16⟩, ⟨-397719, 17⟩⟩,
  ⟨⟨-397715, 17⟩, ⟨-360213, 17⟩⟩,
  ⟨⟨-360209, 17⟩, ⟨-326827, 17⟩⟩,
  ⟨⟨-40853, 14⟩, ⟨-18563, 13⟩⟩,
  ⟨⟨-297005, 17⟩, ⟨-270287, 17⟩⟩,
  ⟨⟨-67571, 15⟩, ⟨-123135, 16⟩⟩,
  ⟨⟨-492537, 18⟩, ⟨-14039, 13⟩⟩,
  ⟨⟨-449245, 18⟩, ⟨-410127, 18⟩⟩,
  ⟨⟨-102531, 16⟩, ⟨-187343, 17⟩⟩,
  ⟨⟨-374683, 18⟩, ⟨-342505, 18⟩⟩,
  ⟨⟨-171251, 17⟩, ⟨-313225, 18⟩⟩,
  ⟨⟨-156611, 17⟩, ⟨-286529, 18⟩⟩,
  ⟨⟨-143263, 17⟩, ⟨-131073, 17⟩⟩,
  ⟨⟨-524287, 19⟩, ⟨-59959, 16⟩⟩,
  ⟨⟨-479669, 19⟩, ⟨-438791, 19⟩⟩,
  ⟨⟨-109697, 17⟩, ⟨-401279, 19⟩⟩,
  ⟨⟨-100319, 17⟩, ⟨-366815, 19⟩⟩,
  ⟨⟨-91703, 17⟩, ⟨-83779, 17⟩⟩,
  ⟨⟨-335113, 19⟩, ⟨-305933, 19⟩⟩,
  ⟨⟨-152965, 18⟩, ⟨-279043, 19⟩⟩,
  ⟨⟨-279041, 19⟩, ⟨-31781, 16⟩⟩,
  ⟨⟨-127123, 18⟩, ⟨-231375, 19⟩⟩,
  ⟨⟨-462747, 20⟩, ⟨-420527, 20⟩⟩,
  ⟨⟨-105131, 18⟩, ⟨-23847, 16⟩⟩,
  ⟨⟨-95387, 18⟩, ⟨-345571, 20⟩⟩,
  ⟨⟨-10799, 15⟩, ⟨-312357, 20⟩⟩,
  ⟨⟨-156177, 19⟩, ⟨-140853, 19⟩⟩,
  ⟨⟨-281703, 20⟩, ⟨-126717, 19⟩⟩,
  ⟨⟨-31679, 17⟩, ⟨-454751, 21⟩⟩,
  ⟨⟨-454747, 21⟩, ⟨-203379, 20⟩⟩,
  ⟨⟨-203377, 20⟩, ⟨-181307, 20⟩⟩,
  ⟨⟨-181305, 20⟩, ⟨-161035, 20⟩⟩,
  ⟨⟨-322067, 21⟩, ⟨-284897, 21⟩⟩,
  ⟨⟨-142447, 20⟩, ⟨-250885, 21⟩⟩,
  ⟨⟨-501765, 22⟩, ⟨-439679, 22⟩⟩,
  ⟨⟨-219837, 21⟩, ⟨-383165, 22⟩⟩,
  ⟨⟨-383161, 22⟩, ⟨-82975, 20⟩⟩,
  ⟨⟨-41487, 19⟩, ⟨-285565, 22⟩⟩,
  ⟨⟨-285561, 22⟩, ⟨-487745, 23⟩⟩,
  ⟨⟨-487739, 23⟩, ⟨-206545, 22⟩⟩,
  ⟨⟨-413085, 23⟩, ⟨-346633, 23⟩⟩,
  ⟨⟨-346629, 23⟩, ⟨-71967, 21⟩⟩,
  ⟨⟨-35983, 20⟩, ⟨-472597, 24⟩⟩,
  ⟨⟨-236295, 23⟩, ⟨-95719, 22⟩⟩,
  ⟨⟨-191435, 23⟩, ⟨-152809, 23⟩⟩,
  ⟨⟨-76403, 22⟩, ⟨-479731, 25⟩⟩,
  ⟨⟨-479723, 25⟩, ⟨-184661, 24⟩⟩,
  ⟨⟨-369315, 25⟩, ⟨-69525, 23⟩⟩,
  ⟨⟨-139047, 24⟩, ⟨-204113, 25⟩⟩,
  ⟨⟨-408217, 26⟩, ⟨-71, 14⟩⟩,
  ⟨⟨-290809, 26⟩, ⟨-400105, 27⟩⟩,
  ⟨⟨-400095, 27⟩, ⟨-66021, 25⟩⟩,
  ⟨⟨-66019, 25⟩, ⟨-331783, 28⟩⟩,
  ⟨⟨-331773, 28⟩, ⟨-24543, 25⟩⟩,
  ⟨⟨-98169, 27⟩, ⟨-432041, 30⟩⟩,
  ⟨⟨-216013, 29⟩, ⟨-434165, 31⟩⟩,
  ⟨⟨-108537, 29⟩, ⟨-194593, 31⟩⟩,
  ⟨⟨-389169, 32⟩, ⟨-301193, 33⟩⟩,
  ⟨⟨-150589, 32⟩, ⟨-384197, 35⟩⟩,
  ⟨⟨-24011, 31⟩, ⟨-377203, 37⟩⟩,
  ⟨⟨-94295, 35⟩, ⟨-513447, 40⟩⟩,
  ⟨⟨-256707, 39⟩, ⟨-409011, 43⟩⟩,
  ⟨⟨-204491, 42⟩, ⟨-71191, 45⟩⟩,
  ⟨⟨-142371, 46⟩, ⟨-99553, 52⟩⟩,
  ⟨⟨-99545, 52⟩, ⟨-333463, 64⟩⟩,
  ⟨⟨-333435, 64⟩, ⟨-412563, 83⟩⟩,
  ⟨⟨-103131, 81⟩, ⟨-262165, 128⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private def eulerianCoefficients : List ℤ := [
  0x1, 0x3fffffffffffffffffffffffff91, 0x5156c7b52959eb35b6ff82e03b9410a1d5d22dd2f2d2,
  0xfffffffffdcbb5f68731202fda3a73640c62accc9d449de218fab92, 0xaa51823744a7eedec4df0570e8e6f571015430cac41c3f662a6353c41d2ed307, 0x1455b1a370ff035918ef4e22e7f3e307ee0f2f9391cd11c5e22742e346cdb7f23702c757,
  0x1c08598dc0be7fa274a64a84b7abdbe8aaef2f4a4bc359aef3f5820e76f67069cae7869abc744c, 0x3fff3d85f3dc8a9bd9cbc0d993beb2e180bc8882cdbcc6b0ae4c58c8b3aa9d2e81add9c7704d0e3724c, 0x19d64bce0a3182e6faad77453bb7bf5cdf06936dbcc3041666710a72a154140e39b6afbe512249c2fa0d001b,
  0x2a892c438f968bfa9139a3d4b77ad54b9a93be0c175462ab15f4990c0f1db292df41d67fecc658d25b9448c0a20b, 0x17269df5624ba2ed36256a7af92a0539482d482b8e9481b4f5de2282aca31bc82c2e6dca26ba020de37197f138d2885a, 0x50b5eb3a6252e4c758d44aa7d53c60c3b8f715185521fc3211b606798edc2d7cc97f4497bf824b4e0a79751dfb0123d5e9a,
  0x822b1a67c98b729477f0a737feffeabc7cef12344a0ae7fe46361f9d49c2c71399ce0636991d4ad0e884a33c2fae06b80d5dad, 0x6c92d186d2fd3b30badb158f017f6efce1a559eadd6d145b3ecb2725e7dde888f12f09302eaa81488cc85083f31678dc03bb8c35d, 0x331fe13254d65111079965b6edfd403439b270539104efb354779f833b7c2528431cb9003f66c279e143279fec08083e1a9c005a3db0,
  0xe92e957e930c8977354da8dc95c310673b66b4ef79b9435adefa49ed4d0eb1e60cdd708a2c4e1d987b727c9af36436b332ab2ae5bdc1b0, 0x2a953bf7df2c63ddbcb749d14d0aa6932ef02c6625f050c3a7bf6c588e61de936a1dff5ffc2ad457705073274a1908403157bc090a855557e, 0x537bf51ef672a83fc47df1d5118d8361c76a5f3b9457bd5cb10622a4ba51ae5a9f64651ae36d194a46fe9bc6ad02f83993cf3585aa8282c295e,
  0x721d61f62e9bca30bb6d57c4e01ba1821518c47579be11bebb4254160d12e6ac047e7a34df29dff316bf32e8b543e002c15a6ec41a7777f9fa7ac, 0x704d9f64300aae691f68727b64327efb30f974998d83d5e55091dadc3a2c6d705510b6062df433959bda3025c43fb9eb8e247da92bc7c8c2504ea2c, 0x51c241ed5114a3a2c3ee64570037ff2c25775575fde0ec388392b39e353fbc3ca10ee2463a68480bed75ec82137d65c74d2915ed86a006ad856c5a472,
  0x2d0fbb67c2097710bde02483fa8d91910e89afbaa804146834a4f24d1f17be1020b8d97c3403b0d4b852c659e4ad82ab252264fe22a14823d45a37810d2, 0x132dc59b8e3d6aa20678a624029d4921bf6612296b4a793308cb52108fe2c8880560f26c0b5b3437b5195d23bbc3012363824438b133d04646e1e38727518, 0x669a0e3947bd9ec381ae7d250a12e0b85c40856c2e2cc9e4473f7ee86a12c7cb5b7605437861af9c79ebb4f1dd876405ff5f5719cac108b1eeab7684e29d18,
  0x1b5b1dd209563977f0314833dd0cbf5c23a049c01fa303a574f9aa73c9b0535a8ab1be4a3a63632706261f6466cdb2d6637c5dd017421a0bbcb5fc744b71c3c2, 0x5e482bf8f5cae26f5de0a01b181facc9bc0442d49ac5131f96922435ad8c45c98ebe76881141417c97d6e10fd557a01473897bca35af92fe431b76275b1309e62, 0x1098f62849d943849983c190109f920d70270c4a5ef76ad12f192768dedaee6f9d558efc65fc7b70980a22595160a59dc7fca65c960fc27a0c498321655f2c2430c,
  0x2698d3b45e83528af8c6758f13315752d7a387747a408fd4e197556c4e6cda1c0faaaf42a9350d1fd201f7a3d770f77ebe9cb9e71f300f99f2a1233d8c9f1895848c, 0x4ac6c0638bacf738d926f716af5a7240d990bf70a7d1a037c67009dbfaec449c023397f59e960333526f5e5431a3838526d5b4e3117ccc1a89899ba7dfa7563c4aeee, 0x79aaea735f80053b980cf737820a43200343e2ee2eba78fabecbc73f5ca6d03a0385ea0a23380a27059fb8d432f03a51e8c0303c36cf92b0c46f4c80cf03590a1ca60e,
  0xa7763cc65d00fb2b243947f156d5b1574bbc8615e0b55fbdf7ce6f22ae462d46c7ca7e507697ef7529f3a70615c06812e2beef406d49deccea04da21fd3b2c694237af0, 0xc43e74c69ddb5ac6f623c355c3162409842dc46ff68f9b89ca9a28c603bd67eaf6e4a51fbf246be845bba2ecb369b13bf7d7c1de7b6eed9f0cedbd95ebd738360c1126f0, 0xc4f1d5d5c66f1da3e43a9a51c6f66a491e89c660d3346822f483f21a7ef1c919266e48ce8be7db6509c58a8a70b36f188b98dbf861f15d0a8653ce59d284cb6014b8b0c5b,
  0xaa272a2eab86d0de5df73b930fd52fd18506356e94664e8db30f53f961013b4d13e2d28f8ad31cd3aa83c8fa066f2ecab1c652adc3a3fb9dd6e054435da52a6d36a1040b8b, 0x7f285cbc78f61163f92c9a0b487abd61a344ecdfc888f3eb760d6adb8a8efe15b30a4c1f38e7b93a877da8078ecefa66096500adae49e7b807c25e7e75a617f7ff8a66ba1b6, 0x528cd39070ebf3be7089f853450037fff64cd7cbf1f68ff9811c50303c06715f56e84e9b9dcb5a29800275b30c45b77439e7421838fd54e26ac73951fa814393844d30e909f6,
  0x2ebc7d04ebe942175618677565dcbcbd091f74b3520c015e4d4012b224dfc8400816ed47a5cce10e8787afbe811c980b5c412f3a001aa32e5c2c976bf27acd1b76b27be96d6fd, 0x17283739f702dab329e1c5dbe107f320d21b8ce11a504cbad2128729b0b6901b656a1ddf3c415fdedd23c29a9e379c2856d9fde944a261f15ac75ebf214df30e8b8542311fa86d, 0xa12e9c0b07f1c2d1d9fd250093d5bf6525b348ec2aac3b11a91f729b704f0b0a7352664e5213c8c74053a52d6989d132efdab647d41f437347edf84e857ebbea2920ddb1c24ef4,
  0x3dbda7e28ade348a9b618a930179fa9755b3c98850dcc80400415a09a45e9a95f058a0fc55eb6f0b72a3369240f19eec61d795dfaabf4f41ed03f55de98cba50d85d07cf48f04f4, 0x14e1135aabd80066f5abfaef01d6411bc3460d294c6e8a8e63ce3e0b83d8da6341b6fa71b446f00b3b677ade0cc449440398ad80556f01083c172fa4cd2c5b5a61a97854bc33e441, 0x63f9d004936e89ddce77ebb401db0b682507f549af6c1fd20dbb7601664dc2940a8fba1b095ea318d0bcb248168068ae66592e609f5b826517a7707beb5cb0a23c7051eda0448211,
  0x1a88d47ae96b61d5bb125ff5c7d3e923005b2ddd04274526516961126ce03b7ad620ad7045451af084102399aa125291b4f0bf04026058cf580cd83c08f5e17e4ad3c305aa19419de, 0x642013b3cb9d64c36b2e7d06d4f2ab335506ab220d080a90041b6f074156acaa40bde6959c6b66c3d99003483c3d11cf3301f1bfdadf5959ed19c988164e610e7c2f8c55ac7abfc9e, 0x1504daba2c7c51577756b8439beaed63daea89105fa732f05bf048d737f7bc4e56af8c1d8a6739b62797e2af1e4fdf4c039e8ceb3118e822570826818dc98cd8cb5157faf81f8fba17,
  0x3ef0c3e92dc0cb12f4cbfa0ddf23e40d8672aab0730c2dd7da0e25b67be9723195367e4d405d8e22ace852d4d3c23195f2e13a2e57e75999c39a5dc3025b6a0999c242a119175eb527, 0xa842b23383eccb1e25c30b8b6b6da039a254a870fa7c36c5be61863648419e867f8b3d63c9708561528969ff8e0491fdd10188a0fdf38c0f251c63434d43af80fe68bb5e2a789d0b60, 0x1921133c5af966fbe8ab880fd027c8faccb511fc7b800fe7807539d8037a74ca2e12b0fea67b1f4aeddd4b3638579ea7002769e71c01a1c273fceef2e4b88f563730c529256699e7360,
  0x35bb126935d24c48f236acedf42323e806d305d54ecfcdebbdfc7d4b60d7bcf24d52390a8200eb84f0be8c2f692fbb2d1be3c054239b52708220b6b020f97eb1efbd3d50bc958b80f94, 0x66e5204bfaa895ab0a4c251bdac11e160ba890d557760791503435547f643ca3b6c64d5c1f3135af26396922e86f21735873967759f9978a273067f758784efca7e06284384e1c594d4, 0xb09dc6e42c67d3329a568e9653134f02ef196275ba7d65321a1b5c62ddbffedabee6dd9a418e267322f8b4700360464941a71b8ed7ba88de106efd987bd256fac91d1ea233fa09ce408,
  0x10fe69c9221b6a0068177e18637cd18313e72db6742760419ffe517020899ee3ac563ec19e82c9e133918f2b85d59d027047b29a955795ff3a39d7629e096b44a3a1a4d3095c485f7b08, 0x1779fe82ab4cfd2b5a2a8aab8d0e839a4ac7b907ae9871f40bc3e10739de607f066624e7cf00379013d2a2b413ff963c9f78df2c140c449b28dc23d3cdd7029550d51dce30212ce75f0c, 0x1d1d3ff6c27f4de16a47e20fb853cbe4e39bce2ebf54ccb9f87dd5dfb02777ebca566548d7a0209bbcbb9231cae5e331f3ea94302b50dde5251b25e7d6b3ea308116b057f9b768e6474c,
  0x206b8bcdd03eacabe7e0c37b6b5c1f359d06c45e4f0529400314111eb554c326637cc9b48647764b9a59d9511681ce4e3b46feae9ce0d6096c32ff1743d6354c89e17160705f54319350, 0x206b8bcdd03eacabe7e0c37b6b5c1f359d06c45e4f0529400314111eb554c326637cc9b48647764b9a59d9511681ce4e3b46feae9ce0d6096c32ff1743d6354c89e17160705f54319350, 0x1d1d3ff6c27f4de16a47e20fb853cbe4e39bce2ebf54ccb9f87dd5dfb02777ebca566548d7a0209bbcbb9231cae5e331f3ea94302b50dde5251b25e7d6b3ea308116b057f9b768e6474c,
  0x1779fe82ab4cfd2b5a2a8aab8d0e839a4ac7b907ae9871f40bc3e10739de607f066624e7cf00379013d2a2b413ff963c9f78df2c140c449b28dc23d3cdd7029550d51dce30212ce75f0c, 0x10fe69c9221b6a0068177e18637cd18313e72db6742760419ffe517020899ee3ac563ec19e82c9e133918f2b85d59d027047b29a955795ff3a39d7629e096b44a3a1a4d3095c485f7b08, 0xb09dc6e42c67d3329a568e9653134f02ef196275ba7d65321a1b5c62ddbffedabee6dd9a418e267322f8b4700360464941a71b8ed7ba88de106efd987bd256fac91d1ea233fa09ce408,
  0x66e5204bfaa895ab0a4c251bdac11e160ba890d557760791503435547f643ca3b6c64d5c1f3135af26396922e86f21735873967759f9978a273067f758784efca7e06284384e1c594d4, 0x35bb126935d24c48f236acedf42323e806d305d54ecfcdebbdfc7d4b60d7bcf24d52390a8200eb84f0be8c2f692fbb2d1be3c054239b52708220b6b020f97eb1efbd3d50bc958b80f94, 0x1921133c5af966fbe8ab880fd027c8faccb511fc7b800fe7807539d8037a74ca2e12b0fea67b1f4aeddd4b3638579ea7002769e71c01a1c273fceef2e4b88f563730c529256699e7360,
  0xa842b23383eccb1e25c30b8b6b6da039a254a870fa7c36c5be61863648419e867f8b3d63c9708561528969ff8e0491fdd10188a0fdf38c0f251c63434d43af80fe68bb5e2a789d0b60, 0x3ef0c3e92dc0cb12f4cbfa0ddf23e40d8672aab0730c2dd7da0e25b67be9723195367e4d405d8e22ace852d4d3c23195f2e13a2e57e75999c39a5dc3025b6a0999c242a119175eb527, 0x1504daba2c7c51577756b8439beaed63daea89105fa732f05bf048d737f7bc4e56af8c1d8a6739b62797e2af1e4fdf4c039e8ceb3118e822570826818dc98cd8cb5157faf81f8fba17,
  0x642013b3cb9d64c36b2e7d06d4f2ab335506ab220d080a90041b6f074156acaa40bde6959c6b66c3d99003483c3d11cf3301f1bfdadf5959ed19c988164e610e7c2f8c55ac7abfc9e, 0x1a88d47ae96b61d5bb125ff5c7d3e923005b2ddd04274526516961126ce03b7ad620ad7045451af084102399aa125291b4f0bf04026058cf580cd83c08f5e17e4ad3c305aa19419de, 0x63f9d004936e89ddce77ebb401db0b682507f549af6c1fd20dbb7601664dc2940a8fba1b095ea318d0bcb248168068ae66592e609f5b826517a7707beb5cb0a23c7051eda0448211,
  0x14e1135aabd80066f5abfaef01d6411bc3460d294c6e8a8e63ce3e0b83d8da6341b6fa71b446f00b3b677ade0cc449440398ad80556f01083c172fa4cd2c5b5a61a97854bc33e441, 0x3dbda7e28ade348a9b618a930179fa9755b3c98850dcc80400415a09a45e9a95f058a0fc55eb6f0b72a3369240f19eec61d795dfaabf4f41ed03f55de98cba50d85d07cf48f04f4, 0xa12e9c0b07f1c2d1d9fd250093d5bf6525b348ec2aac3b11a91f729b704f0b0a7352664e5213c8c74053a52d6989d132efdab647d41f437347edf84e857ebbea2920ddb1c24ef4,
  0x17283739f702dab329e1c5dbe107f320d21b8ce11a504cbad2128729b0b6901b656a1ddf3c415fdedd23c29a9e379c2856d9fde944a261f15ac75ebf214df30e8b8542311fa86d, 0x2ebc7d04ebe942175618677565dcbcbd091f74b3520c015e4d4012b224dfc8400816ed47a5cce10e8787afbe811c980b5c412f3a001aa32e5c2c976bf27acd1b76b27be96d6fd, 0x528cd39070ebf3be7089f853450037fff64cd7cbf1f68ff9811c50303c06715f56e84e9b9dcb5a29800275b30c45b77439e7421838fd54e26ac73951fa814393844d30e909f6,
  0x7f285cbc78f61163f92c9a0b487abd61a344ecdfc888f3eb760d6adb8a8efe15b30a4c1f38e7b93a877da8078ecefa66096500adae49e7b807c25e7e75a617f7ff8a66ba1b6, 0xaa272a2eab86d0de5df73b930fd52fd18506356e94664e8db30f53f961013b4d13e2d28f8ad31cd3aa83c8fa066f2ecab1c652adc3a3fb9dd6e054435da52a6d36a1040b8b, 0xc4f1d5d5c66f1da3e43a9a51c6f66a491e89c660d3346822f483f21a7ef1c919266e48ce8be7db6509c58a8a70b36f188b98dbf861f15d0a8653ce59d284cb6014b8b0c5b,
  0xc43e74c69ddb5ac6f623c355c3162409842dc46ff68f9b89ca9a28c603bd67eaf6e4a51fbf246be845bba2ecb369b13bf7d7c1de7b6eed9f0cedbd95ebd738360c1126f0, 0xa7763cc65d00fb2b243947f156d5b1574bbc8615e0b55fbdf7ce6f22ae462d46c7ca7e507697ef7529f3a70615c06812e2beef406d49deccea04da21fd3b2c694237af0, 0x79aaea735f80053b980cf737820a43200343e2ee2eba78fabecbc73f5ca6d03a0385ea0a23380a27059fb8d432f03a51e8c0303c36cf92b0c46f4c80cf03590a1ca60e,
  0x4ac6c0638bacf738d926f716af5a7240d990bf70a7d1a037c67009dbfaec449c023397f59e960333526f5e5431a3838526d5b4e3117ccc1a89899ba7dfa7563c4aeee, 0x2698d3b45e83528af8c6758f13315752d7a387747a408fd4e197556c4e6cda1c0faaaf42a9350d1fd201f7a3d770f77ebe9cb9e71f300f99f2a1233d8c9f1895848c, 0x1098f62849d943849983c190109f920d70270c4a5ef76ad12f192768dedaee6f9d558efc65fc7b70980a22595160a59dc7fca65c960fc27a0c498321655f2c2430c,
  0x5e482bf8f5cae26f5de0a01b181facc9bc0442d49ac5131f96922435ad8c45c98ebe76881141417c97d6e10fd557a01473897bca35af92fe431b76275b1309e62, 0x1b5b1dd209563977f0314833dd0cbf5c23a049c01fa303a574f9aa73c9b0535a8ab1be4a3a63632706261f6466cdb2d6637c5dd017421a0bbcb5fc744b71c3c2, 0x669a0e3947bd9ec381ae7d250a12e0b85c40856c2e2cc9e4473f7ee86a12c7cb5b7605437861af9c79ebb4f1dd876405ff5f5719cac108b1eeab7684e29d18,
  0x132dc59b8e3d6aa20678a624029d4921bf6612296b4a793308cb52108fe2c8880560f26c0b5b3437b5195d23bbc3012363824438b133d04646e1e38727518, 0x2d0fbb67c2097710bde02483fa8d91910e89afbaa804146834a4f24d1f17be1020b8d97c3403b0d4b852c659e4ad82ab252264fe22a14823d45a37810d2, 0x51c241ed5114a3a2c3ee64570037ff2c25775575fde0ec388392b39e353fbc3ca10ee2463a68480bed75ec82137d65c74d2915ed86a006ad856c5a472,
  0x704d9f64300aae691f68727b64327efb30f974998d83d5e55091dadc3a2c6d705510b6062df433959bda3025c43fb9eb8e247da92bc7c8c2504ea2c, 0x721d61f62e9bca30bb6d57c4e01ba1821518c47579be11bebb4254160d12e6ac047e7a34df29dff316bf32e8b543e002c15a6ec41a7777f9fa7ac, 0x537bf51ef672a83fc47df1d5118d8361c76a5f3b9457bd5cb10622a4ba51ae5a9f64651ae36d194a46fe9bc6ad02f83993cf3585aa8282c295e,
  0x2a953bf7df2c63ddbcb749d14d0aa6932ef02c6625f050c3a7bf6c588e61de936a1dff5ffc2ad457705073274a1908403157bc090a855557e, 0xe92e957e930c8977354da8dc95c310673b66b4ef79b9435adefa49ed4d0eb1e60cdd708a2c4e1d987b727c9af36436b332ab2ae5bdc1b0, 0x331fe13254d65111079965b6edfd403439b270539104efb354779f833b7c2528431cb9003f66c279e143279fec08083e1a9c005a3db0,
  0x6c92d186d2fd3b30badb158f017f6efce1a559eadd6d145b3ecb2725e7dde888f12f09302eaa81488cc85083f31678dc03bb8c35d, 0x822b1a67c98b729477f0a737feffeabc7cef12344a0ae7fe46361f9d49c2c71399ce0636991d4ad0e884a33c2fae06b80d5dad, 0x50b5eb3a6252e4c758d44aa7d53c60c3b8f715185521fc3211b606798edc2d7cc97f4497bf824b4e0a79751dfb0123d5e9a,
  0x17269df5624ba2ed36256a7af92a0539482d482b8e9481b4f5de2282aca31bc82c2e6dca26ba020de37197f138d2885a, 0x2a892c438f968bfa9139a3d4b77ad54b9a93be0c175462ab15f4990c0f1db292df41d67fecc658d25b9448c0a20b, 0x19d64bce0a3182e6faad77453bb7bf5cdf06936dbcc3041666710a72a154140e39b6afbe512249c2fa0d001b,
  0x3fff3d85f3dc8a9bd9cbc0d993beb2e180bc8882cdbcc6b0ae4c58c8b3aa9d2e81add9c7704d0e3724c, 0x1c08598dc0be7fa274a64a84b7abdbe8aaef2f4a4bc359aef3f5820e76f67069cae7869abc744c, 0x1455b1a370ff035918ef4e22e7f3e307ee0f2f9391cd11c5e22742e346cdb7f23702c757,
  0xaa51823744a7eedec4df0570e8e6f571015430cac41c3f662a6353c41d2ed307, 0xfffffffffdcbb5f68731202fda3a73640c62accc9d449de218fab92, 0x5156c7b52959eb35b6ff82e03b9410a1d5d22dd2f2d2,
  0x3fffffffffffffffffffffffff91, 0x1]

private theorem eulerianCoefficients_eq : descentCoeffs 110 = eulerianCoefficients := by
  decide +kernel

private theorem upper : upperOK (descentCoeffs 110) first gaps = true := by
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

private theorem lower (i : Fin (lastRepresentative 111 - 2)) :
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

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 111) :
    StrictNegativeInterlacing (originalQuotient 111 k) (eulerian 110) 108 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N111
