import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentPackedData.C127L096.N096

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N096

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L096.N096 LongCycleBounds.DescentNecklace.Packed.C127L096.N096.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L096.N096 LongCycleBounds.DescentNecklace.Packed.C127L096.N096.rows

private theorem actual : RepresentativeChecks 96 previousNodes rows :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L096.N096 LongCycleBounds.DescentNecklace.Packed.C127L096.N096.dataChecks

private def first : LongCycleFinite.Dyadic := ⟨-39614081257132168796771975168, 0⟩

private def gaps : List Window := [
  ⟨⟨-39612796773448828253273849856, 0⟩, ⟨-54580581836521472, 0⟩⟩,
  ⟨⟨-53454544490725376, 0⟩, ⟨-739707453440, 0⟩⟩,
  ⟨⟨-737593524224, 0⟩, ⟨-1586774016, 0⟩⟩,
  ⟨⟨-1553043456, 0⟩, ⟨-31525376, 0⟩⟩,
  ⟨⟨-31450624, 0⟩, ⟨-2075716, 0⟩⟩,
  ⟨⟨-2074220, 0⟩, ⟨-279884, 0⟩⟩,
  ⟨⟨-279790, 0⟩, ⟨-239817, 2⟩⟩,
  ⟨⟨-479539, 3⟩, ⟨-282181, 4⟩⟩,
  ⟨⟨-282143, 4⟩, ⟨-208143, 5⟩⟩,
  ⟨⟨-208123, 5⟩, ⟨-362943, 7⟩⟩,
  ⟨⟨-90729, 5⟩, ⟨-89831, 6⟩⟩,
  ⟨⟨-179651, 7⟩, ⟨-392647, 9⟩⟩,
  ⟨⟨-98157, 7⟩, ⟨-232003, 9⟩⟩,
  ⟨⟨-463987, 10⟩, ⟨-146001, 9⟩⟩,
  ⟨⟨-36499, 7⟩, ⟨-193477, 10⟩⟩,
  ⟨⟨-193471, 10⟩, ⟨-66889, 9⟩⟩,
  ⟨⟨-66887, 9⟩, ⟨-191717, 11⟩⟩,
  ⟨⟨-5991, 6⟩, ⟨-141573, 11⟩⟩,
  ⟨⟨-283139, 12⟩, ⟨-214519, 12⟩⟩,
  ⟨⟨-214515, 12⟩, ⟨-332275, 13⟩⟩,
  ⟨⟨-332269, 13⟩, ⟨-262273, 13⟩⟩,
  ⟨⟨-65567, 11⟩, ⟨-420915, 14⟩⟩,
  ⟨⟨-105227, 12⟩, ⟨-342661, 14⟩⟩,
  ⟨⟨-2677, 7⟩, ⟨-35313, 11⟩⟩,
  ⟨⟨-282499, 14⟩, ⟨-235511, 14⟩⟩,
  ⟨⟨-58877, 12⟩, ⟨-49569, 12⟩⟩,
  ⟨⟨-198273, 14⟩, ⟨-168389, 14⟩⟩,
  ⟨⟨-168387, 14⟩, ⟨-288239, 15⟩⟩,
  ⟨⟨-288235, 15⟩, ⟨-496805, 16⟩⟩,
  ⟨⟨-496799, 16⟩, ⟨-430781, 16⟩⟩,
  ⟨⟨-53847, 13⟩, ⟨-46949, 13⟩⟩,
  ⟨⟨-93897, 14⟩, ⟨-164539, 15⟩⟩,
  ⟨⟨-329075, 16⟩, ⟨-144795, 15⟩⟩,
  ⟨⟨-144793, 15⟩, ⟨-63959, 14⟩⟩,
  ⟨⟨-511667, 17⟩, ⟨-14175, 12⟩⟩,
  ⟨⟨-113399, 15⟩, ⟨-12605, 12⟩⟩,
  ⟨⟨-100839, 15⟩, ⟨-359661, 17⟩⟩,
  ⟨⟨-359657, 17⟩, ⟨-160731, 16⟩⟩,
  ⟨⟨-321459, 17⟩, ⟨-143959, 16⟩⟩,
  ⟨⟨-287915, 17⟩, ⟨-129169, 16⟩⟩,
  ⟨⟨-8073, 12⟩, ⟨-116075, 16⟩⟩,
  ⟨⟨-58037, 15⟩, ⟨-13055, 13⟩⟩,
  ⟨⟨-104439, 16⟩, ⟨-23517, 14⟩⟩,
  ⟨⟨-94067, 16⟩, ⟨-10599, 13⟩⟩,
  ⟨⟨-339165, 18⟩, ⟨-305893, 18⟩⟩,
  ⟨⟨-152945, 17⟩, ⟨-137987, 17⟩⟩,
  ⟨⟨-275971, 18⟩, ⟨-498017, 19⟩⟩,
  ⟨⟨-498013, 19⟩, ⟨-449309, 19⟩⟩,
  ⟨⟨-449305, 19⟩, ⟨-405227, 19⟩⟩,
  ⟨⟨-50653, 16⟩, ⟨-91317, 17⟩⟩,
  ⟨⟨-365265, 19⟩, ⟨-328993, 19⟩⟩,
  ⟨⟨-164495, 18⟩, ⟨-18501, 15⟩⟩,
  ⟨⟨-296013, 19⟩, ⟨-33251, 16⟩⟩,
  ⟨⟨-266005, 19⟩, ⟨-238679, 19⟩⟩,
  ⟨⟨-238677, 19⟩, ⟨-427545, 20⟩⟩,
  ⟨⟨-213771, 19⟩, ⟨-382137, 20⟩⟩,
  ⟨⟨-191067, 19⟩, ⟨-340737, 20⟩⟩,
  ⟨⟨-170367, 19⟩, ⟨-151499, 19⟩⟩,
  ⟨⟨-302995, 20⟩, ⟨-134305, 19⟩⟩,
  ⟨⟨-268607, 20⟩, ⟨-474603, 21⟩⟩,
  ⟨⟨-237299, 20⟩, ⟨-417653, 21⟩⟩,
  ⟨⟨-26103, 17⟩, ⟨-182965, 20⟩⟩,
  ⟨⟨-182963, 20⟩, ⟨-159525, 20⟩⟩,
  ⟨⟨-159523, 20⟩, ⟨-276651, 21⟩⟩,
  ⟨⟨-34581, 18⟩, ⟨-119207, 20⟩⟩,
  ⟨⟨-476823, 22⟩, ⟨-51013, 19⟩⟩,
  ⟨⟨-408099, 22⟩, ⟨-346589, 22⟩⟩,
  ⟨⟨-43323, 19⟩, ⟨-291795, 22⟩⟩,
  ⟨⟨-291791, 22⟩, ⟨-486515, 23⟩⟩,
  ⟨⟨-486509, 23⟩, ⟨-401101, 23⟩⟩,
  ⟨⟨-401095, 23⟩, ⟨-326527, 23⟩⟩,
  ⟨⟨-163261, 22⟩, ⟨-262021, 23⟩⟩,
  ⟨⟨-262017, 23⟩, ⟨-413635, 24⟩⟩,
  ⟨⟨-103407, 22⟩, ⟨-160175, 23⟩⟩,
  ⟨⟨-40043, 21⟩, ⟨-242703, 24⟩⟩,
  ⟨⟨-485397, 25⟩, ⟨-358449, 25⟩⟩,
  ⟨⟨-358441, 25⟩, ⟨-513691, 26⟩⟩,
  ⟨⟨-32105, 22⟩, ⟨-355193, 26⟩⟩,
  ⟨⟨-22199, 22⟩, ⟨-470691, 27⟩⟩,
  ⟨⟨-470679, 27⟩, ⟨-148107, 26⟩⟩,
  ⟨⟨-148103, 26⟩, ⟨-350039, 28⟩⟩,
  ⟨⟨-87507, 26⟩, ⟨-382507, 29⟩⟩,
  ⟨⟨-382493, 29⟩, ⟨-94673, 28⟩⟩,
  ⟨⟨-378677, 30⟩, ⟨-82547, 29⟩⟩,
  ⟨⟨-330173, 31⟩, ⟨-487145, 33⟩⟩,
  ⟨⟨-487121, 33⟩, ⟨-71643, 32⟩⟩,
  ⟨⟨-71639, 32⟩, ⟨-122791, 35⟩⟩,
  ⟨⟨-491133, 37⟩, ⟨-264863, 39⟩⟩,
  ⟨⟨-264845, 39⟩, ⟨-17451, 39⟩⟩,
  ⟨⟨-279195, 43⟩, ⟨-356733, 49⟩⟩,
  ⟨⟨-356705, 49⟩, ⟨-390407, 58⟩⟩,
  ⟨⟨-195187, 57⟩, ⟨-352833, 74⟩⟩,
  ⟨⟨-11025, 69⟩, ⟨-262149, 113⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private def eulerianCoefficients : List ℤ := [
  0x1, 0x7fffffffffffffffffffffa0, 0x5f1aaea8fc0367016dd5d32f3ca91350eb3afb,
  0x3fffffffdc55fe80a17eb04776cfd0ce494098c1a7ce61c0, 0x17f85dd0ad5c4ee3b1d344dd21630f8946e551bec9689883bd37e7a5, 0x2f8d4e575acefe7e195732d493243613a786dcfe7cf29f8a0898513642f5e0,
  0x67df1fb19ed56c56215b45043f3d5c0137b4fe0f933cae555ab552c6ba5de328c2f, 0x1ffd90c1e0fc0e89699e3acb1a74bec5b1fb6bf0e328c4d148ce55c54dfdb50eef8eb580, 0x2348d0dd00c43faa886d0cb7581a9ce454bfbdb463d473bc23b849d86fe7de17700d16baa915,
  0xbeef160210401c87f3150f7a1da52d3219d5363881f5d58392956ddf94a0822f904f0bf304e67a0, 0x18c1c6effc673622d575f2683611fa95ac295eb315297e79fd4355daf35f7fd217326612e940bcb1327, 0x173147a4ee86c2d031fd10f6c8e68952045b63081f686d65b70aeba1bd2639acf44c5b9467843aadb74440,
  0xb187a2ff307f687ed413adc3a17c8417f338bd2c079c7562fbaa6d9d78de9c265b89d670a35e065e788080f9, 0x2fac5a0ac384bb6b948f9f04dc0138c906df9d33d59c2c4577d8e223c05491488a252f70c59d43faaf3a81f96e0, 0x7bccd520ac1ab82f71bff387ab222e4d165442979717f7d8457e12768f4870c6ef0c0ed6cb2e14188d3ba267c817b,
  0xce160d8d7394e8a1d5d58ae42fb57bfee176c2b992fa85ae00631f6e447502590ed23fff49685a6dd6995b02dc04100, 0xe69e749f406c518247f774fba63ae2880cc28494b8a14ea2e7000184319e6e6c5a37d2604679ce3e837f478351262dd27, 0xb45cb12849115b853f316bebac3d94564bc147ff069e350b935c7041734a1b33dd281ddf207ebe83eb78f01de94bd6cf660,
  0x65cec39508de682e911b20b1629b2abc1d43d384b1a2b68ad6df72826d2c48f0ffa714e291327537aedcc768b0943d11d0a9d, 0x2a9be89af7f7dee7d51a9c1ee8584547479ac816639b9fb165984d2591f063b6440b01f0cd471ace8ba4d2466fe206a6c83b140, 0xd86dc0e6ec800194554cb03a5e2c11dc8fed57543874afabe0ea0b5d78719ae985715207297641d8b67b3c576e906be4ec656703,
  0x35235f9177b82e1fd5a0a89fb7d977012f449740b504b775ece6d19b5248e1cfd6435f19bd5f64b247e1d121d298932a16c4dfba20, 0xa4279aead2f8bb637bcc3e396fde5072ff4d2584eca83b1db2ecaca25308bceeb45cdaae13041398ab2387ddf095331b27b57352ba9, 0x19491bbcc8600dfb77584e8ff6ce23c40fdf900cc7b58fc32c34de9fd45472f67bf3fc04a33d6e4aa71cfbda50a7aee56e2d214b9a780,
  0x325821b87acbacea04246edd8e16cf6b0429cb28dcf97f20d1994b8b6c72610ae6fdf014daea01d19032668432f61ace6c91a8a7a4668b, 0x51ded825215d090a49395751475fd00832bbce3e4b3a59aaf5b0d1576a8a2b68f31776dcfdbb617aeec4053aa749c6580c776f6faff3d60, 0x6dcc1075ed6b569dd49ecfee2f20ce12d4ad39f4a2d11af2790007d3039569371e2bf253073401da09992fed9168395e81707fcee61df499,
  0x7a78b36c4f0ca8e2607eb83bc41bff267163115a50a1cf46a4d8494ed94a89cec96418e82eeaabdef41dbedf1ec93266acad25e0db1192cc0, 0x727af9c7f5e0bfededf23226086c7b72b1fe2ccce6f01f27451cc7ce1826a98c03c63b7c7ac069c1151bc714347ab979d4117e90f7dd0b6987, 0x5a4754840878e81c2ceed5ce0ac1a4b3a5a7854f286c23f945e80f770cb04fcb1987e0953a9625f29543962e14d76dc2ac7744a364507c7d620,
  0x3c6ba1e7b707e1b371b6b1fc06bfa2b667f3efded4c372abf44044296303818804ffb12b586224d9800f21902868c21e5b131161d4d4874dc465, 0x2280531d06452848665945a84de1c53ca9c0a8d98d9108ea5a56a92f3e32adffa09fddbfb31829ae40181681990828c3851cc9106346b84418c00, 0x10e3882f2f7cc8970627b0edaaf47a06e2d7ac5af5a423a2bbd59a159dadde6a1b6c33035fbfa5047de19225c5fdaf5e329117c4788a0a79c8020a,
  0x71e07696ec9dfe50345645ff6dda3a8a4fa93e274070be8fffe4e3812fd878602b0fbd570e610d5e95a90393cf405e52e1046e1e6a3411dbff3840, 0x2978adeeb7f7ce7d9c98071c37a9b03dbfb6072e80a92bcd2ea9f850fb74e48fc111b253d20898e4b07df8de0ba32740712e99a20cb0a42f4a65c4e, 0xd187a4a33cc9088c4006f9483be49255e9b0843f1999a64fd8c84d96add4e1ad1eaa593c7f7021877e803c4352dce79e546b5658d47826fa71ded80,
  0x398b099432aa677381ff8a4aa995d5404997dda1c01d61dd18b6fca0e6a02c583b9b2cec96732c078d51c6524255040d7652d39c75199c163d9c0ef2, 0xdc7dc1570188f52cec70724abf070caf34362b8e5df106fef2c364b460f2e74716d414ecda6bc926eaac9d1e8ebc5c5823936de83639690bc32716c0, 0x2e27df72f0f216ef13426134e709b1b2cbdee0a6f0aebbe2eed9e29c876b8eb0c30ad958352b1d954147c06c26cb141ccc614b32fcc6fe572727367d6,
  0x87680417b9c83c96b2d6969ee905e326dfcf678b44db3995b1c18df75dbfeda096efa3e6c4466edde56c3a434309a47c32b1da2632f55c931f0ff2300, 0x15c9366db228743cef5f8a926ac907d540b7cb71195466819a428d12793019c7aff5e3fb6fd5b08536e741031030df9dff56360c909726b709b5ff3cb2, 0x314a420d80779f982cb6d809b71da8eeb253bc01c2f3d36a4f89d5357162f8894d5253c25e497e8463419a2db95b090a44fce0c249505a33d1e2eb1440,
  0x62239fa33c7feb01fb800b207a8263705ee113c5aa683b8d1ac9693c6efe656f595dc536c91da2761eb6e2f052a8575b7947be9889591e1dbb4e171ea6, 0xac264797dd205e33b439c23f07d580b73e936585c55cdc88207ea5e6facda52ab03e89ca6dbb60da35d0999f67d5aac8b8442a62ac6d7a4558d1bf8e80, 0x10a477e3dadf7ac1f639e1d6748c897a7275c5cc8815a0b1e36b27859473061fdefb6e88438aeb42646c06af094580fcf17f7d9c5831fcc6d249fcbef9a,
  0x16b71177677d88e0d1f524c51962162b046f30a9332553aea801d64727c13e528ca0997886531399bbad22f0488940d759fb7a29c8ce70e4524ea29e4c0, 0x1b5ef48a4eb0478d9d0aca848df2a08713178ae82e62934c63c80fc37e4f285ff3f8e74a8e4575800452bb73493eeda2de2217c0a84aef16b2c76916eee, 0x1d20045f0ecbd93f2fbe921b92e5a06a85ab68ba2e61c533c2a82a64627c6fb96a71ca202055146fa6f87bf4f53c5c091621fbafa3c3756e328d96d6600,
  0x1b5ef48a4eb0478d9d0aca848df2a08713178ae82e62934c63c80fc37e4f285ff3f8e74a8e4575800452bb73493eeda2de2217c0a84aef16b2c76916eee, 0x16b71177677d88e0d1f524c51962162b046f30a9332553aea801d64727c13e528ca0997886531399bbad22f0488940d759fb7a29c8ce70e4524ea29e4c0, 0x10a477e3dadf7ac1f639e1d6748c897a7275c5cc8815a0b1e36b27859473061fdefb6e88438aeb42646c06af094580fcf17f7d9c5831fcc6d249fcbef9a,
  0xac264797dd205e33b439c23f07d580b73e936585c55cdc88207ea5e6facda52ab03e89ca6dbb60da35d0999f67d5aac8b8442a62ac6d7a4558d1bf8e80, 0x62239fa33c7feb01fb800b207a8263705ee113c5aa683b8d1ac9693c6efe656f595dc536c91da2761eb6e2f052a8575b7947be9889591e1dbb4e171ea6, 0x314a420d80779f982cb6d809b71da8eeb253bc01c2f3d36a4f89d5357162f8894d5253c25e497e8463419a2db95b090a44fce0c249505a33d1e2eb1440,
  0x15c9366db228743cef5f8a926ac907d540b7cb71195466819a428d12793019c7aff5e3fb6fd5b08536e741031030df9dff56360c909726b709b5ff3cb2, 0x87680417b9c83c96b2d6969ee905e326dfcf678b44db3995b1c18df75dbfeda096efa3e6c4466edde56c3a434309a47c32b1da2632f55c931f0ff2300, 0x2e27df72f0f216ef13426134e709b1b2cbdee0a6f0aebbe2eed9e29c876b8eb0c30ad958352b1d954147c06c26cb141ccc614b32fcc6fe572727367d6,
  0xdc7dc1570188f52cec70724abf070caf34362b8e5df106fef2c364b460f2e74716d414ecda6bc926eaac9d1e8ebc5c5823936de83639690bc32716c0, 0x398b099432aa677381ff8a4aa995d5404997dda1c01d61dd18b6fca0e6a02c583b9b2cec96732c078d51c6524255040d7652d39c75199c163d9c0ef2, 0xd187a4a33cc9088c4006f9483be49255e9b0843f1999a64fd8c84d96add4e1ad1eaa593c7f7021877e803c4352dce79e546b5658d47826fa71ded80,
  0x2978adeeb7f7ce7d9c98071c37a9b03dbfb6072e80a92bcd2ea9f850fb74e48fc111b253d20898e4b07df8de0ba32740712e99a20cb0a42f4a65c4e, 0x71e07696ec9dfe50345645ff6dda3a8a4fa93e274070be8fffe4e3812fd878602b0fbd570e610d5e95a90393cf405e52e1046e1e6a3411dbff3840, 0x10e3882f2f7cc8970627b0edaaf47a06e2d7ac5af5a423a2bbd59a159dadde6a1b6c33035fbfa5047de19225c5fdaf5e329117c4788a0a79c8020a,
  0x2280531d06452848665945a84de1c53ca9c0a8d98d9108ea5a56a92f3e32adffa09fddbfb31829ae40181681990828c3851cc9106346b84418c00, 0x3c6ba1e7b707e1b371b6b1fc06bfa2b667f3efded4c372abf44044296303818804ffb12b586224d9800f21902868c21e5b131161d4d4874dc465, 0x5a4754840878e81c2ceed5ce0ac1a4b3a5a7854f286c23f945e80f770cb04fcb1987e0953a9625f29543962e14d76dc2ac7744a364507c7d620,
  0x727af9c7f5e0bfededf23226086c7b72b1fe2ccce6f01f27451cc7ce1826a98c03c63b7c7ac069c1151bc714347ab979d4117e90f7dd0b6987, 0x7a78b36c4f0ca8e2607eb83bc41bff267163115a50a1cf46a4d8494ed94a89cec96418e82eeaabdef41dbedf1ec93266acad25e0db1192cc0, 0x6dcc1075ed6b569dd49ecfee2f20ce12d4ad39f4a2d11af2790007d3039569371e2bf253073401da09992fed9168395e81707fcee61df499,
  0x51ded825215d090a49395751475fd00832bbce3e4b3a59aaf5b0d1576a8a2b68f31776dcfdbb617aeec4053aa749c6580c776f6faff3d60, 0x325821b87acbacea04246edd8e16cf6b0429cb28dcf97f20d1994b8b6c72610ae6fdf014daea01d19032668432f61ace6c91a8a7a4668b, 0x19491bbcc8600dfb77584e8ff6ce23c40fdf900cc7b58fc32c34de9fd45472f67bf3fc04a33d6e4aa71cfbda50a7aee56e2d214b9a780,
  0xa4279aead2f8bb637bcc3e396fde5072ff4d2584eca83b1db2ecaca25308bceeb45cdaae13041398ab2387ddf095331b27b57352ba9, 0x35235f9177b82e1fd5a0a89fb7d977012f449740b504b775ece6d19b5248e1cfd6435f19bd5f64b247e1d121d298932a16c4dfba20, 0xd86dc0e6ec800194554cb03a5e2c11dc8fed57543874afabe0ea0b5d78719ae985715207297641d8b67b3c576e906be4ec656703,
  0x2a9be89af7f7dee7d51a9c1ee8584547479ac816639b9fb165984d2591f063b6440b01f0cd471ace8ba4d2466fe206a6c83b140, 0x65cec39508de682e911b20b1629b2abc1d43d384b1a2b68ad6df72826d2c48f0ffa714e291327537aedcc768b0943d11d0a9d, 0xb45cb12849115b853f316bebac3d94564bc147ff069e350b935c7041734a1b33dd281ddf207ebe83eb78f01de94bd6cf660,
  0xe69e749f406c518247f774fba63ae2880cc28494b8a14ea2e7000184319e6e6c5a37d2604679ce3e837f478351262dd27, 0xce160d8d7394e8a1d5d58ae42fb57bfee176c2b992fa85ae00631f6e447502590ed23fff49685a6dd6995b02dc04100, 0x7bccd520ac1ab82f71bff387ab222e4d165442979717f7d8457e12768f4870c6ef0c0ed6cb2e14188d3ba267c817b,
  0x2fac5a0ac384bb6b948f9f04dc0138c906df9d33d59c2c4577d8e223c05491488a252f70c59d43faaf3a81f96e0, 0xb187a2ff307f687ed413adc3a17c8417f338bd2c079c7562fbaa6d9d78de9c265b89d670a35e065e788080f9, 0x173147a4ee86c2d031fd10f6c8e68952045b63081f686d65b70aeba1bd2639acf44c5b9467843aadb74440,
  0x18c1c6effc673622d575f2683611fa95ac295eb315297e79fd4355daf35f7fd217326612e940bcb1327, 0xbeef160210401c87f3150f7a1da52d3219d5363881f5d58392956ddf94a0822f904f0bf304e67a0, 0x2348d0dd00c43faa886d0cb7581a9ce454bfbdb463d473bc23b849d86fe7de17700d16baa915,
  0x1ffd90c1e0fc0e89699e3acb1a74bec5b1fb6bf0e328c4d148ce55c54dfdb50eef8eb580, 0x67df1fb19ed56c56215b45043f3d5c0137b4fe0f933cae555ab552c6ba5de328c2f, 0x2f8d4e575acefe7e195732d493243613a786dcfe7cf29f8a0898513642f5e0,
  0x17f85dd0ad5c4ee3b1d344dd21630f8946e551bec9689883bd37e7a5, 0x3fffffffdc55fe80a17eb04776cfd0ce494098c1a7ce61c0, 0x5f1aaea8fc0367016dd5d32f3ca91350eb3afb,
  0x7fffffffffffffffffffffa0, 0x1]

private theorem eulerianCoefficients_eq : descentCoeffs 95 = eulerianCoefficients := by
  decide +kernel

private theorem upper : upperOK (descentCoeffs 95) first gaps = true := by
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

private theorem lower (i : Fin (lastRepresentative 96 - 2)) :
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

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 96) :
    StrictNegativeInterlacing (originalQuotient 96 k) (eulerian 95) 93 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N096
