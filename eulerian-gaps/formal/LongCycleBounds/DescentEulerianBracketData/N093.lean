import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentPackedData.C127L096.N093

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N093

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L096.N093 LongCycleBounds.DescentNecklace.Packed.C127L096.N093.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L096.N093 LongCycleBounds.DescentNecklace.Packed.C127L096.N093.rows

private theorem actual : RepresentativeChecks 93 previousNodes rows :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L096.N093 LongCycleBounds.DescentNecklace.Packed.C127L096.N093.dataChecks

private def first : LongCycleFinite.Dyadic := ⟨-4951760157141521099596496896, 0⟩

private def gaps : List Window := [
  ⟨⟨-4951599596681103531659231232, 0⟩, ⟨-15948691038797824, 0⟩⟩,
  ⟨⟨-15807919190704128, 0⟩, ⟨-311609524224, 0⟩⟩,
  ⟨⟨-310977232896, 0⟩, ⟨-817629184, 0⟩⟩,
  ⟨⟨-803430400, 0⟩, ⟨-18161152, 0⟩⟩,
  ⟨⟨-18122496, 0⟩, ⟨-1298924, 0⟩⟩,
  ⟨⟨-1298068, 0⟩, ⟨-186048, 0⟩⟩,
  ⟨⟨-371979, 1⟩, ⟨-333827, 3⟩⟩,
  ⟨⟨-83441, 1⟩, ⟨-203567, 4⟩⟩,
  ⟨⟨-407083, 5⟩, ⟨-309123, 6⟩⟩,
  ⟨⟨-309095, 6⟩, ⟨-137985, 6⟩⟩,
  ⟨⟨-137975, 6⟩, ⟨-139321, 7⟩⟩,
  ⟨⟨-278625, 8⟩, ⟨-38695, 6⟩⟩,
  ⟨⟨-309545, 9⟩, ⟨-185497, 9⟩⟩,
  ⟨⟨-370979, 10⟩, ⟨-14769, 6⟩⟩,
  ⟨⟨-29537, 7⟩, ⟨-316431, 11⟩⟩,
  ⟨⟨-316421, 11⟩, ⟨-441565, 12⟩⟩,
  ⟨⟨-441553, 12⟩, ⟨-318915, 12⟩⟩,
  ⟨⟨-318907, 12⟩, ⟨-474269, 13⟩⟩,
  ⟨⟨-474259, 13⟩, ⟨-180751, 12⟩⟩,
  ⟨⟨-361495, 13⟩, ⟨-140735, 12⟩⟩,
  ⟨⟨-281465, 13⟩, ⟨-223211, 13⟩⟩,
  ⟨⟨-223207, 13⟩, ⟨-359707, 14⟩⟩,
  ⟨⟨-359701, 14⟩, ⟨-146943, 13⟩⟩,
  ⟨⟨-293881, 14⟩, ⟨-486109, 15⟩⟩,
  ⟨⟨-243051, 14⟩, ⟨-25397, 11⟩⟩,
  ⟨⟨-406347, 15⟩, ⟨-342909, 15⟩⟩,
  ⟨⟨-42863, 12⟩, ⟨-36475, 12⟩⟩,
  ⟨⟨-72949, 13⟩, ⟨-500317, 16⟩⟩,
  ⟨⟨-500311, 16⟩, ⟨-431755, 16⟩⟩,
  ⟨⟨-215875, 15⟩, ⟨-46847, 13⟩⟩,
  ⟨⟨-93693, 14⟩, ⟨-327017, 16⟩⟩,
  ⟨⟨-327013, 16⟩, ⟨-286671, 16⟩⟩,
  ⟨⟨-71667, 14⟩, ⟨-504677, 17⟩⟩,
  ⟨⟨-15771, 12⟩, ⟨-445855, 17⟩⟩,
  ⟨⟨-445851, 17⟩, ⟨-395163, 17⟩⟩,
  ⟨⟨-395159, 17⟩, ⟨-351227, 17⟩⟩,
  ⟨⟨-351223, 17⟩, ⟨-312949, 17⟩⟩,
  ⟨⟨-156473, 16⟩, ⟨-279441, 17⟩⟩,
  ⟨⟨-139719, 16⟩, ⟨-499951, 18⟩⟩,
  ⟨⟨-249973, 17⟩, ⟨-447925, 18⟩⟩,
  ⟨⟨-447921, 18⟩, ⟨-401817, 18⟩⟩,
  ⟨⟨-200907, 17⟩, ⟨-22551, 14⟩⟩,
  ⟨⟨-90203, 16⟩, ⟨-324235, 18⟩⟩,
  ⟨⟨-40529, 15⟩, ⟨-72877, 16⟩⟩,
  ⟨⟨-291505, 18⟩, ⟨-262145, 18⟩⟩,
  ⟨⟨-131071, 17⟩, ⟨-58935, 16⟩⟩,
  ⟨⟨-117869, 17⟩, ⟨-423889, 19⟩⟩,
  ⟨⟨-423885, 19⟩, ⟨-380915, 19⟩⟩,
  ⟨⟨-23807, 15⟩, ⟨-171023, 18⟩⟩,
  ⟨⟨-171021, 18⟩, ⟨-306837, 19⟩⟩,
  ⟨⟨-306833, 19⟩, ⟨-137453, 18⟩⟩,
  ⟨⟨-274903, 19⟩, ⟨-245921, 19⟩⟩,
  ⟨⟨-245919, 19⟩, ⟨-219589, 19⟩⟩,
  ⟨⟨-219587, 19⟩, ⟨-195657, 19⟩⟩,
  ⟨⟨-391311, 20⟩, ⟨-10869, 15⟩⟩,
  ⟨⟨-86951, 18⟩, ⟨-154131, 19⟩⟩,
  ⟨⟨-154129, 19⟩, ⟨-136167, 19⟩⟩,
  ⟨⟨-272331, 20⟩, ⟨-479437, 21⟩⟩,
  ⟨⟨-59929, 18⟩, ⟨-210141, 20⟩⟩,
  ⟨⟨-210139, 20⟩, ⟨-366727, 21⟩⟩,
  ⟨⟨-366723, 21⟩, ⟨-159165, 20⟩⟩,
  ⟨⟨-159163, 20⟩, ⟨-137353, 20⟩⟩,
  ⟨⟨-274703, 21⟩, ⟨-14719, 17⟩⟩,
  ⟨⟨-471003, 22⟩, ⟨-400809, 22⟩⟩,
  ⟨⟨-100201, 20⟩, ⟨-338231, 22⟩⟩,
  ⟨⟨-169113, 21⟩, ⟨-282737, 22⟩⟩,
  ⟨⟨-282733, 22⟩, ⟨-467663, 23⟩⟩,
  ⟨⟨-467657, 23⟩, ⟨-382091, 23⟩⟩,
  ⟨⟨-382085, 23⟩, ⟨-307873, 23⟩⟩,
  ⟨⟨-76967, 21⟩, ⟨-244151, 23⟩⟩,
  ⟨⟨-244147, 23⟩, ⟨-380197, 24⟩⟩,
  ⟨⟨-190095, 23⟩, ⟨-289797, 24⟩⟩,
  ⟨⟨-283, 14⟩, ⟨-107743, 23⟩⟩,
  ⟨⟨-107741, 23⟩, ⟨-155629, 24⟩⟩,
  ⟨⟨-311251, 25⟩, ⟨-434357, 26⟩⟩,
  ⟨⟨-434347, 26⟩, ⟨-72703, 24⟩⟩,
  ⟨⟨-72701, 24⟩, ⟨-46309, 24⟩⟩,
  ⟨⟨-185231, 26⟩, ⟨-55499, 25⟩⟩,
  ⟨⟨-221989, 27⟩, ⟨-15415, 24⟩⟩,
  ⟨⟨-493263, 29⟩, ⟨-498047, 30⟩⟩,
  ⟨⟨-124507, 28⟩, ⟨-111161, 29⟩⟩,
  ⟨⟨-27789, 27⟩, ⟨-337605, 32⟩⟩,
  ⟨⟨-84397, 30⟩, ⟨-411771, 34⟩⟩,
  ⟨⟨-102937, 32⟩, ⟨-92365, 34⟩⟩,
  ⟨⟨-369437, 36⟩, ⟨-211627, 38⟩⟩,
  ⟨⟨-423225, 39⟩, ⟨-484715, 43⟩⟩,
  ⟨⟨-484679, 43⟩, ⟨-174613, 47⟩⟩,
  ⟨⟨-174599, 47⟩, ⟨-462903, 57⟩⟩,
  ⟨⟨-28929, 53⟩, ⟨-297717, 72⟩⟩,
  ⟨⟨-37211, 69⟩, ⟨-262165, 110⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private def eulerianCoefficients : List ℤ := [
  0x1, 0xfffffffffffffffffffffa3, 0x385ba9df65eecd13cf4f4dbd2d6daca1bbce7,
  0xfffffffeb86b349d7f82e6ccdb030c2467f28493f0774d, 0x31174721509c47a16ba5ffe2631ec4f5a86ed38ca007b373923d1e, 0x385b9809f106fccb095812555c559acdea33f4fac1c14cb50442744025fa,
  0x4d85fd16bdd06f04be21600b03948803a654aa3619736c8b5b37f4c03085462aa, 0xffe3d616ea7841413338a678f7b18bde0799f951a80cf4cf548de833c7813d4d4ad2e, 0xc626b74eadb92a465289d7248f22f2fcbf20baea1775304ab626e34d3fe5c15431de39123,
  0x30cf3a5bf62a6edd3067ddf747f1422e7ea40579877e9e7239e2703ceb950d7fcb1a07ed1b4a9, 0x4bf0133863094634fdaba232908da60b00b690da38513eb06505a6dfe42eb5c5898df14f1b6457dd, 0x369f036ab8f4389cdbb36e9c6858ec2b5f9e8ea0e284334dbe924c7ef9930217022b2828782fa9a7c3f,
  0x1473d33a302c46194fe22f0c588dcc03c339ffa536d0ac5da0c8380f0d45161833052c9b5f151fe66618a4, 0x45de46219a004c43dc912239b51cc9099482719fb7e3e7d557386d04b29a42fdeed32e325d0fed94ab61532c, 0x92247dd9385ecaad6bcf2c5b63f937bbfa57d9b054c996e359f49ee7a00875f7db13e6af20ae14e0f2430d99ac,
  0xc613eba4556c2436a4a55080335c2c195e90b3161f1a3c70b585a71e1c2770893b170c6a04a5232af5e35db59c24, 0xb61a5e94b812f2baa28dfc6375992fbfff99e1ee198521758ece03b94337602cd143907501d4444444fa0354a82c6b, 0x75e349ebe762d86377ec938e4a6f0b20968df58bdc594ad9587e99e480770876109fb797c49ca6e627dd0886110d23e1,
  0x376e1d0a27427363cf77f593d2fa487daca53c4fc44cabe4fceb1f08ad9f17f94d45867ebbe0c6e428806f24ee3d70035d, 0x136d57e5bcc72c34dea195adbff369488c16973738bf43731b30f695e4394d198d7a491c3ac9ef812f7ff74048f1a132535f, 0x5300b3572a465222258d7cb903ec25c15832f67fcb7e26cb7dd30d8026e017686a1374265ee384bd9d1d3cc093f0545440dd6,
  0x11349d05b9e8c0e68e6fc81102e590805abc7dd1a4fad8ecbbaa41d07fdcebc153ae0a2836ca057af5512bc4d8bac810ca4ec22, 0x2d035f621e4c5e8e12f6da94b42685987f62a6ca289d33bc246a10a900efc77241afe9b1f4a07525723f7a7f4406f44dfccffab2, 0x5e30ebbd3532386e97c11f52a3a6bb6da0b836443803011e9b85cec55ed8da210de27543f824415682a72a38871d4f43bb146d786,
  0x9f8ea0f9063010a957c0496c09ff8e1f65b9d0f06cbd2d311ac9b40104a3f9a842b5410d9231f160179637155367f4e1c70c28c391, 0xdd200fcbfd07cdbce6ea1a678cc596b68c590911d92bf7c7aad7edfe31c052e2a448eb17dc28fab754b95847120450bf13894cb8cb3, 0xfd0b920fdc19308ad44cb4c386017e6dd2842c00cca4541477b5eb9ffebbcb08b43700ded9f8abd07720f35deb0d5e9fd4b48daeac5f,
  0xf111b56d04789188d2ed37cafa8b451b1afad7dceeeb1846a6e65fc8285e2f5dc095b1dbc807a2f69712a2297a373e4209149494a2515, 0xc093d776ff517c2b8eb12707e79ec2e2434698a0852a1dfa3be2ddb64e00c9ec8438d594d37c259752642df52590986dce026eedec6430, 0x81d42d2045cdb56e014b678820c96fcf44debdb0de2e7dabedfd83eeea8ad2c54910516b7fb35d21919922561603a6bef83669610650f90,
  0x4a4953219f0c5de8b491d1d13e49d60a8b60209864cfa5b94d68f07fe7cf90204646431d1c02bae63adc656f3511602001dc210bafa15690, 0x24425f84a427b28841374e0045a0531b2e9122fe2680b0edfb01c7fb84570a2931d4955d1451181bf1e7fdaaa472fc48fbe2244a0103d5930, 0xf2a5e1bda2e5adc635519951ae7a62c26a09c55f538307c2528cd8723220fecf4523e80f451470eeb3b4cc2c3fa6bdf33891537984d1a7dba,
  0x575060756ab3056066ff0de81b57314c3663227ec7f80c150bb0239ac7c32450cd579eb9586079d8a3c3d251971e563b40f0a1e0013de4406e, 0x1b209dd5d4b0655dda39b22ced8a62a4fb789d9dc9f3b8b87063f832c4a89632dc87310adac249779a80736fd284c6b6cecada68345a77b9f96, 0x74ccdb24a9b6838e2e699315e034f9d60fbfdfc1b1381a61f2f6b3b31a161de2c0607b7ff9fedef5c75937f795c7f034a3f5f17db82c7084632,
  0x1b4cd310817bec2c1eb96cf5cc8ebdcecd413eda3eb9069656aff1e43b893741cc8c2312a4455b550cf8a71ed90555caad2afb0362617b8fa8dc, 0x58e52e26886a5ddb648bf3242da08b1a058d6980f0edd127c05e3cdfe313366bf3465e7c5062dfac1bc6a2710a416c3da0665c04245c09af13d4, 0xfc94c5b0784e9ed839ffe6a2e998c0070e002b0298ab51d855b9ee52e2fce900ddcd8296f29a33d4fd35a609858c29a0f0534b5c957fe38f10b4,
  0x273650fcd2ffc1a5cb299e51f93301678c4ab7227d9e3e6d86f91a8fc13bfea972a3a22d513387e6152d49dd8c511a75e8eee32bc89ed852b237c, 0x5548df96d127b56d7602ee0d8c7ecd76c1393c2bf6e4e65eb8b210a1a59540fb1dc0dc11c2dd822084946b3f9747c3c81556d1c4fdb01ebce026e, 0xa2a27bcd80653ef514393d2de6b75bceb53e74c0c7b60b8c9ad40685f8baae2823e23e626caccf12d78520cf759e121f59e1a260fa827610cd6ca,
  0x110392427c3e3dfa5caae4f721bfaa1df3484c21fbde3635ed2c72fc33bbcee5334a012ab6bbf4d7e43b6db77ff046664164f8dd49f62c88ea1fd2, 0x1904c5573283357d19a9e1d576d1863f62c548771994792592e491857224cb9f7bda33bf5f99a258d10de57496c615496a7aea6baccc3f6b334c86, 0x2057334d069f4552fc23ecae1a7ecb1f6e8316a6e2acb3ffb69d96b9f13008ec8154ce3c6c6251325f134b490e060129e9152abc343eea1b2df1d8,
  0x24c40f6f08fa5cfb2c943f0bc7887f4099e5b0539fc7b0a4235b8b6e46ceeb3601dde3823631f6e02ed78c87263e54b430ad87b028602039a31908, 0x24c40f6f08fa5cfb2c943f0bc7887f4099e5b0539fc7b0a4235b8b6e46ceeb3601dde3823631f6e02ed78c87263e54b430ad87b028602039a31908, 0x2057334d069f4552fc23ecae1a7ecb1f6e8316a6e2acb3ffb69d96b9f13008ec8154ce3c6c6251325f134b490e060129e9152abc343eea1b2df1d8,
  0x1904c5573283357d19a9e1d576d1863f62c548771994792592e491857224cb9f7bda33bf5f99a258d10de57496c615496a7aea6baccc3f6b334c86, 0x110392427c3e3dfa5caae4f721bfaa1df3484c21fbde3635ed2c72fc33bbcee5334a012ab6bbf4d7e43b6db77ff046664164f8dd49f62c88ea1fd2, 0xa2a27bcd80653ef514393d2de6b75bceb53e74c0c7b60b8c9ad40685f8baae2823e23e626caccf12d78520cf759e121f59e1a260fa827610cd6ca,
  0x5548df96d127b56d7602ee0d8c7ecd76c1393c2bf6e4e65eb8b210a1a59540fb1dc0dc11c2dd822084946b3f9747c3c81556d1c4fdb01ebce026e, 0x273650fcd2ffc1a5cb299e51f93301678c4ab7227d9e3e6d86f91a8fc13bfea972a3a22d513387e6152d49dd8c511a75e8eee32bc89ed852b237c, 0xfc94c5b0784e9ed839ffe6a2e998c0070e002b0298ab51d855b9ee52e2fce900ddcd8296f29a33d4fd35a609858c29a0f0534b5c957fe38f10b4,
  0x58e52e26886a5ddb648bf3242da08b1a058d6980f0edd127c05e3cdfe313366bf3465e7c5062dfac1bc6a2710a416c3da0665c04245c09af13d4, 0x1b4cd310817bec2c1eb96cf5cc8ebdcecd413eda3eb9069656aff1e43b893741cc8c2312a4455b550cf8a71ed90555caad2afb0362617b8fa8dc, 0x74ccdb24a9b6838e2e699315e034f9d60fbfdfc1b1381a61f2f6b3b31a161de2c0607b7ff9fedef5c75937f795c7f034a3f5f17db82c7084632,
  0x1b209dd5d4b0655dda39b22ced8a62a4fb789d9dc9f3b8b87063f832c4a89632dc87310adac249779a80736fd284c6b6cecada68345a77b9f96, 0x575060756ab3056066ff0de81b57314c3663227ec7f80c150bb0239ac7c32450cd579eb9586079d8a3c3d251971e563b40f0a1e0013de4406e, 0xf2a5e1bda2e5adc635519951ae7a62c26a09c55f538307c2528cd8723220fecf4523e80f451470eeb3b4cc2c3fa6bdf33891537984d1a7dba,
  0x24425f84a427b28841374e0045a0531b2e9122fe2680b0edfb01c7fb84570a2931d4955d1451181bf1e7fdaaa472fc48fbe2244a0103d5930, 0x4a4953219f0c5de8b491d1d13e49d60a8b60209864cfa5b94d68f07fe7cf90204646431d1c02bae63adc656f3511602001dc210bafa15690, 0x81d42d2045cdb56e014b678820c96fcf44debdb0de2e7dabedfd83eeea8ad2c54910516b7fb35d21919922561603a6bef83669610650f90,
  0xc093d776ff517c2b8eb12707e79ec2e2434698a0852a1dfa3be2ddb64e00c9ec8438d594d37c259752642df52590986dce026eedec6430, 0xf111b56d04789188d2ed37cafa8b451b1afad7dceeeb1846a6e65fc8285e2f5dc095b1dbc807a2f69712a2297a373e4209149494a2515, 0xfd0b920fdc19308ad44cb4c386017e6dd2842c00cca4541477b5eb9ffebbcb08b43700ded9f8abd07720f35deb0d5e9fd4b48daeac5f,
  0xdd200fcbfd07cdbce6ea1a678cc596b68c590911d92bf7c7aad7edfe31c052e2a448eb17dc28fab754b95847120450bf13894cb8cb3, 0x9f8ea0f9063010a957c0496c09ff8e1f65b9d0f06cbd2d311ac9b40104a3f9a842b5410d9231f160179637155367f4e1c70c28c391, 0x5e30ebbd3532386e97c11f52a3a6bb6da0b836443803011e9b85cec55ed8da210de27543f824415682a72a38871d4f43bb146d786,
  0x2d035f621e4c5e8e12f6da94b42685987f62a6ca289d33bc246a10a900efc77241afe9b1f4a07525723f7a7f4406f44dfccffab2, 0x11349d05b9e8c0e68e6fc81102e590805abc7dd1a4fad8ecbbaa41d07fdcebc153ae0a2836ca057af5512bc4d8bac810ca4ec22, 0x5300b3572a465222258d7cb903ec25c15832f67fcb7e26cb7dd30d8026e017686a1374265ee384bd9d1d3cc093f0545440dd6,
  0x136d57e5bcc72c34dea195adbff369488c16973738bf43731b30f695e4394d198d7a491c3ac9ef812f7ff74048f1a132535f, 0x376e1d0a27427363cf77f593d2fa487daca53c4fc44cabe4fceb1f08ad9f17f94d45867ebbe0c6e428806f24ee3d70035d, 0x75e349ebe762d86377ec938e4a6f0b20968df58bdc594ad9587e99e480770876109fb797c49ca6e627dd0886110d23e1,
  0xb61a5e94b812f2baa28dfc6375992fbfff99e1ee198521758ece03b94337602cd143907501d4444444fa0354a82c6b, 0xc613eba4556c2436a4a55080335c2c195e90b3161f1a3c70b585a71e1c2770893b170c6a04a5232af5e35db59c24, 0x92247dd9385ecaad6bcf2c5b63f937bbfa57d9b054c996e359f49ee7a00875f7db13e6af20ae14e0f2430d99ac,
  0x45de46219a004c43dc912239b51cc9099482719fb7e3e7d557386d04b29a42fdeed32e325d0fed94ab61532c, 0x1473d33a302c46194fe22f0c588dcc03c339ffa536d0ac5da0c8380f0d45161833052c9b5f151fe66618a4, 0x369f036ab8f4389cdbb36e9c6858ec2b5f9e8ea0e284334dbe924c7ef9930217022b2828782fa9a7c3f,
  0x4bf0133863094634fdaba232908da60b00b690da38513eb06505a6dfe42eb5c5898df14f1b6457dd, 0x30cf3a5bf62a6edd3067ddf747f1422e7ea40579877e9e7239e2703ceb950d7fcb1a07ed1b4a9, 0xc626b74eadb92a465289d7248f22f2fcbf20baea1775304ab626e34d3fe5c15431de39123,
  0xffe3d616ea7841413338a678f7b18bde0799f951a80cf4cf548de833c7813d4d4ad2e, 0x4d85fd16bdd06f04be21600b03948803a654aa3619736c8b5b37f4c03085462aa, 0x385b9809f106fccb095812555c559acdea33f4fac1c14cb50442744025fa,
  0x31174721509c47a16ba5ffe2631ec4f5a86ed38ca007b373923d1e, 0xfffffffeb86b349d7f82e6ccdb030c2467f28493f0774d, 0x385ba9df65eecd13cf4f4dbd2d6daca1bbce7,
  0xfffffffffffffffffffffa3, 0x1]

private theorem eulerianCoefficients_eq : descentCoeffs 92 = eulerianCoefficients := by
  decide +kernel

private theorem upper : upperOK (descentCoeffs 92) first gaps = true := by
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

private theorem lower (i : Fin (lastRepresentative 93 - 2)) :
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

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 93) :
    StrictNegativeInterlacing (originalQuotient 93 k) (eulerian 92) 90 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N093
