import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentPackedData.C127L127.N124

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N124

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L127.N124 LongCycleBounds.DescentNecklace.Packed.C127L127.N124.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L127.N124 LongCycleBounds.DescentNecklace.Packed.C127L127.N124.rows

private theorem actual : RepresentativeChecks 124 previousNodes rows :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L127.N124 LongCycleBounds.DescentNecklace.Packed.C127L127.N124.dataChecks

private def first : LongCycleFinite.Dyadic := ⟨-10633823966279326983230456482242756608, 0⟩

private def gaps : List Window := [
  ⟨⟨-10633479165316064904833249378970894336, 0⟩, ⟨-4576368790149548474368, 0⟩⟩,
  ⟨⟨-4281211877770940907520, 0⟩, ⟨-2431432525873152, 0⟩⟩,
  ⟨⟨-2246611493191680, 0⟩, ⟨-875768578048, 0⟩⟩,
  ⟨⟨-772525785088, 0⟩, ⟨-5369495552, 0⟩⟩,
  ⟨⟨-5328896000, 0⟩, ⟨-162260480, 0⟩⟩,
  ⟨⟨-161997824, 0⟩, ⟨-12409632, 0⟩⟩,
  ⟨⟨-12401792, 0⟩, ⟨-1727328, 0⟩⟩,
  ⟨⟨-1726756, 0⟩, ⟨-362130, 0⟩⟩,
  ⟨⟨-362055, 0⟩, ⟨-406781, 2⟩⟩,
  ⟨⟨-406723, 2⟩, ⟨-141789, 2⟩⟩,
  ⟨⟨-70887, 1⟩, ⟨-232991, 4⟩⟩,
  ⟨⟨-58243, 2⟩, ⟨-435003, 6⟩⟩,
  ⟨⟨-217487, 5⟩, ⟨-449365, 7⟩⟩,
  ⟨⟨-112335, 5⟩, ⟨-125919, 6⟩⟩,
  ⟨⟨-503653, 8⟩, ⟨-150883, 7⟩⟩,
  ⟨⟨-150877, 7⟩, ⟨-47769, 6⟩⟩,
  ⟨⟨-191069, 8⟩, ⟨-253441, 9⟩⟩,
  ⟨⟨-506867, 10⟩, ⟨-43697, 7⟩⟩,
  ⟨⟨-174783, 9⟩, ⟨-498565, 11⟩⟩,
  ⟨⟨-62319, 8⟩, ⟨-182935, 10⟩⟩,
  ⟨⟨-182931, 10⟩, ⟨-68813, 9⟩⟩,
  ⟨⟨-275245, 11⟩, ⟨-423213, 12⟩⟩,
  ⟨⟨-423205, 12⟩, ⟨-331591, 12⟩⟩,
  ⟨⟨-331585, 12⟩, ⟨-264175, 12⟩⟩,
  ⟨⟨-132085, 11⟩, ⟨-6675, 7⟩⟩,
  ⟨⟨-427193, 13⟩, ⟨-10937, 8⟩⟩,
  ⟨⟨-174989, 12⟩, ⟨-36263, 10⟩⟩,
  ⟨⟨-72525, 11⟩, ⟨-243007, 13⟩⟩,
  ⟨⟨-60751, 11⟩, ⟨-102743, 12⟩⟩,
  ⟨⟨-410967, 14⟩, ⟨-21905, 10⟩⟩,
  ⟨⟨-350475, 14⟩, ⟨-301195, 14⟩⟩,
  ⟨⟨-301191, 14⟩, ⟨-521297, 15⟩⟩,
  ⟨⟨-130323, 13⟩, ⟨-226987, 14⟩⟩,
  ⟨⟨-453969, 15⟩, ⟨-198813, 14⟩⟩,
  ⟨⟨-397621, 15⟩, ⟨-350095, 15⟩⟩,
  ⟨⟨-350091, 15⟩, ⟨-309723, 15⟩⟩,
  ⟨⟨-309719, 15⟩, ⟨-275203, 15⟩⟩,
  ⟨⟨-1075, 7⟩, ⟨-491017, 16⟩⟩,
  ⟨⟨-122753, 14⟩, ⟨-439635, 16⟩⟩,
  ⟨⟨-439631, 16⟩, ⟨-394949, 16⟩⟩,
  ⟨⟨-394945, 16⟩, ⟨-177947, 15⟩⟩,
  ⟨⟨-177945, 15⟩, ⟨-160801, 15⟩⟩,
  ⟨⟨-321599, 16⟩, ⟨-9105, 11⟩⟩,
  ⟨⟨-291357, 16⟩, ⟨-264583, 16⟩⟩,
  ⟨⟨-66145, 14⟩, ⟨-481565, 17⟩⟩,
  ⟨⟨-481561, 17⟩, ⟨-439107, 17⟩⟩,
  ⟨⟨-439103, 17⟩, ⟨-25069, 13⟩⟩,
  ⟨⟨-401101, 17⟩, ⟨-183493, 16⟩⟩,
  ⟨⟨-366983, 17⟩, ⟨-336261, 17⟩⟩,
  ⟨⟨-168129, 16⟩, ⟨-308515, 17⟩⟩,
  ⟨⟨-308513, 17⟩, ⟨-141697, 16⟩⟩,
  ⟨⟨-283391, 17⟩, ⟨-521181, 18⟩⟩,
  ⟨⟨-260589, 17⟩, ⟨-239845, 17⟩⟩,
  ⟨⟨-479687, 18⟩, ⟨-441855, 18⟩⟩,
  ⟨⟨-110463, 16⟩, ⟨-203643, 17⟩⟩,
  ⟨⟨-407283, 18⟩, ⟨-375639, 18⟩⟩,
  ⟨⟨-375637, 18⟩, ⟨-346613, 18⟩⟩,
  ⟨⟨-346611, 18⟩, ⟨-39993, 15⟩⟩,
  ⟨⟨-319941, 18⟩, ⟨-295405, 18⟩⟩,
  ⟨⟨-295403, 18⟩, ⟨-68197, 16⟩⟩,
  ⟨⟨-136393, 17⟩, ⟨-62979, 16⟩⟩,
  ⟨⟨-503829, 19⟩, ⟨-465259, 19⟩⟩,
  ⟨⟨-58157, 16⟩, ⟨-429575, 19⟩⟩,
  ⟨⟨-107393, 17⟩, ⟨-396523, 19⟩⟩,
  ⟨⟨-49565, 16⟩, ⟨-91471, 17⟩⟩,
  ⟨⟨-365881, 19⟩, ⟨-84363, 17⟩⟩,
  ⟨⟨-337449, 19⟩, ⟨-311051, 19⟩⟩,
  ⟨⟨-311049, 19⟩, ⟨-286519, 19⟩⟩,
  ⟨⟨-71629, 17⟩, ⟨-263709, 19⟩⟩,
  ⟨⟨-131853, 18⟩, ⟨-242489, 19⟩⟩,
  ⟨⟨-484975, 20⟩, ⟨-445489, 20⟩⟩,
  ⟨⟨-222743, 19⟩, ⟨-204365, 19⟩⟩,
  ⟨⟨-408727, 20⟩, ⟨-187255, 19⟩⟩,
  ⟨⟨-374507, 20⟩, ⟨-171327, 19⟩⟩,
  ⟨⟨-342651, 20⟩, ⟨-312999, 20⟩⟩,
  ⟨⟨-312997, 20⟩, ⟨-285403, 20⟩⟩,
  ⟨⟨-285401, 20⟩, ⟨-519459, 21⟩⟩,
  ⟨⟨-519455, 21⟩, ⟨-471719, 21⟩⟩,
  ⟨⟨-471715, 21⟩, ⟨-427361, 21⟩⟩,
  ⟨⟨-213679, 20⟩, ⟨-48273, 18⟩⟩,
  ⟨⟨-96545, 19⟩, ⟨-173997, 20⟩⟩,
  ⟨⟨-173995, 20⟩, ⟨-19539, 17⟩⟩,
  ⟨⟨-312621, 21⟩, ⟨-139955, 20⟩⟩,
  ⟨⟨-279907, 21⟩, ⟨-62427, 19⟩⟩,
  ⟨⟨-124853, 20⟩, ⟨-443755, 22⟩⟩,
  ⟨⟨-443751, 22⟩, ⟨-392579, 22⟩⟩,
  ⟨⟨-392575, 22⟩, ⟨-345655, 22⟩⟩,
  ⟨⟨-345651, 22⟩, ⟨-151375, 21⟩⟩,
  ⟨⟨-151373, 21⟩, ⟨-263653, 22⟩⟩,
  ⟨⟨-263649, 22⟩, ⟨-228159, 22⟩⟩,
  ⟨⟨-456313, 23⟩, ⟨-392149, 23⟩⟩,
  ⟨⟨-24509, 19⟩, ⟨-334429, 23⟩⟩,
  ⟨⟨-334425, 23⟩, ⟨-35349, 20⟩⟩,
  ⟨⟨-70697, 21⟩, ⟨-473759, 24⟩⟩,
  ⟨⟨-473753, 24⟩, ⟨-392703, 24⟩⟩,
  ⟨⟨-196349, 23⟩, ⟨-321723, 24⟩⟩,
  ⟨⟨-160859, 23⟩, ⟨-130067, 23⟩⟩,
  ⟨⟨-130065, 23⟩, ⟨-414491, 25⟩⟩,
  ⟨⟨-414485, 25⟩, ⟨-20297, 21⟩⟩,
  ⟨⟨-324747, 25⟩, ⟨-499329, 26⟩⟩,
  ⟨⟨-62415, 23⟩, ⟨-93913, 24⟩⟩,
  ⟨⟨-375645, 26⟩, ⟨-275679, 26⟩⟩,
  ⟨⟨-275673, 26⟩, ⟨-196585, 26⟩⟩,
  ⟨⟨-393161, 27⟩, ⟨-271155, 27⟩⟩,
  ⟨⟨-67787, 25⟩, ⟨-359665, 28⟩⟩,
  ⟨⟨-359655, 28⟩, ⟨-455469, 29⟩⟩,
  ⟨⟨-455457, 29⟩, ⟨-34111, 26⟩⟩,
  ⟨⟨-272879, 29⟩, ⟨-305867, 30⟩⟩,
  ⟨⟨-4779, 24⟩, ⟨-315967, 31⟩⟩,
  ⟨⟨-315955, 31⟩, ⟨-18435, 28⟩⟩,
  ⟨⟨-294947, 32⟩, ⟨-484701, 34⟩⟩,
  ⟨⟨-484679, 34⟩, ⟨-337911, 35⟩⟩,
  ⟨⟨-337893, 35⟩, ⟨-379605, 37⟩⟩,
  ⟨⟨-379583, 37⟩, ⟨-318293, 39⟩⟩,
  ⟨⟨-318273, 39⟩, ⟨-354465, 42⟩⟩,
  ⟨⟨-354441, 42⟩, ⟨-433935, 46⟩⟩,
  ⟨⟨-27119, 42⟩, ⟨-210643, 50⟩⟩,
  ⟨⟨-421255, 51⟩, ⟨-174393, 57⟩⟩,
  ⟨⟨-348759, 58⟩, ⟨-506753, 70⟩⟩,
  ⟨⟨-506711, 70⟩, ⟨-33917, 87⟩⟩,
  ⟨⟨-135655, 89⟩, ⟨-262149, 141⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private def eulerianCoefficients : List ℤ := [
  0x1, 0x7ffffffffffffffffffffffffffff84, 0x7bac4e64237274c07a5ae310d2803ab9a396aacdba9215405,
  0x3ffffffffffc4188a077ed48f72b598fa03da09e38e14c3054459a13e50000, 0x30684b4bd1e5e24dc0159bee067a516a936fb6eecd0592faf64b8f861c676712ca508b2e, 0x3dd6271a9f34c19f1f53d3df5f138a1d7a0b0471b6fa5bdf5e5b0df12ab020c6b6d4ad5592b223c8,
  0x2786200abc92f857270b58235471080c7a9f21cd54c2848fb4c36c87a64e09737f7f4540c74858741db28be, 0x1fffecdb0805cc9683aff99f06e7d63aa431481097f8b681bdb94704ded65cba2183e2c46d372231e39fccd5de300, 0x3bbe0f4df236e483274d272effb76bafea20afa2ed550c25bb443416c8b90a76f3d5ad82cda80d0843c429552009dc5b67,
  0x183256a139185b408fc4135b6f9d15f5f6994c68f73ee8c96dc97a91b4bcb5e5631c633c9e272b1b014821f0fc1e7c26df7c84c, 0x2d86d152a903f90524f741746a2ad106cf6c0bf0cc0508ca2a42a1235ac1211017e38fa0ebfdf306bde91c1c258c2c6016af83aa94b, 0x1ed5036f0e5c7de63704fed790e7b8ef7c49408c7dd6377afc3b32e5d5790c27cb3fc9088d91fb238f498217f0f0f858455dff44db93500,
  0x8d7e30c029ca44b03aeff68cf2f6085ca10a12bd103fd1073f9bb3c962c83afab56677206da6dd3b2c6ea4a54823abfe3d607e7c7ee6b447ec, 0x137e4d70f1d8cb2d8e5df6bf74c46e612b30c1ceddc0b353e45d4a95101efc1697e716c9023c71cbac8cdd4bb7de97175d14f2a8b9cbb4c76ba310, 0x16ca91e9bcc6ddff48a34420c38c2cc2a8a19bc83fa2932e2b9852be8229c079210feb00dabd59e890306542a4d4b399d5762289c497bf31cd5fb0d2c,
  0xf4d0d339e053a54cbf2dd770ab1819c75022fcf78bb62f78a2b34ace9f7bcb96c06f6b431258496148895a7ef20a027fd22b68bb9023fc93dfe0c5f8100, 0x64a588a0db38bbdedb91a28f89ff1aa37377a482eaecd72365377b62b5e720067a24333627679a4f714b77f0489d3303bf0d959d5eb7c6e9a61980b8ef4665, 0x1ab61b66ab36f20e0723a014670db0ff056ce96d6aef7bd772817933a064f9c1c2835a19b53e0175dab3982bca0cd8a1c4259dbd2cc97a0fd670c3e1fcb625cb4,
  0x4c803676e79106e533bc42620b01f8b62fbef354f09d01f7b8e03c5688ffe50765638cb13b447b534cac2bf2586bd932ce05114c443d70c432eb3f5cf03f1701069, 0x994a976c1798096ee380b3e1cd6de06d758d1c38b5b19d1593a7bfeb0efca1252f11673aed62b3d1dcaf177d61a5a3431e93e869cca2a48c93f5da74726e83cc03700, 0xddac1b447df5104cfacb678006e4662dafa67d6ae285ed54f26efa5843c5227b24e148e6341e7a57fedabb1df2c9d59b0e077513e3cf63cf8346440a58fa1a1dab8edaa,
  0xed877d876e808a2db47882b394a3b6fb05ccae6641a6bd9075a7bd762feea85341e1680be6e157ad7484d0f8285213035064fdd7f88f896b4786bf3cb233cd4bce9450818, 0xc0ec1f2be81f25f6c4824c0f605e5e381ecffd39655a61c48d079b7f67500935fb285abc8c6a93a1c5be23e3af2a529df0f86fe398c3e8951052770da7f464ea83106197f3a, 0x791f259ab74c985126dd33b8c0e63fadaeb6a85b1668e0c0c42fb8e8aca1760f91d120b32e3c2baf21e0db954387cefeac1d485904dbfb458592402d22355bc419ca3bfd27a00,
  0x3bcac4d7c1c7c1cf0eecfddb6c3ab0fb953970644e43e4c1cbee762c13ed507e1eecb403caf04dbdbd250b25d79007e36e36e61caa010bdff2924a045c42814f67b74ba5e3ed67b, 0x178ec3c9d7becdb01021e9f871746b3698030a84f577a10c61cbec27d36bcd58005feabb111de51676684d102099a29205ec83acaa39b9b3340c4d2194081ea64664838a67fcf583c, 0x7817a595aa0cfdb6516206e7f103252875e577212ba25d62808005e627122992e134d5fa56c4552c4654b2ae84d2c9f55a0a965b81ac83a97bf25d6953209d2b313fbe84709373e11f,
  0x1f4dd4ca7befc3a8e3f31c63d4f46941495293c06e3f0cdfeeadb07ffad5b9a647b0c6098263e07ad374d0769f67aaf7457bc9f30596a9da4ddeeecc60c6305b8bed0ab9eb27fde7d600, 0x6bec257c6e4e59e448b63bf505e6aff3fcf62af4e98d76c0c368ccf5bc39c33ce4ab7949e2465f52d0144b12540cf6dab0b962c790ca5aea96335b115c94bc3fc9e235603b3ac4ae46cb8, 0x1366840da16a210cbf2a770db82e711b803cbacb9108232bbc0692a4f4b9db5a9717520cd7d00892ad6973508ba2204e03a6fe17d551983c4517552ced72a87ad359857aab023302aeaefa0,
  0x2ef0217ea46a74d63432fe66b1aefbbf55c338fbc34e39f88f3c1ab717c9c2f7230802a452577d22f4962a3368ee11a805a28edc038901bba883547f4f195dbb4173efb3267eca4f5dfa47b8, 0x603d39f149e287ff491450bad91d7ca56c47510774b3e912ef24532a51f3d961e952e313282cfc9fc2483537dc9fc6e98dc07965f3746b61c5825b2e6e091682df4d28b1f4a0783445108a600, 0xa8581cbcfe4aee67221c3b64fbff4b001dfb29b0ce87197d93b00f81c53bd202eee735d0ab6f8edb6229f47d843d5ee364ddc5f27d7c7279db0e67b1f8357bf8da88ca539038872e67ba2921ad,
  0xfcbfda03250bfa4fe850add2c9d270f8308262c1b6eb2531e1a4e0fa73962414bdee152c052d7ecb1a9d0a7d8cabef837509f645165926b5abd1cd63dc605b72f3e2ee5be76fd2dc5ca71591f74, 0x1477f998694061e3f1f02e31851753820ca8b05d52bce785e5a1d9f8a62ea084138ebda317441a7f4a59a0d94a78a4c6da24b1a51b1ce183806cbf3f02672f81a5f79bd4bd0fa4758dc89bbbfe341, 0x1700f757da5c2ca8b120dc71b37a2a1779caa4c3444a46aee95fa06d66b57a6ce132401d54594b85243f0dedcfac25b4db4e1eadd73256acac965b5234fb7cd82683165e67c2292973f56816f92a00,
  0x1686777d74be5684e0b68edf02b5507a856cdf066f0d7713d9df7504f8993f37f275c3977d53c0c56fbab8a5b091ab45af42ed980bdbd330f279e3951c7dc1030b4e160356f7f5086006ab55957b1be, 0x134c212196141ed2cc7d61e504e727cc16c39710501d804e8254ce01bc7e4667c1b2eb7934a24c2ee740debbb0f2be5308d7765e5395c890b6ae26dc18576571984d49d6d1b254f525fe0c8b7d33f908, 0xe84c5eb2a4884d6cca89fbb47f52a989a184f4db8ab708d59f8251abcc017edbbbe2aec6eb7d43d4d9e463d7cbb1c0e7c7459d0dd86b58455c1bd31ab572a6472ed261dabce65cc54c871208ccc3ec0e,
  0x9a04d95b2bad329218683cd50b8237ffeefe339079cb36c51be7657bab5504cc8e37ce020ad75b7466e0606fd85aee2771f1d3de8f577a155151c90095f6ec04cb3cf265640fa2bdc2e28f1b8ecd47100, 0x5a46e4217534ce2ec250f26ccd86aeb91b2bf24e25ff77829d447742ec7ebbd33624a8c00794a23d7a6cae3cc7028192a4d54f932c13540edf17dac24a3d0ce32b1b5e17f4c25b1ae5488edcca2bca1f8b, 0x2eea43eb3ae56cbf69eccae93b2aa857fbb9ac92c7deaa01b0e000ff8f9a545c97363fdab29a669590a1b0ce062116a57b325038f99333e2a6ff0ec9915f6f76af3942fa3d7f26dd40cf796e1083f6902dc,
  0x15ac7f2a2e09a2c79c7c2f239f903b227bdc3574ba3a6dddcf0554bb7277d61878292d4c4ad318b58000488ae73e5d755c7de5497d4b685a0b3926c2daf36402753e1f89414e3f0356572a12ac54a0b483ff, 0x8ec3dc3f85ed4fb4be1161a55a52090039ef8502261dbbe5c82e703ce99c86cc46b733ada86356a3bbbd1edaa3ad3f41f5b89c68c8691cb834f089260990b532a529b6b25206e9d2557a9e517ea6a2db1700, 0x347e31df062d272f64461b00a12e5228d5f3dacec5af7d25bd5586831ae385199aaf8af95f5cbd9589e9480507367b2bd6248b46f38c6f2b0b6db80f39c496b301233435c520dc9d838a72fd32b27f108c714,
  0x11460057d08aeb3f916d5e14a047ee768a515782a8ec38e7e41fea0dc4b6da27f1f89a0a57ae84fa1e76860ccc76cc804e812744ca1ed8e020c1d09d6b102251359772e77be3c92a819013d8b7389c046895f0, 0x518b01608408c8a3859c71e9cf34977294bd5ddcb39b9f78908dd3bc92c61b2e04f4518a4a9b44a682eee15769c1f83db6ffc34b060784e0902de7e5633bed09623a3097c3e8c6291026822d825b83b7f28154, 0x159bc6776970609a15c606503e3e30826fe912a7f3fabd8e404c161328dffb3dd31b87cd13ad15fc5f156cb374510bd8eec01a4ac35d4b7bb967955bf3dc5ac12e148df4d8171b47d83dafa62e7ec013b8a9300,
  0x526a4a0330530e151804566035b6368e43f0d8b77717fb87ea97ffa4eb22dc2bff000ab355d79a99dcd6af99cf35828db7fd72ce9e5e04c29f39e92e32c08b8f16b8e675bb09168ba83925af54a7a9be4b47b91, 0x11b2844ad6c77e51bdb78b9c4641e38520a48a6273ea74618ae2c369f2135d48fb902ddb22d02bc4d2e65ac98d16af4decec56d1447437e6633ce493df3933e3aeefa6dce0b0f7fa696a1b278d8cfc5f3f7df924, 0x36d7cd6af13cad3e1b3458c70853a6153c9a5858ba9dc7dfcb3623a97919ba9cdbb62b4bdebf3e596e1e7f7c776c9299ea6e3b5e76e88a816e772f6c9f891eb3dd4c46557414947ed6f33ad57aefeb3a483fa6e5,
  0x9978a99daf79c6fae50926497caa96cc0f62e5d3d95f039c4b9aac851c1caa555b4c7a1b672172595b902ea8324862705a9af5ba630acf97ed5df767434feb6abea4f9b1972793202146fdba0a234dbdcd481500, 0x184379c7c7b9440a3142c08b599b5bf16c0e9118cfed4dd100ec4bdf83594ab16a4cd9f2c7c48832f250f38acc94dcce2532ea8416ae17f4ec3e690f454ebcfdf07a730b098ce6a71157e60e948b07527a7b12b8a, 0x378829de11bdb0c74792d5a22cea8cbf53fd7affd2aea3b72f48b51ced5f8961291a2171a2d9c473dbe323cb7fa2d6367efdb94f71e545cb843a745ddf71a3a9cd7a29e67a9924225c7c92e4e32f847de79e15b18,
  0x7315f56f4e9663d7947f835ba1098d33d732a1b527f47428ed3c3bb00ff8351a4a0ac3c84dd8b0e1590d56982db23f493bd1fc6dcdeba006ada7617d9fba2464d7a2926c67e630ce780855b3dd5a2ddf8a9ebd5da, 0xd81f2b22f4a6faf2f213673f070476db9153bf42a2a0edf75bf1099b97439a8ff17f50c077831a3a6c32afaa6f41f7e890ee4fdc59e9a60e03e3327878761686ddd56af1c74d483e328e579c54de99e18b444bc00, 0x16ffd3dc9199f41ea101116f1c03a76ac48bffc28e71efce77c5ca2d3d6d1d10acb54e1111dae7937fa416c7d2e8610aee14218ee5dc0be12399d8989774325ab6677e560cc380636f4ce0dc31ac02d5816be93fff,
  0x238656d926e1f0606b229c6a7633def262628cce9bbc45f69a615b049f0196c81c7816cd28d0b43448b340c3e7d8a8b4a01fc9945d811ed753246257ca808c1fb2c55fe73b6c9829a9425d96d96db56426969667cc, 0x31cc156c540c9551e1cc4d1be994c6f7759e90bd96b4cfd5aa7db29daf404c4abb84b828006589d605691ccd5ebb3d23b35e27108a8d4f5c990ab2ec0048a7a7c23a5792634c391d3a364946c1b814c8cfbd708df3, 0x3f5e5c8b1d0c233da034e714aa98af9d3eb9456e0143c7ba9f9513fce4bec27d543ba979f84f4b4fbdf0f26cac2305c457c6602fbc86ba2a6c193c5aa42d8ba99744059cfbe3cca46f3e3773007f40f2df15612400,
  0x49389dc032535ac20a680e8049534a223446492c0c07d4eae543c633dc0730e4b4c184d0e417b75c7f7c1d63cd7fa65d176038fb5699c1ba5dc3c24ffe4248521738ca80b3db3c72291da246f21b950823acbfee10, 0x4cd563c23fa8464e1785562805696292ebc468f7055ac7f6bebe9b72fb9500ae69fe6911b4893a25cd145beb6742582781ca9f0f1af569d9603c2381f6c252460e7822ab84ae699a3c9415b18da7733842ac68aec0, 0x49389dc032535ac20a680e8049534a223446492c0c07d4eae543c633dc0730e4b4c184d0e417b75c7f7c1d63cd7fa65d176038fb5699c1ba5dc3c24ffe4248521738ca80b3db3c72291da246f21b950823acbfee10,
  0x3f5e5c8b1d0c233da034e714aa98af9d3eb9456e0143c7ba9f9513fce4bec27d543ba979f84f4b4fbdf0f26cac2305c457c6602fbc86ba2a6c193c5aa42d8ba99744059cfbe3cca46f3e3773007f40f2df15612400, 0x31cc156c540c9551e1cc4d1be994c6f7759e90bd96b4cfd5aa7db29daf404c4abb84b828006589d605691ccd5ebb3d23b35e27108a8d4f5c990ab2ec0048a7a7c23a5792634c391d3a364946c1b814c8cfbd708df3, 0x238656d926e1f0606b229c6a7633def262628cce9bbc45f69a615b049f0196c81c7816cd28d0b43448b340c3e7d8a8b4a01fc9945d811ed753246257ca808c1fb2c55fe73b6c9829a9425d96d96db56426969667cc,
  0x16ffd3dc9199f41ea101116f1c03a76ac48bffc28e71efce77c5ca2d3d6d1d10acb54e1111dae7937fa416c7d2e8610aee14218ee5dc0be12399d8989774325ab6677e560cc380636f4ce0dc31ac02d5816be93fff, 0xd81f2b22f4a6faf2f213673f070476db9153bf42a2a0edf75bf1099b97439a8ff17f50c077831a3a6c32afaa6f41f7e890ee4fdc59e9a60e03e3327878761686ddd56af1c74d483e328e579c54de99e18b444bc00, 0x7315f56f4e9663d7947f835ba1098d33d732a1b527f47428ed3c3bb00ff8351a4a0ac3c84dd8b0e1590d56982db23f493bd1fc6dcdeba006ada7617d9fba2464d7a2926c67e630ce780855b3dd5a2ddf8a9ebd5da,
  0x378829de11bdb0c74792d5a22cea8cbf53fd7affd2aea3b72f48b51ced5f8961291a2171a2d9c473dbe323cb7fa2d6367efdb94f71e545cb843a745ddf71a3a9cd7a29e67a9924225c7c92e4e32f847de79e15b18, 0x184379c7c7b9440a3142c08b599b5bf16c0e9118cfed4dd100ec4bdf83594ab16a4cd9f2c7c48832f250f38acc94dcce2532ea8416ae17f4ec3e690f454ebcfdf07a730b098ce6a71157e60e948b07527a7b12b8a, 0x9978a99daf79c6fae50926497caa96cc0f62e5d3d95f039c4b9aac851c1caa555b4c7a1b672172595b902ea8324862705a9af5ba630acf97ed5df767434feb6abea4f9b1972793202146fdba0a234dbdcd481500,
  0x36d7cd6af13cad3e1b3458c70853a6153c9a5858ba9dc7dfcb3623a97919ba9cdbb62b4bdebf3e596e1e7f7c776c9299ea6e3b5e76e88a816e772f6c9f891eb3dd4c46557414947ed6f33ad57aefeb3a483fa6e5, 0x11b2844ad6c77e51bdb78b9c4641e38520a48a6273ea74618ae2c369f2135d48fb902ddb22d02bc4d2e65ac98d16af4decec56d1447437e6633ce493df3933e3aeefa6dce0b0f7fa696a1b278d8cfc5f3f7df924, 0x526a4a0330530e151804566035b6368e43f0d8b77717fb87ea97ffa4eb22dc2bff000ab355d79a99dcd6af99cf35828db7fd72ce9e5e04c29f39e92e32c08b8f16b8e675bb09168ba83925af54a7a9be4b47b91,
  0x159bc6776970609a15c606503e3e30826fe912a7f3fabd8e404c161328dffb3dd31b87cd13ad15fc5f156cb374510bd8eec01a4ac35d4b7bb967955bf3dc5ac12e148df4d8171b47d83dafa62e7ec013b8a9300, 0x518b01608408c8a3859c71e9cf34977294bd5ddcb39b9f78908dd3bc92c61b2e04f4518a4a9b44a682eee15769c1f83db6ffc34b060784e0902de7e5633bed09623a3097c3e8c6291026822d825b83b7f28154, 0x11460057d08aeb3f916d5e14a047ee768a515782a8ec38e7e41fea0dc4b6da27f1f89a0a57ae84fa1e76860ccc76cc804e812744ca1ed8e020c1d09d6b102251359772e77be3c92a819013d8b7389c046895f0,
  0x347e31df062d272f64461b00a12e5228d5f3dacec5af7d25bd5586831ae385199aaf8af95f5cbd9589e9480507367b2bd6248b46f38c6f2b0b6db80f39c496b301233435c520dc9d838a72fd32b27f108c714, 0x8ec3dc3f85ed4fb4be1161a55a52090039ef8502261dbbe5c82e703ce99c86cc46b733ada86356a3bbbd1edaa3ad3f41f5b89c68c8691cb834f089260990b532a529b6b25206e9d2557a9e517ea6a2db1700, 0x15ac7f2a2e09a2c79c7c2f239f903b227bdc3574ba3a6dddcf0554bb7277d61878292d4c4ad318b58000488ae73e5d755c7de5497d4b685a0b3926c2daf36402753e1f89414e3f0356572a12ac54a0b483ff,
  0x2eea43eb3ae56cbf69eccae93b2aa857fbb9ac92c7deaa01b0e000ff8f9a545c97363fdab29a669590a1b0ce062116a57b325038f99333e2a6ff0ec9915f6f76af3942fa3d7f26dd40cf796e1083f6902dc, 0x5a46e4217534ce2ec250f26ccd86aeb91b2bf24e25ff77829d447742ec7ebbd33624a8c00794a23d7a6cae3cc7028192a4d54f932c13540edf17dac24a3d0ce32b1b5e17f4c25b1ae5488edcca2bca1f8b, 0x9a04d95b2bad329218683cd50b8237ffeefe339079cb36c51be7657bab5504cc8e37ce020ad75b7466e0606fd85aee2771f1d3de8f577a155151c90095f6ec04cb3cf265640fa2bdc2e28f1b8ecd47100,
  0xe84c5eb2a4884d6cca89fbb47f52a989a184f4db8ab708d59f8251abcc017edbbbe2aec6eb7d43d4d9e463d7cbb1c0e7c7459d0dd86b58455c1bd31ab572a6472ed261dabce65cc54c871208ccc3ec0e, 0x134c212196141ed2cc7d61e504e727cc16c39710501d804e8254ce01bc7e4667c1b2eb7934a24c2ee740debbb0f2be5308d7765e5395c890b6ae26dc18576571984d49d6d1b254f525fe0c8b7d33f908, 0x1686777d74be5684e0b68edf02b5507a856cdf066f0d7713d9df7504f8993f37f275c3977d53c0c56fbab8a5b091ab45af42ed980bdbd330f279e3951c7dc1030b4e160356f7f5086006ab55957b1be,
  0x1700f757da5c2ca8b120dc71b37a2a1779caa4c3444a46aee95fa06d66b57a6ce132401d54594b85243f0dedcfac25b4db4e1eadd73256acac965b5234fb7cd82683165e67c2292973f56816f92a00, 0x1477f998694061e3f1f02e31851753820ca8b05d52bce785e5a1d9f8a62ea084138ebda317441a7f4a59a0d94a78a4c6da24b1a51b1ce183806cbf3f02672f81a5f79bd4bd0fa4758dc89bbbfe341, 0xfcbfda03250bfa4fe850add2c9d270f8308262c1b6eb2531e1a4e0fa73962414bdee152c052d7ecb1a9d0a7d8cabef837509f645165926b5abd1cd63dc605b72f3e2ee5be76fd2dc5ca71591f74,
  0xa8581cbcfe4aee67221c3b64fbff4b001dfb29b0ce87197d93b00f81c53bd202eee735d0ab6f8edb6229f47d843d5ee364ddc5f27d7c7279db0e67b1f8357bf8da88ca539038872e67ba2921ad, 0x603d39f149e287ff491450bad91d7ca56c47510774b3e912ef24532a51f3d961e952e313282cfc9fc2483537dc9fc6e98dc07965f3746b61c5825b2e6e091682df4d28b1f4a0783445108a600, 0x2ef0217ea46a74d63432fe66b1aefbbf55c338fbc34e39f88f3c1ab717c9c2f7230802a452577d22f4962a3368ee11a805a28edc038901bba883547f4f195dbb4173efb3267eca4f5dfa47b8,
  0x1366840da16a210cbf2a770db82e711b803cbacb9108232bbc0692a4f4b9db5a9717520cd7d00892ad6973508ba2204e03a6fe17d551983c4517552ced72a87ad359857aab023302aeaefa0, 0x6bec257c6e4e59e448b63bf505e6aff3fcf62af4e98d76c0c368ccf5bc39c33ce4ab7949e2465f52d0144b12540cf6dab0b962c790ca5aea96335b115c94bc3fc9e235603b3ac4ae46cb8, 0x1f4dd4ca7befc3a8e3f31c63d4f46941495293c06e3f0cdfeeadb07ffad5b9a647b0c6098263e07ad374d0769f67aaf7457bc9f30596a9da4ddeeecc60c6305b8bed0ab9eb27fde7d600,
  0x7817a595aa0cfdb6516206e7f103252875e577212ba25d62808005e627122992e134d5fa56c4552c4654b2ae84d2c9f55a0a965b81ac83a97bf25d6953209d2b313fbe84709373e11f, 0x178ec3c9d7becdb01021e9f871746b3698030a84f577a10c61cbec27d36bcd58005feabb111de51676684d102099a29205ec83acaa39b9b3340c4d2194081ea64664838a67fcf583c, 0x3bcac4d7c1c7c1cf0eecfddb6c3ab0fb953970644e43e4c1cbee762c13ed507e1eecb403caf04dbdbd250b25d79007e36e36e61caa010bdff2924a045c42814f67b74ba5e3ed67b,
  0x791f259ab74c985126dd33b8c0e63fadaeb6a85b1668e0c0c42fb8e8aca1760f91d120b32e3c2baf21e0db954387cefeac1d485904dbfb458592402d22355bc419ca3bfd27a00, 0xc0ec1f2be81f25f6c4824c0f605e5e381ecffd39655a61c48d079b7f67500935fb285abc8c6a93a1c5be23e3af2a529df0f86fe398c3e8951052770da7f464ea83106197f3a, 0xed877d876e808a2db47882b394a3b6fb05ccae6641a6bd9075a7bd762feea85341e1680be6e157ad7484d0f8285213035064fdd7f88f896b4786bf3cb233cd4bce9450818,
  0xddac1b447df5104cfacb678006e4662dafa67d6ae285ed54f26efa5843c5227b24e148e6341e7a57fedabb1df2c9d59b0e077513e3cf63cf8346440a58fa1a1dab8edaa, 0x994a976c1798096ee380b3e1cd6de06d758d1c38b5b19d1593a7bfeb0efca1252f11673aed62b3d1dcaf177d61a5a3431e93e869cca2a48c93f5da74726e83cc03700, 0x4c803676e79106e533bc42620b01f8b62fbef354f09d01f7b8e03c5688ffe50765638cb13b447b534cac2bf2586bd932ce05114c443d70c432eb3f5cf03f1701069,
  0x1ab61b66ab36f20e0723a014670db0ff056ce96d6aef7bd772817933a064f9c1c2835a19b53e0175dab3982bca0cd8a1c4259dbd2cc97a0fd670c3e1fcb625cb4, 0x64a588a0db38bbdedb91a28f89ff1aa37377a482eaecd72365377b62b5e720067a24333627679a4f714b77f0489d3303bf0d959d5eb7c6e9a61980b8ef4665, 0xf4d0d339e053a54cbf2dd770ab1819c75022fcf78bb62f78a2b34ace9f7bcb96c06f6b431258496148895a7ef20a027fd22b68bb9023fc93dfe0c5f8100,
  0x16ca91e9bcc6ddff48a34420c38c2cc2a8a19bc83fa2932e2b9852be8229c079210feb00dabd59e890306542a4d4b399d5762289c497bf31cd5fb0d2c, 0x137e4d70f1d8cb2d8e5df6bf74c46e612b30c1ceddc0b353e45d4a95101efc1697e716c9023c71cbac8cdd4bb7de97175d14f2a8b9cbb4c76ba310, 0x8d7e30c029ca44b03aeff68cf2f6085ca10a12bd103fd1073f9bb3c962c83afab56677206da6dd3b2c6ea4a54823abfe3d607e7c7ee6b447ec,
  0x1ed5036f0e5c7de63704fed790e7b8ef7c49408c7dd6377afc3b32e5d5790c27cb3fc9088d91fb238f498217f0f0f858455dff44db93500, 0x2d86d152a903f90524f741746a2ad106cf6c0bf0cc0508ca2a42a1235ac1211017e38fa0ebfdf306bde91c1c258c2c6016af83aa94b, 0x183256a139185b408fc4135b6f9d15f5f6994c68f73ee8c96dc97a91b4bcb5e5631c633c9e272b1b014821f0fc1e7c26df7c84c,
  0x3bbe0f4df236e483274d272effb76bafea20afa2ed550c25bb443416c8b90a76f3d5ad82cda80d0843c429552009dc5b67, 0x1fffecdb0805cc9683aff99f06e7d63aa431481097f8b681bdb94704ded65cba2183e2c46d372231e39fccd5de300, 0x2786200abc92f857270b58235471080c7a9f21cd54c2848fb4c36c87a64e09737f7f4540c74858741db28be,
  0x3dd6271a9f34c19f1f53d3df5f138a1d7a0b0471b6fa5bdf5e5b0df12ab020c6b6d4ad5592b223c8, 0x30684b4bd1e5e24dc0159bee067a516a936fb6eecd0592faf64b8f861c676712ca508b2e, 0x3ffffffffffc4188a077ed48f72b598fa03da09e38e14c3054459a13e50000,
  0x7bac4e64237274c07a5ae310d2803ab9a396aacdba9215405, 0x7ffffffffffffffffffffffffffff84, 0x1]

private theorem eulerianCoefficients_eq : descentCoeffs 123 = eulerianCoefficients := by
  decide +kernel

private theorem upper : upperOK (descentCoeffs 123) first gaps = true := by
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

private theorem lower (i : Fin (lastRepresentative 124 - 2)) :
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

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 124) :
    StrictNegativeInterlacing (originalQuotient 124 k) (eulerian 123) 121 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N124
