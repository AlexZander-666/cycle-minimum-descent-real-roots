import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentPackedData.C127L104.N100

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N100

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L104.N100 LongCycleBounds.DescentNecklace.Packed.C127L104.N100.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L104.N100 LongCycleBounds.DescentNecklace.Packed.C127L104.N100.rows

private theorem actual : RepresentativeChecks 100 previousNodes rows :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L104.N100 LongCycleBounds.DescentNecklace.Packed.C127L104.N100.dataChecks

private def first : LongCycleFinite.Dyadic := ⟨-633825300114114700748351602688, 0⟩

private def gaps : List Window := [
  ⟨⟨-633804748375181252052381597696, 0⟩, ⟨-271313290246750208, 0⟩⟩,
  ⟨⟨-253298341981454336, 0⟩, ⟨-2337032634368, 0⟩⟩,
  ⟨⟨-2326219718656, 0⟩, ⟨-3916185600, 0⟩⟩,
  ⟨⟨-3809329152, 0⟩, ⟨-65710080, 0⟩⟩,
  ⟨⟨-65526400, 0⟩, ⟨-3876520, 0⟩⟩,
  ⟨⟨-3873376, 0⟩, ⟨-482130, 0⟩⟩,
  ⟨⟨-481953, 0⟩, ⟨-194247, 1⟩⟩,
  ⟨⟨-388411, 2⟩, ⟨-435637, 4⟩⟩,
  ⟨⟨-54447, 1⟩, ⟨-309153, 5⟩⟩,
  ⟨⟨-154561, 4⟩, ⟨-522319, 7⟩⟩,
  ⟨⟨-522279, 7⟩, ⟨-503665, 8⟩⟩,
  ⟨⟨-251817, 7⟩, ⟨-269157, 8⟩⟩,
  ⟨⟨-269143, 8⟩, ⟨-39015, 6⟩⟩,
  ⟨⟨-156053, 8⟩, ⟨-193257, 9⟩⟩,
  ⟨⟨-96625, 8⟩, ⟨-252529, 10⟩⟩,
  ⟨⟨-252521, 10⟩, ⟨-43123, 8⟩⟩,
  ⟨⟨-172487, 10⟩, ⟨-244569, 11⟩⟩,
  ⟨⟨-244563, 11⟩, ⟨-357827, 12⟩⟩,
  ⟨⟨-357819, 12⟩, ⟨-268871, 12⟩⟩,
  ⟨⟨-268865, 12⟩, ⟨-413441, 13⟩⟩,
  ⟨⟨-413433, 13⟩, ⟨-324243, 13⟩⟩,
  ⟨⟨-324237, 13⟩, ⟨-517435, 14⟩⟩,
  ⟨⟨-258713, 13⟩, ⟨-209565, 13⟩⟩,
  ⟨⟨-419123, 14⟩, ⟨-344029, 14⟩⟩,
  ⟨⟨-344023, 14⟩, ⟨-71425, 12⟩⟩,
  ⟨⟨-279, 4⟩, ⟨-119861, 13⟩⟩,
  ⟨⟨-239719, 14⟩, ⟨-25375, 11⟩⟩,
  ⟨⟨-202997, 14⟩, ⟨-173311, 14⟩⟩,
  ⟨⟨-173309, 14⟩, ⟨-298093, 15⟩⟩,
  ⟨⟨-298089, 15⟩, ⟨-516071, 16⟩⟩,
  ⟨⟨-516065, 16⟩, ⟨-56167, 13⟩⟩,
  ⟨⟨-449331, 16⟩, ⟨-196643, 15⟩⟩,
  ⟨⟨-196641, 15⟩, ⟨-172923, 15⟩⟩,
  ⟨⟨-172921, 15⟩, ⟨-152705, 15⟩⟩,
  ⟨⟨-152703, 15⟩, ⟨-2115, 9⟩⟩,
  ⟨⟨-270717, 16⟩, ⟨-481565, 17⟩⟩,
  ⟨⟨-60195, 14⟩, ⟨-107401, 15⟩⟩,
  ⟨⟨-13425, 12⟩, ⟨-192137, 16⟩⟩,
  ⟨⟨-384271, 17⟩, ⟨-344547, 17⟩⟩,
  ⟨⟨-344543, 17⟩, ⟨-154787, 16⟩⟩,
  ⟨⟨-154785, 16⟩, ⟨-139329, 16⟩⟩,
  ⟨⟨-278655, 17⟩, ⟨-502447, 18⟩⟩,
  ⟨⟨-502443, 18⟩, ⟨-453589, 18⟩⟩,
  ⟨⟨-453585, 18⟩, ⟨-102485, 16⟩⟩,
  ⟨⟨-25621, 14⟩, ⟨-185413, 17⟩⟩,
  ⟨⟨-185411, 17⟩, ⟨-335677, 18⟩⟩,
  ⟨⟨-167837, 17⟩, ⟨-304007, 18⟩⟩,
  ⟨⟨-304005, 18⟩, ⟨-17213, 14⟩⟩,
  ⟨⟨-275405, 18⟩, ⟨-499043, 19⟩⟩,
  ⟨⟨-499039, 19⟩, ⟨-883, 10⟩⟩,
  ⟨⟨-113023, 17⟩, ⟨-204721, 18⟩⟩,
  ⟨⟨-409439, 19⟩, ⟨-46329, 16⟩⟩,
  ⟨⟨-370629, 19⟩, ⟨-83817, 17⟩⟩,
  ⟨⟨-335265, 19⟩, ⟨-303005, 19⟩⟩,
  ⟨⟨-151501, 18⟩, ⟨-136771, 18⟩⟩,
  ⟨⟨-68385, 17⟩, ⟨-493223, 20⟩⟩,
  ⟨⟨-493219, 20⟩, ⟨-443967, 20⟩⟩,
  ⟨⟨-443963, 20⟩, ⟨-199451, 19⟩⟩,
  ⟨⟨-199449, 19⟩, ⟨-357661, 20⟩⟩,
  ⟨⟨-178829, 19⟩, ⟨-319923, 20⟩⟩,
  ⟨⟨-19995, 16⟩, ⟨-285403, 20⟩⟩,
  ⟨⟨-35675, 17⟩, ⟨-507683, 21⟩⟩,
  ⟨⟨-253839, 20⟩, ⟨-450021, 21⟩⟩,
  ⟨⟨-14063, 16⟩, ⟨-397403, 21⟩⟩,
  ⟨⟨-397399, 21⟩, ⟨-349467, 21⟩⟩,
  ⟨⟨-349463, 21⟩, ⟨-152937, 20⟩⟩,
  ⟨⟨-305871, 21⟩, ⟨-16645, 17⟩⟩,
  ⟨⟨-266317, 21⟩, ⟨-57633, 19⟩⟩,
  ⟨⟨-461059, 22⟩, ⟨-396513, 22⟩⟩,
  ⟨⟨-396509, 22⟩, ⟨-84631, 20⟩⟩,
  ⟨⟨-42315, 19⟩, ⟨-286667, 22⟩⟩,
  ⟨⟨-286663, 22⟩, ⟨-481065, 23⟩⟩,
  ⟨⟨-481059, 23⟩, ⟨-399503, 23⟩⟩,
  ⟨⟨-199749, 22⟩, ⟨-20495, 19⟩⟩,
  ⟨⟨-327915, 23⟩, ⟨-132811, 22⟩⟩,
  ⟨⟨-265617, 23⟩, ⟨-423883, 24⟩⟩,
  ⟨⟨-105969, 22⟩, ⟨-166217, 23⟩⟩,
  ⟨⟨-83107, 22⟩, ⟨-127795, 23⟩⟩,
  ⟨⟨-511171, 25⟩, ⟨-384097, 25⟩⟩,
  ⟨⟨-384089, 25⟩, ⟨-280989, 25⟩⟩,
  ⟨⟨-280983, 25⟩, ⟨-398403, 26⟩⟩,
  ⟨⟨-398393, 26⟩, ⟨-68033, 24⟩⟩,
  ⟨⟨-272125, 26⟩, ⟨-22225, 23⟩⟩,
  ⟨⟨-177795, 26⟩, ⟨-440357, 28⟩⟩,
  ⟨⟨-440343, 28⟩, ⟨-127661, 27⟩⟩,
  ⟨⟨-127657, 27⟩, ⟨-272887, 29⟩⟩,
  ⟨⟨-272877, 29⟩, ⟨-263141, 30⟩⟩,
  ⟨⟨-131565, 29⟩, ⟨-444575, 32⟩⟩,
  ⟨⟨-444555, 32⟩, ⟨-315513, 33⟩⟩,
  ⟨⟨-39437, 30⟩, ⟨-44223, 32⟩⟩,
  ⟨⟨-88441, 33⟩, ⟨-17823, 33⟩⟩,
  ⟨⟨-285149, 37⟩, ⟨-70929, 38⟩⟩,
  ⟨⟨-17731, 36⟩, ⟨-133901, 43⟩⟩,
  ⟨⟨-133891, 43⟩, ⟨-145715, 49⟩⟩,
  ⟨⟨-291407, 50⟩, ⟨-493875, 60⟩⟩,
  ⟨⟨-493833, 60⟩, ⟨-139395, 75⟩⟩,
  ⟨⟨-69691, 74⟩, ⟨-262149, 117⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private def eulerianCoefficients : List ℤ := [
  0x1, 0x7ffffffffffffffffffffff9c, 0x1e17714377bd1fa773c0a7d1f2317f1c9a6819f1,
  0x3ffffffff43ed7c1a53a1f04c6c8be71fd64aa58d3af5af3d0, 0x3a855d2c0f3e5c8c03248a8453cfafaed8fdc092a297feda4e802c2358, 0xf0bb733fa57ef1c741df265f1c641bf9fecd77394944a06d029c3d4bd65cb900,
  0x3ce383b97d04fdc39e66f4dc050087391eb506b301f02cb752329a53b1e30110ef1c38, 0x1ffe8370dfeb8d145293c41cd0295023d35221e1bc83c24d887de74991b317a918dc24281f0, 0x388b8b5f5a876f2b3e0846d35563114b3efb6b1dde35a7125e34f0b1763188d9784df31d9277ae4,
  0x1d2c95a8e9ba8899ba6142ccdf251d2dabdd907ad828057f4cdc57bc2e9c1ad3a122b219dba12ee5470, 0x58c807e0de4e8783b1a90ebda6759b54fc48476561f0c0b1ef3e60c583927312f6278b6eb18e84bc559a84, 0x7630a2c6f3d9a824de86dcba61ca93496cebe4d1a7ceaac5c3f15a841bf0c5bd0113c2f0cafca61eaef2bb6d0,
  0x4e4b718265f2a2f1846d5932fb88c3c7d285e29952b9987eac97d9e6e6f3590989d57223834e995a16d4b9951d08, 0x1c7f6f4f32c6ae7c2c9b3916cc934b2c2a6eb3f5fc70ac9cfe07c8252b16054fbfa31822e7ba629dee15adfba071000, 0x628c468018cb6276f4139def8b4d6260b6316a439c7d61f4365884eef82b22383ba7fac9d1b995be2bd90599f21576568,
  0xd74219504236c57aa9421b69f36136a50912df132c5ae960e915fc29fee81212f09ea0261ecaeaef4e56f3ba47b9e445570, 0x13831ee4203ba6a2044525dd2c042f945ba69a2e5419a2610afb3d88cb152bf7b9e5b070473d043fde7e734742ea63de490e52, 0x1392cbbbcb5c3bfd22cd3a15e82521ed9163815274a42e041550c55dbb89eafeb84ad27197ae3921a1370a865e878193c956dab8,
  0xe0c41f828cc236428f16c8ee56437a3889eed16e76d4939ebf2b04a7d2ffd4fecfc870db70bb1e2318a44b0b16cf02d84ac21bb92, 0x76ba2d261967a710752789c8fd826660442cad417fb12e1408cd59823827d6e2cdef2edac817a08dee2e8e5c8d112715d4e00ddd530, 0x2f4660fca6cdfb208b33ea56998367299abd333ea34afd0d740f2f80bfb3df103718a43cc13a6053bddc468fb5cbced1ed6de77c35688,
  0xe7b565b77980db822ce456cf98f825c19e1301a273fceb78fd43b9f4dd093ce6b2452465b424071fab7fe9b3ac12cf87de8c489168b400, 0x379214b51bad7ee7f6fc469ad406e7e722e8fcced7a6f374ec3560ec046cb62caa65072e72bf637fe4f266be9e091e14547406e3cc8f24a8, 0xa97e68e0a490663779bf480a6a7284a83c733eabcd599962a5252b8b97dac300511bbb0c113a25108c94bc71ff91e3196804d537a9e6eb410,
  0x1a05bf5545672445907a43788d6ca53e5f13d1846d5aba93575238ff5e9b2d5b6dfd460e3200cf4e89ee236e6d5e9f5f4b6fa2cc08f4ec59ef4, 0x3414985a032d43a5a93dc06e6ef407ef7abbf0bd8215a0c98500bacc6ceb9e42076adbf04bbc3d1aed78c5c0b3d640cf7074a63ecb6c099f8ab0, 0x55c9344b243ca4063f04002907d7b92194f696948381f90c0d49cc31145c85974db38e1a120e496b521e341798aa14d0021958ac80c1fc8a94ad4,
  0x75581d6859aed543b05a53907694619eb98b1df2ba73b7ae2e9e54d54400bee89d7cd6ddba698ce040e271337271f3fff10802e16c6d061e8309b0, 0x865b525f528d7c80682ea56d7e8e62bfe6ea3875f67f9328f7b0473e1817af4472fdf11dc6052126d8a0a5b146f427819d942fec2346555fd7eb198, 0x81ae675b8e179146d8c94608cf83a4396db82ef65321647a88c36e337200a5637246a0dda8cb6df38cf737f2937df6b04e0ccc647ab8826b11794100,
  0x6a2ea43632f0064608e20707fdb1f6fa6d1eab046ad848915ee8c579741410ff4d7b1cc160259bee3ff0f1fce2e4636618a2fc7fba8f2b98572659138, 0x4a2b92fbd3961ba5ea7423235a0cae443e55b51176f434ed258ca611c5500c6f68385d8c8a3c8d40b4205a76e821c0ba0a8336042ae9bc365e7ca67710, 0x2c6c231ed333e3c1a1d83dfc4ffaa434b5032c094df8248d4c9939575c3cc9210be93a60d5072b7e2e682105ade144a94e01354d3365cf66fd47c27b29f,
  0x16ea70751d63766f552872285f71d24397b8cfd7308884c4569f4399bac6b5c5a2d9c1dfb5a83a4394180f26efdcabb4b5db289426c8be0a3005d47154a4, 0xa3928f66fd7123f660598a7eff61ec990782778243afaba8d9da72b75e93cf56352f0e3265b483b57a6da07ec1cb7bbca1cff78b28d98eb423e0c93c3a4f, 0x3f56cbf7af8a0a791d618d461364ec1021ff435aa83f326355220238caab96beefe3af4442694aea201519db66748fac62e956765120d04303ce387feac20,
  0x155b9bc4d8d7b47fc3e4fed818d3c75974a2af5822200eec47f8e021a8f36e4a354ff1881ec967ea51ef28093ea89a580bed8f359843457e79c8d6c3b70cf0, 0x64a32555fb5d12e09756a64feecf48df7e1bdaee6d175a726b8aff3b5f5b75654ac04051421cafa697737778b83eda514498dd0101c1c01cd7602565aa8e00, 0x19f3b9fd0beaa20968e35d02e5cda2351966133674926cf4bf104c87d5f2cab7897826a3ffb1d71a52cfd1a2b58d7733502759bbaf5844d94b28f87f94775b0,
  0x5dfb8d96b37597d18f1fbcd9e24ce5686824e4c5b20f531eac5217517e76560aa9564360276c013a0493ab0ac12b168b7b652439f22d95191b95bad9adf3960, 0x12b56ca448935f9885837cb5053eca53c5676226c801147e918968e8d7719cad04f98f44af8570920636aa23bb6920d8f1d66669f9d28d0c47bff9e080685d48, 0x3480eef54cf67b529759ab32ad31f9bd8ebf4a6b99138c33d39923b86de532a7fbca6e61b06afef9784214d6fb5b69e8ffa09b14eda2edb00b1237e377aaf0e0,
  0x8208b06ba09237169ee806eee36d72d7b1af89011c5c79a4ae22fdf46e67f7b9c3d4355dde6b38d5731152244e5ff67e6e3fa65d42369a44456e2386cbda5b88, 0x11c9ad21c07f66c855cbecb174a4d29b8f48e47052eb9ec0123665b172094d5c1dd174e3474f89366f14dc9176871fc73d06792ce60ba89feff439b4801dc1020, 0x2272142e9a85facc84a8f5ff586a341e548b2ce2d2d2e651238cf9e3bd64d4c6ae8d25c35cedfaa820cc577d93e1d9b74e3bdba88295317ffa0dd818c8e9f3ad0,
  0x3b12eb81277fb8c9910ffe4b20fdc7b0500abbb28c306c59f5923e720e8aa8ae9039dee63b2e3c94d9ce75862949881e2e4193161cf6da196b67271f67a0fb400, 0x59cb5ec6f1ce9d601065c02dfbfa0870fd4d436af75bccd515229b3c205a5d14e5eee49c80aea61add9678a5149c07d536963697d252807e543626f2143a3c290, 0x790c56bd6d4089ed1c573ce25954fa7fe9f3208e3fe1b8cf8ffc46228e908bd170d20384c86ee2d3f030a6a1ddf0063333af06f895c74550257c08731a1c27e60,
  0x90c7c0ecad7461b9787d221570e90a8f40e7189bb061c88487679dadfd3382ee1d33323d0eade86011cc251f2bf7fdb92e353b27b0cfd9d916ed60a0aed1a773c, 0x99adc9667b0e052466457f20c7f812d2d093b9c9a805fe5b577b830643269fc2c94a93013422b1ca676c7825e8f47b8e388400b9f18595ab09f3a68c375fe0210, 0x90c7c0ecad7461b9787d221570e90a8f40e7189bb061c88487679dadfd3382ee1d33323d0eade86011cc251f2bf7fdb92e353b27b0cfd9d916ed60a0aed1a773c,
  0x790c56bd6d4089ed1c573ce25954fa7fe9f3208e3fe1b8cf8ffc46228e908bd170d20384c86ee2d3f030a6a1ddf0063333af06f895c74550257c08731a1c27e60, 0x59cb5ec6f1ce9d601065c02dfbfa0870fd4d436af75bccd515229b3c205a5d14e5eee49c80aea61add9678a5149c07d536963697d252807e543626f2143a3c290, 0x3b12eb81277fb8c9910ffe4b20fdc7b0500abbb28c306c59f5923e720e8aa8ae9039dee63b2e3c94d9ce75862949881e2e4193161cf6da196b67271f67a0fb400,
  0x2272142e9a85facc84a8f5ff586a341e548b2ce2d2d2e651238cf9e3bd64d4c6ae8d25c35cedfaa820cc577d93e1d9b74e3bdba88295317ffa0dd818c8e9f3ad0, 0x11c9ad21c07f66c855cbecb174a4d29b8f48e47052eb9ec0123665b172094d5c1dd174e3474f89366f14dc9176871fc73d06792ce60ba89feff439b4801dc1020, 0x8208b06ba09237169ee806eee36d72d7b1af89011c5c79a4ae22fdf46e67f7b9c3d4355dde6b38d5731152244e5ff67e6e3fa65d42369a44456e2386cbda5b88,
  0x3480eef54cf67b529759ab32ad31f9bd8ebf4a6b99138c33d39923b86de532a7fbca6e61b06afef9784214d6fb5b69e8ffa09b14eda2edb00b1237e377aaf0e0, 0x12b56ca448935f9885837cb5053eca53c5676226c801147e918968e8d7719cad04f98f44af8570920636aa23bb6920d8f1d66669f9d28d0c47bff9e080685d48, 0x5dfb8d96b37597d18f1fbcd9e24ce5686824e4c5b20f531eac5217517e76560aa9564360276c013a0493ab0ac12b168b7b652439f22d95191b95bad9adf3960,
  0x19f3b9fd0beaa20968e35d02e5cda2351966133674926cf4bf104c87d5f2cab7897826a3ffb1d71a52cfd1a2b58d7733502759bbaf5844d94b28f87f94775b0, 0x64a32555fb5d12e09756a64feecf48df7e1bdaee6d175a726b8aff3b5f5b75654ac04051421cafa697737778b83eda514498dd0101c1c01cd7602565aa8e00, 0x155b9bc4d8d7b47fc3e4fed818d3c75974a2af5822200eec47f8e021a8f36e4a354ff1881ec967ea51ef28093ea89a580bed8f359843457e79c8d6c3b70cf0,
  0x3f56cbf7af8a0a791d618d461364ec1021ff435aa83f326355220238caab96beefe3af4442694aea201519db66748fac62e956765120d04303ce387feac20, 0xa3928f66fd7123f660598a7eff61ec990782778243afaba8d9da72b75e93cf56352f0e3265b483b57a6da07ec1cb7bbca1cff78b28d98eb423e0c93c3a4f, 0x16ea70751d63766f552872285f71d24397b8cfd7308884c4569f4399bac6b5c5a2d9c1dfb5a83a4394180f26efdcabb4b5db289426c8be0a3005d47154a4,
  0x2c6c231ed333e3c1a1d83dfc4ffaa434b5032c094df8248d4c9939575c3cc9210be93a60d5072b7e2e682105ade144a94e01354d3365cf66fd47c27b29f, 0x4a2b92fbd3961ba5ea7423235a0cae443e55b51176f434ed258ca611c5500c6f68385d8c8a3c8d40b4205a76e821c0ba0a8336042ae9bc365e7ca67710, 0x6a2ea43632f0064608e20707fdb1f6fa6d1eab046ad848915ee8c579741410ff4d7b1cc160259bee3ff0f1fce2e4636618a2fc7fba8f2b98572659138,
  0x81ae675b8e179146d8c94608cf83a4396db82ef65321647a88c36e337200a5637246a0dda8cb6df38cf737f2937df6b04e0ccc647ab8826b11794100, 0x865b525f528d7c80682ea56d7e8e62bfe6ea3875f67f9328f7b0473e1817af4472fdf11dc6052126d8a0a5b146f427819d942fec2346555fd7eb198, 0x75581d6859aed543b05a53907694619eb98b1df2ba73b7ae2e9e54d54400bee89d7cd6ddba698ce040e271337271f3fff10802e16c6d061e8309b0,
  0x55c9344b243ca4063f04002907d7b92194f696948381f90c0d49cc31145c85974db38e1a120e496b521e341798aa14d0021958ac80c1fc8a94ad4, 0x3414985a032d43a5a93dc06e6ef407ef7abbf0bd8215a0c98500bacc6ceb9e42076adbf04bbc3d1aed78c5c0b3d640cf7074a63ecb6c099f8ab0, 0x1a05bf5545672445907a43788d6ca53e5f13d1846d5aba93575238ff5e9b2d5b6dfd460e3200cf4e89ee236e6d5e9f5f4b6fa2cc08f4ec59ef4,
  0xa97e68e0a490663779bf480a6a7284a83c733eabcd599962a5252b8b97dac300511bbb0c113a25108c94bc71ff91e3196804d537a9e6eb410, 0x379214b51bad7ee7f6fc469ad406e7e722e8fcced7a6f374ec3560ec046cb62caa65072e72bf637fe4f266be9e091e14547406e3cc8f24a8, 0xe7b565b77980db822ce456cf98f825c19e1301a273fceb78fd43b9f4dd093ce6b2452465b424071fab7fe9b3ac12cf87de8c489168b400,
  0x2f4660fca6cdfb208b33ea56998367299abd333ea34afd0d740f2f80bfb3df103718a43cc13a6053bddc468fb5cbced1ed6de77c35688, 0x76ba2d261967a710752789c8fd826660442cad417fb12e1408cd59823827d6e2cdef2edac817a08dee2e8e5c8d112715d4e00ddd530, 0xe0c41f828cc236428f16c8ee56437a3889eed16e76d4939ebf2b04a7d2ffd4fecfc870db70bb1e2318a44b0b16cf02d84ac21bb92,
  0x1392cbbbcb5c3bfd22cd3a15e82521ed9163815274a42e041550c55dbb89eafeb84ad27197ae3921a1370a865e878193c956dab8, 0x13831ee4203ba6a2044525dd2c042f945ba69a2e5419a2610afb3d88cb152bf7b9e5b070473d043fde7e734742ea63de490e52, 0xd74219504236c57aa9421b69f36136a50912df132c5ae960e915fc29fee81212f09ea0261ecaeaef4e56f3ba47b9e445570,
  0x628c468018cb6276f4139def8b4d6260b6316a439c7d61f4365884eef82b22383ba7fac9d1b995be2bd90599f21576568, 0x1c7f6f4f32c6ae7c2c9b3916cc934b2c2a6eb3f5fc70ac9cfe07c8252b16054fbfa31822e7ba629dee15adfba071000, 0x4e4b718265f2a2f1846d5932fb88c3c7d285e29952b9987eac97d9e6e6f3590989d57223834e995a16d4b9951d08,
  0x7630a2c6f3d9a824de86dcba61ca93496cebe4d1a7ceaac5c3f15a841bf0c5bd0113c2f0cafca61eaef2bb6d0, 0x58c807e0de4e8783b1a90ebda6759b54fc48476561f0c0b1ef3e60c583927312f6278b6eb18e84bc559a84, 0x1d2c95a8e9ba8899ba6142ccdf251d2dabdd907ad828057f4cdc57bc2e9c1ad3a122b219dba12ee5470,
  0x388b8b5f5a876f2b3e0846d35563114b3efb6b1dde35a7125e34f0b1763188d9784df31d9277ae4, 0x1ffe8370dfeb8d145293c41cd0295023d35221e1bc83c24d887de74991b317a918dc24281f0, 0x3ce383b97d04fdc39e66f4dc050087391eb506b301f02cb752329a53b1e30110ef1c38,
  0xf0bb733fa57ef1c741df265f1c641bf9fecd77394944a06d029c3d4bd65cb900, 0x3a855d2c0f3e5c8c03248a8453cfafaed8fdc092a297feda4e802c2358, 0x3ffffffff43ed7c1a53a1f04c6c8be71fd64aa58d3af5af3d0,
  0x1e17714377bd1fa773c0a7d1f2317f1c9a6819f1, 0x7ffffffffffffffffffffff9c, 0x1]

private theorem eulerianCoefficients_eq : descentCoeffs 99 = eulerianCoefficients := by
  decide +kernel

private theorem upper : upperOK (descentCoeffs 99) first gaps = true := by
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

private theorem lower (i : Fin (lastRepresentative 100 - 2)) :
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

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 100) :
    StrictNegativeInterlacing (originalQuotient 100 k) (eulerian 99) 97 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N100
