import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentPackedData.C127L104.N102

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N102

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L104.N102 LongCycleBounds.DescentNecklace.Packed.C127L104.N102.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L104.N102 LongCycleBounds.DescentNecklace.Packed.C127L104.N102.rows

private theorem actual : RepresentativeChecks 102 previousNodes rows :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L104.N102 LongCycleBounds.DescentNecklace.Packed.C127L104.N102.dataChecks

private def first : LongCycleFinite.Dyadic := ⟨-2535301200456458802993406410752, 0⟩

private def gaps : List Window := [
  ⟨⟨-2535218993500725008209526390784, 0⟩, ⟨-640604061644619776, 0⟩⟩,
  ⟨⟨-568545368095064064, 0⟩, ⟨-4168056045568, 0⟩⟩,
  ⟨⟨-4142747615232, 0⟩, ⟨-6111035392, 0⟩⟩,
  ⟨⟨-5921767424, 0⟩, ⟨-95033856, 0⟩⟩,
  ⟨⟨-94746368, 0⟩, ⟨-5296384, 0⟩⟩,
  ⟨⟨-5291824, 0⟩, ⟨-632480, 0⟩⟩,
  ⟨⟨-632236, 0⟩, ⟨-247147, 1⟩⟩,
  ⟨⟨-494185, 2⟩, ⟨-270541, 3⟩⟩,
  ⟨⟨-135251, 2⟩, ⟨-376629, 5⟩⟩,
  ⟨⟨-188295, 4⟩, ⟨-313139, 6⟩⟩,
  ⟨⟨-156557, 5⟩, ⟨-149001, 6⟩⟩,
  ⟨⟨-297983, 7⟩, ⟨-314973, 8⟩⟩,
  ⟨⟨-314957, 8⟩, ⟨-361781, 9⟩⟩,
  ⟨⟨-361765, 9⟩, ⟨-444383, 10⟩⟩,
  ⟨⟨-222183, 9⟩, ⟨-288291, 10⟩⟩,
  ⟨⟨-288281, 10⟩, ⟨-195707, 10⟩⟩,
  ⟨⟨-195701, 10⟩, ⟨-137995, 10⟩⟩,
  ⟨⟨-275983, 11⟩, ⟨-200945, 11⟩⟩,
  ⟨⟨-50235, 9⟩, ⟨-150357, 11⟩⟩,
  ⟨⟨-300707, 12⟩, ⟨-460701, 13⟩⟩,
  ⟨⟨-115173, 11⟩, ⟨-45015, 10⟩⟩,
  ⟨⟨-180057, 12⟩, ⟨-286507, 13⟩⟩,
  ⟨⟨-143251, 12⟩, ⟨-462961, 14⟩⟩,
  ⟨⟨-462953, 14⟩, ⟨-379139, 14⟩⟩,
  ⟨⟨-379133, 14⟩, ⟨-314225, 14⟩⟩,
  ⟨⟨-314221, 14⟩, ⟨-32899, 11⟩⟩,
  ⟨⟨-65797, 12⟩, ⟨-222529, 14⟩⟩,
  ⟨⟨-445053, 15⟩, ⟨-94865, 13⟩⟩,
  ⟨⟨-379455, 15⟩, ⟨-325961, 15⟩⟩,
  ⟨⟨-325957, 15⟩, ⟨-70471, 13⟩⟩,
  ⟨⟨-281881, 15⟩, ⟨-245237, 15⟩⟩,
  ⟨⟨-490469, 16⟩, ⟨-53627, 13⟩⟩,
  ⟨⟨-429011, 16⟩, ⟨-47135, 13⟩⟩,
  ⟨⟨-94269, 14⟩, ⟨-332879, 16⟩⟩,
  ⟨⟨-83219, 14⟩, ⟨-295011, 16⟩⟩,
  ⟨⟨-9219, 11⟩, ⟨-262369, 16⟩⟩,
  ⟨⟨-131183, 15⟩, ⟨-468151, 17⟩⟩,
  ⟨⟨-468147, 17⟩, ⟨-418841, 17⟩⟩,
  ⟨⟨-418837, 17⟩, ⟨-375669, 17⟩⟩,
  ⟨⟨-187833, 16⟩, ⟨-10553, 12⟩⟩,
  ⟨⟨-337693, 17⟩, ⟨-304155, 17⟩⟩,
  ⟨⟨-38019, 14⟩, ⟨-17151, 13⟩⟩,
  ⟨⟨-274413, 17⟩, ⟨-495905, 18⟩⟩,
  ⟨⟨-495901, 18⟩, ⟨-112161, 16⟩⟩,
  ⟨⟨-3505, 11⟩, ⟨-101579, 16⟩⟩,
  ⟨⟨-406313, 18⟩, ⟨-368293, 18⟩⟩,
  ⟨⟨-368289, 18⟩, ⟨-334047, 18⟩⟩,
  ⟨⟨-83511, 16⟩, ⟨-303125, 18⟩⟩,
  ⟨⟨-151561, 17⟩, ⟨-68785, 16⟩⟩,
  ⟨⟨-137569, 17⟩, ⟨-499527, 19⟩⟩,
  ⟨⟨-499523, 19⟩, ⟨-453411, 19⟩⟩,
  ⟨⟨-14169, 14⟩, ⟨-25715, 15⟩⟩,
  ⟨⟨-411437, 19⟩, ⟨-373181, 19⟩⟩,
  ⟨⟨-186589, 18⟩, ⟨-169129, 18⟩⟩,
  ⟨⟨-338255, 19⟩, ⟨-38293, 16⟩⟩,
  ⟨⟨-306341, 19⟩, ⟨-277151, 19⟩⟩,
  ⟨⟨-277149, 19⟩, ⟨-125211, 18⟩⟩,
  ⟨⟨-62605, 17⟩, ⟨-451875, 20⟩⟩,
  ⟨⟨-451871, 20⟩, ⟨-203497, 19⟩⟩,
  ⟨⟨-203495, 19⟩, ⟨-11433, 15⟩⟩,
  ⟨⟨-365853, 20⟩, ⟨-328143, 20⟩⟩,
  ⟨⟨-82035, 18⟩, ⟨-293581, 20⟩⟩,
  ⟨⟨-146789, 19⟩, ⟨-523843, 21⟩⟩,
  ⟨⟨-523839, 21⟩, ⟨-232941, 20⟩⟩,
  ⟨⟨-232939, 20⟩, ⟨-412885, 21⟩⟩,
  ⟨⟨-412881, 21⟩, ⟨-182243, 20⟩⟩,
  ⟨⟨-182241, 20⟩, ⟨-320363, 21⟩⟩,
  ⟨⟨-320359, 21⟩, ⟨-70055, 19⟩⟩,
  ⟨⟨-280217, 21⟩, ⟨-243789, 21⟩⟩,
  ⟨⟨-487573, 22⟩, ⟨-26353, 18⟩⟩,
  ⟨⟨-105411, 20⟩, ⟨-362201, 22⟩⟩,
  ⟨⟨-90549, 20⟩, ⟨-154407, 21⟩⟩,
  ⟨⟨-154405, 21⟩, ⟨-522209, 23⟩⟩,
  ⟨⟨-261101, 22⟩, ⟨-109349, 21⟩⟩,
  ⟨⟨-218695, 22⟩, ⟨-181253, 22⟩⟩,
  ⟨⟨-362501, 23⟩, ⟨-296875, 23⟩⟩,
  ⟨⟨-148435, 22⟩, ⟨-239855, 23⟩⟩,
  ⟨⟨-479703, 24⟩, ⟨-190825, 23⟩⟩,
  ⟨⟨-95411, 22⟩, ⟨-74583, 22⟩⟩,
  ⟨⟨-149163, 23⟩, ⟨-457045, 25⟩⟩,
  ⟨⟨-457037, 25⟩, ⟨-341989, 25⟩⟩,
  ⟨⟨-170991, 24⟩, ⟨-497993, 26⟩⟩,
  ⟨⟨-248991, 25⟩, ⟨-351141, 26⟩⟩,
  ⟨⟨-87783, 24⟩, ⟨-476751, 27⟩⟩,
  ⟨⟨-476739, 27⟩, ⟨-77323, 25⟩⟩,
  ⟨⟨-77321, 25⟩, ⟨-379907, 28⟩⟩,
  ⟨⟨-47487, 25⟩, ⟨-54547, 26⟩⟩,
  ⟨⟨-218181, 28⟩, ⟨-230611, 29⟩⟩,
  ⟨⟨-461205, 30⟩, ⟨-109729, 29⟩⟩,
  ⟨⟨-219449, 30⟩, ⟨-45617, 29⟩⟩,
  ⟨⟨-364919, 32⟩, ⟨-254037, 33⟩⟩,
  ⟨⟨-31753, 30⟩, ⟨-278061, 35⟩⟩,
  ⟨⟨-69511, 33⟩, ⟨-108673, 36⟩⟩,
  ⟨⟨-54333, 35⟩, ⟨-415391, 41⟩⟩,
  ⟨⟨-207681, 40⟩, ⟨-5797, 39⟩⟩,
  ⟨⟨-92745, 43⟩, ⟨-46569, 48⟩⟩,
  ⟨⟨-186261, 50⟩, ⟨-138869, 59⟩⟩,
  ⟨⟨-277715, 60⟩, ⟨-123903, 76⟩⟩,
  ⟨⟨-495565, 78⟩, ⟨-262149, 119⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private def eulerianCoefficients : List ℤ := [
  0x1, 0x1fffffffffffffffffffffff9a, 0x10ed2fb5f35a62c4311c5e66183bd78016da84f92,
  0x3ffffffff9417efd8109fc7cca6eb26352582822f6e4ef5b17a, 0x5b7061a267d170988c5a0ad611c375caeb6c960dc60b6a959b020d39389, 0x21da5d24fa4609b68b0af6031a3571eb160823de49dd87a05fbdc1c94ca45c3af0,
  0xba790b94422d8f7e7efc213940524e95659e8274579ef244ddeb082fa10a4711695d410, 0x7ffb5b399f8910f480dc93843b1fce1c9ca74907f97e0d9a8c207a009a88d38d44da26826ab0, 0x11e4eb908b58230478fe43939e6f8d20555978115844436b41ba8fb91f2668fbe6a9ec847b44427dc,
  0xb66ea5d7d5113bb70e579ac2236c5110ce14fa75c73e8f5630d0dfc5d0c75d75737369a1440262095aa8, 0x2a04149a06cc7f4b92b7cd71f9d1c984c547497635734f373639f905a3a2b514ec88ebe9b882d13af366f0e8, 0x42a7faabf535754ce5c11fc70c714ff4eb272b98bc24048561ec877d9abca8e22542db5c4e774dd5eb78daaa5e8,
  0x33efac6e027a229afa245e036b95b2f0714ca58d823e7cf2c377917c195efbea1baa4af7d5c9be3109dd706dd9b5cc, 0x15fec57136ee29f2c0cb308f743c1859e67ef55c00ba5e82ee381ab4c1b5e6727a368f9140ee3fb0737d23cc5a1902fd0, 0x57b50b1b5b213a83a344ab49256ffc6adf199367027ac660cc2815e22f5943f58470457fd485126eb6034421431ccc039f0,
  0xdb4170b3b80385c7f598272f525fe400cdf8d47f736b84701df82792e2eed15b5c2c2584114054cc2a038aa899c77db0f6690, 0x169a3871d25fbca1126eb7e5b1d47bc99d2438862dbec3e9d1b49ccad4d46db88bcce4e1bfacf56a6ec2150ad70749198c38967a, 0x19a5f34922d3e6d8af80c858c980eafa368257e9b2b3be3d2ea982fddc1ce53001f12a88e76749cc9fc17695a4e12ce62c3b3d23d4,
  0x14bab02f4ead34e8a2b53daec692b2a2bc48c0f55a6866bd190cca0ceee69d70061a8ffd32593bf20c24b167704a3de27773cefb6724, 0xc4894af5a561ee28c79e798b054cf8969ea40903486ffd7468a605bb423eb8d489ab3052d3c39d832d4d8c973b28a0dde489682a86654, 0x57813583a6092b3e1092759244fb927dbbe1c441ed1e4960428721581f29e37fa4669d64b980e4ad8704403b587dbbf2ef57bff079867da,
  0x1de3f91e441f0f3a62ebff4544b1b8a181d0696c8fea52573181af8729d55ae67d3666e96b12b19049f50eef7ce042d9fe09ead9399d753d0, 0x7f99bfadc487c94b50a8c60de6e80ca4ea48b689dd98f10797b03614a49a57e79ba348c4e52108aff6a3888d82d2da8919d30dfb75957eb8b0, 0x1b01ddad350c74399df05a088cc2345038144c287261633c38c90c820e710b134e32ac491239b12c1690b2d5a9d6d7148bf32da3c55061da7210,
  0x4989f73ac0c201f95c9266bffd423d4a83b6e2264b6cfde52858bb5d195740279b3237e459ec2a8edbd96d386751590b216ff268fdef37c7542dc, 0xa2eb0c871b87a8b97a0eaa8b639abf4331738706e50f178c2d4477813fc3ece5674abcda63c15f3491ce9dfc43303869f60f8433849316b3116348, 0x128b8980bd5628755b2d63823cca27d118c35f38e3a66457b1e43482ab01d52dd9ede513e685312c365f0dc7b34743c581c7f24b0566b980a6c68748,
  0x1c05f8fd51eb5b8b6f99c1f7b22c108009a773e393efb1b8c4a02da88cbc3f6020dc24bea25089f2d629e343b658aa50beb7c4b27add4a3918af7bf08, 0x236bbe69f3ad8bef7c4ee1e88867d33779051eb862ce5db0e5019f052aaa86956e93be38d0985afac2a2495bfe77c76a8fd8dd7f586674ffe24c4c702c, 0x25b8d2664ca05e271681fc86e085f6a839213b89ce9782c71600ffd000cfab86861202ef698751034998b78c5cf0587ffab1b9aa5201797e7260546d270,
  0x2211299b1d9aad960a3f14732404b948fe261456a77b61cc622104d684c65ebd0caef26cb882909089a33b7c0efe80399c7bbb871a00b4187ea09bbd0150, 0x1a3de946610f5f664f51c8fd1d360045fbf70d53357536b6c30a5e10256a438c625897cad6c093d91e14f7e6c6b9976abf0b7fa2ae4ab2b7277736bb1dbb0, 0x1154c9b544b22f54c7408ce7440769fa81a1a85bc555e92616c76036dffd49e49c6ba5b9db3c8ebfc491446d14e919e4b0080705d52bd34b8f7ce066b72317,
  0x9dc13925a53e1373c6b2d0a7ab54940d9a1b171c085125dd114e12a7e299de3d2b7025a311fb9734b76de242bbf82b728f4d9ab50547de16aa4457e3c1f226, 0x4da192ae435cc81f5232ce31417fe9a11abb4c4b5e2358b68d6274b5e60f8eb02ceb2948f33c76a0d02b1c33d297dba341a0d15c27932fdd7e34c136467154e, 0x212b87cbac0a46d2c9e2fc5749e5c4227485d0cefcf346c893c6ca95f2aa50b374b014735afdb413d86c61d57c606264ca8565004e435160eda1141a91a6b786,
  0xc58ffdc1cfdab70b79c51d3a22841484b562930f9f3f29b8472fabe10bc16840ac17b46e6fb91b4161a1b957aa937ac9e0a49fbb89ace48e8b66edc6d077fdbf, 0x404491a1c56ff7c8494f7fbe0b0418d52c8ee93f0f25f4227ee898315d14baa7ead392ceca80190ae8677167c4d435e2897b88efaf15d0a98580a7665fbd1a060, 0x1251dd2c5a53928fe4fbbfcb1e4b77bf529e395a27bd45951e384fabaac349aa5ff9d001eceefdb9fda7670de40689841c99f435bea767f07c776ccf836c76f7a0,
  0x496516823c6e794bb94f800ef471eda13ecfb42a13ae399be0829900e80a2898dd8741eb95ae33f6c3bb8ba0beb74d14e46e354a5f8f402eb79cf468e2fe321de0, 0x102daf62a39e27a6aa28529bb404d6aab96b4c9024fd831dda21ebccc52867682ba905e7627ad2b9f5ca185739f41700275df5488c3e137d692baded179d5a05278, 0x32542079c99f77628490b0820687f1d32cce2b51f3a2eff7476c3e23cc11acace43c9775387eb1f63aa878ec30cc29832c1b424eb5028128afd852c39235611ec50,
  0x8a54dd5836c5f21eb64b44dc918baee128a02d38c1c7641420852718281543b7fee4cba61407ff5446e38d687733f07f65f7953291094c07a2c1fc0cc209339bfd0, 0x1506fee01a52f76999d71ac4fdb584c730170d71f4cd09c7ed56b6204c5fb8cc852d00aca482b0ddbb4b710993683a4727ed5164b1edf2912fb084aee169aaffa0d0, 0x2d4fa727fec220664dbe1a2ae069b4fa36c55d958c3d11409684b2b8c4bb4a26c9e45df0b03e98371d8bc09613f266dc5cdbdfd64208090305d22ecc74d9ddf894d8,
  0x569ad4d9454cb53de9ef74a11e7b3c29d40971942395aeba50832235afb3b1b429cb0893701e70031c00d074210704f2c1f2e1b42e96a46d7e1e57b1ba15229f8320, 0x92f546b8e366582bafcd72052602781e7cf4cbbf4ecebd70459ff9e87dc0136d0d7dde699cb126d7d45813b7750a1cfeb4b31a7800245ba5a88a2f70d7625e774060, 0xdd8e1c6ad596f4e52fcef3995c3e910a68db63357763b71bac6a54429cafa2f9236bdb4ec588bb0f44586a55a16db3dc335ac25e70b2706e6b07a46cf48ef2340ea0,
  0x128ee368b08b2c5ccfdeb14d69e2b27941a4842a1a541924319ad16a3aee72c36776e8c2a5096704c965db6c605cff2feabe5ce37fa7484cc563a5a0aabae75b3d54c, 0x161e815ee6d1de3d276b840951eae4fa029674ba403615fb2393a03a60fddfc2583ee40f362c8941a4556c809eb0c34abf6401dcbdefb07df5fbb0a5f0e9e8bed6b18, 0x17738d368ef822383bf7cf3f38c0218f92c816eb49057a63d8ba48185a44e631470f73fb78aeed09dc6e0b33e6a85bcf323adb6a84de70da68be258f727f8a41bf7f8,
  0x161e815ee6d1de3d276b840951eae4fa029674ba403615fb2393a03a60fddfc2583ee40f362c8941a4556c809eb0c34abf6401dcbdefb07df5fbb0a5f0e9e8bed6b18, 0x128ee368b08b2c5ccfdeb14d69e2b27941a4842a1a541924319ad16a3aee72c36776e8c2a5096704c965db6c605cff2feabe5ce37fa7484cc563a5a0aabae75b3d54c, 0xdd8e1c6ad596f4e52fcef3995c3e910a68db63357763b71bac6a54429cafa2f9236bdb4ec588bb0f44586a55a16db3dc335ac25e70b2706e6b07a46cf48ef2340ea0,
  0x92f546b8e366582bafcd72052602781e7cf4cbbf4ecebd70459ff9e87dc0136d0d7dde699cb126d7d45813b7750a1cfeb4b31a7800245ba5a88a2f70d7625e774060, 0x569ad4d9454cb53de9ef74a11e7b3c29d40971942395aeba50832235afb3b1b429cb0893701e70031c00d074210704f2c1f2e1b42e96a46d7e1e57b1ba15229f8320, 0x2d4fa727fec220664dbe1a2ae069b4fa36c55d958c3d11409684b2b8c4bb4a26c9e45df0b03e98371d8bc09613f266dc5cdbdfd64208090305d22ecc74d9ddf894d8,
  0x1506fee01a52f76999d71ac4fdb584c730170d71f4cd09c7ed56b6204c5fb8cc852d00aca482b0ddbb4b710993683a4727ed5164b1edf2912fb084aee169aaffa0d0, 0x8a54dd5836c5f21eb64b44dc918baee128a02d38c1c7641420852718281543b7fee4cba61407ff5446e38d687733f07f65f7953291094c07a2c1fc0cc209339bfd0, 0x32542079c99f77628490b0820687f1d32cce2b51f3a2eff7476c3e23cc11acace43c9775387eb1f63aa878ec30cc29832c1b424eb5028128afd852c39235611ec50,
  0x102daf62a39e27a6aa28529bb404d6aab96b4c9024fd831dda21ebccc52867682ba905e7627ad2b9f5ca185739f41700275df5488c3e137d692baded179d5a05278, 0x496516823c6e794bb94f800ef471eda13ecfb42a13ae399be0829900e80a2898dd8741eb95ae33f6c3bb8ba0beb74d14e46e354a5f8f402eb79cf468e2fe321de0, 0x1251dd2c5a53928fe4fbbfcb1e4b77bf529e395a27bd45951e384fabaac349aa5ff9d001eceefdb9fda7670de40689841c99f435bea767f07c776ccf836c76f7a0,
  0x404491a1c56ff7c8494f7fbe0b0418d52c8ee93f0f25f4227ee898315d14baa7ead392ceca80190ae8677167c4d435e2897b88efaf15d0a98580a7665fbd1a060, 0xc58ffdc1cfdab70b79c51d3a22841484b562930f9f3f29b8472fabe10bc16840ac17b46e6fb91b4161a1b957aa937ac9e0a49fbb89ace48e8b66edc6d077fdbf, 0x212b87cbac0a46d2c9e2fc5749e5c4227485d0cefcf346c893c6ca95f2aa50b374b014735afdb413d86c61d57c606264ca8565004e435160eda1141a91a6b786,
  0x4da192ae435cc81f5232ce31417fe9a11abb4c4b5e2358b68d6274b5e60f8eb02ceb2948f33c76a0d02b1c33d297dba341a0d15c27932fdd7e34c136467154e, 0x9dc13925a53e1373c6b2d0a7ab54940d9a1b171c085125dd114e12a7e299de3d2b7025a311fb9734b76de242bbf82b728f4d9ab50547de16aa4457e3c1f226, 0x1154c9b544b22f54c7408ce7440769fa81a1a85bc555e92616c76036dffd49e49c6ba5b9db3c8ebfc491446d14e919e4b0080705d52bd34b8f7ce066b72317,
  0x1a3de946610f5f664f51c8fd1d360045fbf70d53357536b6c30a5e10256a438c625897cad6c093d91e14f7e6c6b9976abf0b7fa2ae4ab2b7277736bb1dbb0, 0x2211299b1d9aad960a3f14732404b948fe261456a77b61cc622104d684c65ebd0caef26cb882909089a33b7c0efe80399c7bbb871a00b4187ea09bbd0150, 0x25b8d2664ca05e271681fc86e085f6a839213b89ce9782c71600ffd000cfab86861202ef698751034998b78c5cf0587ffab1b9aa5201797e7260546d270,
  0x236bbe69f3ad8bef7c4ee1e88867d33779051eb862ce5db0e5019f052aaa86956e93be38d0985afac2a2495bfe77c76a8fd8dd7f586674ffe24c4c702c, 0x1c05f8fd51eb5b8b6f99c1f7b22c108009a773e393efb1b8c4a02da88cbc3f6020dc24bea25089f2d629e343b658aa50beb7c4b27add4a3918af7bf08, 0x128b8980bd5628755b2d63823cca27d118c35f38e3a66457b1e43482ab01d52dd9ede513e685312c365f0dc7b34743c581c7f24b0566b980a6c68748,
  0xa2eb0c871b87a8b97a0eaa8b639abf4331738706e50f178c2d4477813fc3ece5674abcda63c15f3491ce9dfc43303869f60f8433849316b3116348, 0x4989f73ac0c201f95c9266bffd423d4a83b6e2264b6cfde52858bb5d195740279b3237e459ec2a8edbd96d386751590b216ff268fdef37c7542dc, 0x1b01ddad350c74399df05a088cc2345038144c287261633c38c90c820e710b134e32ac491239b12c1690b2d5a9d6d7148bf32da3c55061da7210,
  0x7f99bfadc487c94b50a8c60de6e80ca4ea48b689dd98f10797b03614a49a57e79ba348c4e52108aff6a3888d82d2da8919d30dfb75957eb8b0, 0x1de3f91e441f0f3a62ebff4544b1b8a181d0696c8fea52573181af8729d55ae67d3666e96b12b19049f50eef7ce042d9fe09ead9399d753d0, 0x57813583a6092b3e1092759244fb927dbbe1c441ed1e4960428721581f29e37fa4669d64b980e4ad8704403b587dbbf2ef57bff079867da,
  0xc4894af5a561ee28c79e798b054cf8969ea40903486ffd7468a605bb423eb8d489ab3052d3c39d832d4d8c973b28a0dde489682a86654, 0x14bab02f4ead34e8a2b53daec692b2a2bc48c0f55a6866bd190cca0ceee69d70061a8ffd32593bf20c24b167704a3de27773cefb6724, 0x19a5f34922d3e6d8af80c858c980eafa368257e9b2b3be3d2ea982fddc1ce53001f12a88e76749cc9fc17695a4e12ce62c3b3d23d4,
  0x169a3871d25fbca1126eb7e5b1d47bc99d2438862dbec3e9d1b49ccad4d46db88bcce4e1bfacf56a6ec2150ad70749198c38967a, 0xdb4170b3b80385c7f598272f525fe400cdf8d47f736b84701df82792e2eed15b5c2c2584114054cc2a038aa899c77db0f6690, 0x57b50b1b5b213a83a344ab49256ffc6adf199367027ac660cc2815e22f5943f58470457fd485126eb6034421431ccc039f0,
  0x15fec57136ee29f2c0cb308f743c1859e67ef55c00ba5e82ee381ab4c1b5e6727a368f9140ee3fb0737d23cc5a1902fd0, 0x33efac6e027a229afa245e036b95b2f0714ca58d823e7cf2c377917c195efbea1baa4af7d5c9be3109dd706dd9b5cc, 0x42a7faabf535754ce5c11fc70c714ff4eb272b98bc24048561ec877d9abca8e22542db5c4e774dd5eb78daaa5e8,
  0x2a04149a06cc7f4b92b7cd71f9d1c984c547497635734f373639f905a3a2b514ec88ebe9b882d13af366f0e8, 0xb66ea5d7d5113bb70e579ac2236c5110ce14fa75c73e8f5630d0dfc5d0c75d75737369a1440262095aa8, 0x11e4eb908b58230478fe43939e6f8d20555978115844436b41ba8fb91f2668fbe6a9ec847b44427dc,
  0x7ffb5b399f8910f480dc93843b1fce1c9ca74907f97e0d9a8c207a009a88d38d44da26826ab0, 0xba790b94422d8f7e7efc213940524e95659e8274579ef244ddeb082fa10a4711695d410, 0x21da5d24fa4609b68b0af6031a3571eb160823de49dd87a05fbdc1c94ca45c3af0,
  0x5b7061a267d170988c5a0ad611c375caeb6c960dc60b6a959b020d39389, 0x3ffffffff9417efd8109fc7cca6eb26352582822f6e4ef5b17a, 0x10ed2fb5f35a62c4311c5e66183bd78016da84f92,
  0x1fffffffffffffffffffffff9a, 0x1]

private theorem eulerianCoefficients_eq : descentCoeffs 101 = eulerianCoefficients := by
  decide +kernel

private theorem upper : upperOK (descentCoeffs 101) first gaps = true := by
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

private theorem lower (i : Fin (lastRepresentative 102 - 2)) :
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

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 102) :
    StrictNegativeInterlacing (originalQuotient 102 k) (eulerian 101) 99 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N102
