import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentPackedData.C127L072.N069

namespace LongCycleBounds.DescentNecklace.EulerianBrackets.N069

open LongCycleFinite LongCycles

private abbrev previousNodes : Array LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L072.N069 LongCycleBounds.DescentNecklace.Packed.C127L072.N069.nodes

private abbrev rows : Array (List ℤ) :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L072.N069 LongCycleBounds.DescentNecklace.Packed.C127L072.N069.rows

private theorem actual : RepresentativeChecks 69 previousNodes rows :=
  descentFrozenConst LongCycleBounds.DescentPackedData.C127L072.N069 LongCycleBounds.DescentNecklace.Packed.C127L072.N069.dataChecks

private def first : LongCycleFinite.Dyadic := ⟨-295147905179352825856, 0⟩

private def gaps : List Window := [
  ⟨⟨-295138335030144663552, 0⟩, ⟨-945811357696, 0⟩⟩,
  ⟨⟨-937219325952, 0⟩, ⟨-311746560, 0⟩⟩,
  ⟨⟨-273430528, 0⟩, ⟨-3687600, 0⟩⟩,
  ⟨⟨-3673424, 0⟩, ⟨-215958, 0⟩⟩,
  ⟨⟨-431579, 1⟩, ⟨-238803, 3⟩⟩,
  ⟨⟨-477455, 4⟩, ⟨-441743, 6⟩⟩,
  ⟨⟨-220833, 5⟩, ⟨-285027, 7⟩⟩,
  ⟨⟨-284995, 7⟩, ⟨-461759, 9⟩⟩,
  ⟨⟨-230861, 8⟩, ⟨-439985, 10⟩⟩,
  ⟨⟨-219979, 9⟩, ⟨-59077, 8⟩⟩,
  ⟨⟨-472593, 11⟩, ⟨-139001, 10⟩⟩,
  ⟨⟨-277991, 11⟩, ⟨-350951, 12⟩⟩,
  ⟨⟨-350939, 12⟩, ⟨-234241, 12⟩⟩,
  ⟨⟨-117117, 11⟩, ⟨-10219, 8⟩⟩,
  ⟨⟨-326999, 13⟩, ⟨-118373, 12⟩⟩,
  ⟨⟨-473481, 14⟩, ⟨-176629, 13⟩⟩,
  ⟨⟨-176625, 13⟩, ⟨-270217, 14⟩⟩,
  ⟨⟨-270211, 14⟩, ⟨-105535, 13⟩⟩,
  ⟨⟨-105533, 13⟩, ⟨-167807, 14⟩⟩,
  ⟨⟨-41951, 12⟩, ⟨-270851, 15⟩⟩,
  ⟨⟨-135423, 14⟩, ⟨-442771, 16⟩⟩,
  ⟨⟨-110691, 14⟩, ⟨-91467, 14⟩⟩,
  ⟨⟨-182931, 15⟩, ⟨-152569, 15⟩⟩,
  ⟨⟨-152567, 15⟩, ⟨-513033, 17⟩⟩,
  ⟨⟨-513027, 17⟩, ⟨-434195, 17⟩⟩,
  ⟨⟨-217095, 16⟩, ⟨-369575, 17⟩⟩,
  ⟨⟨-184785, 16⟩, ⟨-158039, 16⟩⟩,
  ⟨⟨-158037, 16⟩, ⟨-135695, 16⟩⟩,
  ⟨⟨-135693, 16⟩, ⟨-58441, 15⟩⟩,
  ⟨⟨-233761, 17⟩, ⟨-1577, 10⟩⟩,
  ⟨⟨-403707, 18⟩, ⟨-174621, 17⟩⟩,
  ⟨⟨-174619, 17⟩, ⟨-151243, 17⟩⟩,
  ⟨⟨-151241, 17⟩, ⟨-262145, 18⟩⟩,
  ⟨⟨-131071, 17⟩, ⟨-454371, 19⟩⟩,
  ⟨⟨-227183, 18⟩, ⟨-393539, 19⟩⟩,
  ⟨⟨-393535, 19⟩, ⟨-170221, 18⟩⟩,
  ⟨⟨-170219, 18⟩, ⟨-293973, 19⟩⟩,
  ⟨⟨-293969, 19⟩, ⟨-253215, 19⟩⟩,
  ⟨⟨-63303, 17⟩, ⟨-434833, 20⟩⟩,
  ⟨⟨-108707, 18⟩, ⟨-371887, 20⟩⟩,
  ⟨⟨-371883, 20⟩, ⟨-316541, 20⟩⟩,
  ⟨⟨-316537, 20⟩, ⟨-267899, 20⟩⟩,
  ⟨⟨-267895, 20⟩, ⟨-225209, 20⟩⟩,
  ⟨⟨-112603, 19⟩, ⟨-375657, 21⟩⟩,
  ⟨⟨-375651, 21⟩, ⟨-77603, 19⟩⟩,
  ⟨⟨-310407, 21⟩, ⟨-253721, 21⟩⟩,
  ⟨⟨-507435, 22⟩, ⟨-409523, 22⟩⟩,
  ⟨⟨-409517, 22⟩, ⟨-20349, 18⟩⟩,
  ⟨⟨-325579, 22⟩, ⟨-508633, 23⟩⟩,
  ⟨⟨-31789, 19⟩, ⟨-24317, 19⟩⟩,
  ⟨⟨-48633, 20⟩, ⟨-290273, 23⟩⟩,
  ⟨⟨-290267, 23⟩, ⟨-420295, 24⟩⟩,
  ⟨⟨-210143, 23⟩, ⟨-293383, 24⟩⟩,
  ⟨⟨-573, 15⟩, ⟨-391629, 25⟩⟩,
  ⟨⟨-195809, 24⟩, ⟨-247203, 25⟩⟩,
  ⟨⟨-494391, 26⟩, ⟨-145409, 25⟩⟩,
  ⟨⟨-36351, 23⟩, ⟨-4881, 21⟩⟩,
  ⟨⟨-78093, 25⟩, ⟨-74415, 26⟩⟩,
  ⟨⟨-297647, 28⟩, ⟨-482235, 30⟩⟩,
  ⟨⟨-482211, 30⟩, ⟨-77785, 29⟩⟩,
  ⟨⟨-155561, 30⟩, ⟨-287871, 33⟩⟩,
  ⟨⟨-287853, 33⟩, ⟨-159225, 35⟩⟩,
  ⟨⟨-318427, 36⟩, ⟨-298877, 40⟩⟩,
  ⟨⟨-149427, 39⟩, ⟨-113733, 45⟩⟩,
  ⟨⟨-454893, 47⟩, ⟨-76495, 56⟩⟩,
  ⟨⟨-305951, 58⟩, ⟨-262165, 86⟩⟩]

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private def eulerianCoefficients : List ℤ := [
  0x1, 0xfffffffffffffffbb, 0xdb6794b881558de83727119d67b,
  0xfffffc4dd14ea3bb4f0c069227840adc81, 0x3b58a38c75aee8fd6171b8ca801c29b7c8966ab0, 0xdb5795cb4279ecabc6ec6817a668efaee73734bccc50,
  0x77355a068ee314bcae5efa777512f5ab49cce058616cb2d0, 0xfdfd689593b95f66edcec95dfca8365125a25fa82b3c09d02b0, 0xb7bea83a86c42e6840d564b873bbb5d952734b3c279a266ef32978,
  0x38371fcd293383dbf8473550a8016663096665590d55de6494ed97f68, 0x87baf021de6af6faa36d9b88479846f48154dc93dcacc24e66096a612e8, 0xb4b5ce6e19d3d9b6bf1b1ff5a8668940a0ab0a47548ab19945502d7844a78,
  0x902bf6be91ee1805f27a7a6707e8cd31c19eddd066963d5a7dfdd4337afd410, 0x49720610c28f8c4463c8d46c4cf301fdb98841e0b30b90864bc9804cadc5b3970, 0x191b289e6e832646d7a1cd096d1ec90f874813af107f124ef9318f3462d8aabe3f0,
  0x5fd869a504f2d289a98d5c762d86d41262715e84acd92c3f5446cf153ef6b048e410, 0x107aa50fcb7fa6d0ff1e3b1d61e37766a41f6df3d8433b8ed1b0e79510c009e48a619c, 0x218785515811d3eca27956f4591ae3aa7089f23eda74725db6ef5d5bd1464caf2d431b4,
  0x338ef1d31764c68d3aa39f114e42c3da735c8fecb6fbc4cce407f7aed1040b8607b74034, 0x3d01f41b72343a5718fee7fb621172012f577249e3ec0ebb0de5f330ae86e9d291fd1c09c, 0x386637f727afedf1d58b27de8e29b342576d70ee2be1177d21367b855dd35c953898791bb0,
  0x294329590259415d2e0961aac0206d73b43026200dbb35d8f3bb40741ac25aff3fc15aa4650, 0x18274a3b2b72dd5d86cbabf342c419aa3e7ddd524f2b4693dfced1e0131c60d25c5e7d76d6d0, 0xb6b23706848bd39b81a2212488c505c8101838621d4a8b34a96c97b289359d47ef25160f7bb0,
  0x464ffd4d2fde1ea49563daaace537b6799385bad4b3a2d7d074c2a7d9d550f9b53b53a22bd748, 0x162e35a8ac742d5a9613b432707639ee9e41eb711c038f7736fc1ff49735c6971c7abd5e1d3158, 0x5c4c33b2bdbe01d12156bfb67221d071c06b37842755e8b4f869f898570fc5dac7153bc3d1fed8,
  0x13e3495dae9c88f25e04bc1e73332cf0078f6f4e492bb587fdf06216db60259cda5e62e863a4448, 0x390ac75868434ba12f085f03f4aceda2238da2a083ac016ab04174788216e7235ea48b3b28cad90, 0x8893bbded756a8c02249807cf8d9ca3040c225d9b0b45d82384ba7fb75b5e1bd803eb62cbd88cf0,
  0x111bcc49f3a7f3bd5ac859290559c3940a6d555ca36addc9e67d7b23f245ccdbebbc7af95d803970, 0x1cc41f76dcf0e8271bc4af35199668c0e7eb90e9344fe13a473cce363fc540241728e6e90da61590, 0x28a3b5a0a400037ad69841837ac9375ef848afea2ea56ba96e8fa484ae644dda423b6c1528d3f1c6,
  0x304a95c70f6eba5a4202cf02fbdd8ca378a12a8388a19d0bb3b487cdfb6f031be8bcfd9fd3417562, 0x304a95c70f6eba5a4202cf02fbdd8ca378a12a8388a19d0bb3b487cdfb6f031be8bcfd9fd3417562, 0x28a3b5a0a400037ad69841837ac9375ef848afea2ea56ba96e8fa484ae644dda423b6c1528d3f1c6,
  0x1cc41f76dcf0e8271bc4af35199668c0e7eb90e9344fe13a473cce363fc540241728e6e90da61590, 0x111bcc49f3a7f3bd5ac859290559c3940a6d555ca36addc9e67d7b23f245ccdbebbc7af95d803970, 0x8893bbded756a8c02249807cf8d9ca3040c225d9b0b45d82384ba7fb75b5e1bd803eb62cbd88cf0,
  0x390ac75868434ba12f085f03f4aceda2238da2a083ac016ab04174788216e7235ea48b3b28cad90, 0x13e3495dae9c88f25e04bc1e73332cf0078f6f4e492bb587fdf06216db60259cda5e62e863a4448, 0x5c4c33b2bdbe01d12156bfb67221d071c06b37842755e8b4f869f898570fc5dac7153bc3d1fed8,
  0x162e35a8ac742d5a9613b432707639ee9e41eb711c038f7736fc1ff49735c6971c7abd5e1d3158, 0x464ffd4d2fde1ea49563daaace537b6799385bad4b3a2d7d074c2a7d9d550f9b53b53a22bd748, 0xb6b23706848bd39b81a2212488c505c8101838621d4a8b34a96c97b289359d47ef25160f7bb0,
  0x18274a3b2b72dd5d86cbabf342c419aa3e7ddd524f2b4693dfced1e0131c60d25c5e7d76d6d0, 0x294329590259415d2e0961aac0206d73b43026200dbb35d8f3bb40741ac25aff3fc15aa4650, 0x386637f727afedf1d58b27de8e29b342576d70ee2be1177d21367b855dd35c953898791bb0,
  0x3d01f41b72343a5718fee7fb621172012f577249e3ec0ebb0de5f330ae86e9d291fd1c09c, 0x338ef1d31764c68d3aa39f114e42c3da735c8fecb6fbc4cce407f7aed1040b8607b74034, 0x218785515811d3eca27956f4591ae3aa7089f23eda74725db6ef5d5bd1464caf2d431b4,
  0x107aa50fcb7fa6d0ff1e3b1d61e37766a41f6df3d8433b8ed1b0e79510c009e48a619c, 0x5fd869a504f2d289a98d5c762d86d41262715e84acd92c3f5446cf153ef6b048e410, 0x191b289e6e832646d7a1cd096d1ec90f874813af107f124ef9318f3462d8aabe3f0,
  0x49720610c28f8c4463c8d46c4cf301fdb98841e0b30b90864bc9804cadc5b3970, 0x902bf6be91ee1805f27a7a6707e8cd31c19eddd066963d5a7dfdd4337afd410, 0xb4b5ce6e19d3d9b6bf1b1ff5a8668940a0ab0a47548ab19945502d7844a78,
  0x87baf021de6af6faa36d9b88479846f48154dc93dcacc24e66096a612e8, 0x38371fcd293383dbf8473550a8016663096665590d55de6494ed97f68, 0xb7bea83a86c42e6840d564b873bbb5d952734b3c279a266ef32978,
  0xfdfd689593b95f66edcec95dfca8365125a25fa82b3c09d02b0, 0x77355a068ee314bcae5efa777512f5ab49cce058616cb2d0, 0xdb5795cb4279ecabc6ec6817a668efaee73734bccc50,
  0x3b58a38c75aee8fd6171b8ca801c29b7c8966ab0, 0xfffffc4dd14ea3bb4f0c069227840adc81, 0xdb6794b881558de83727119d67b,
  0xfffffffffffffffbb, 0x1]

private theorem eulerianCoefficients_eq : descentCoeffs 68 = eulerianCoefficients := by
  decide +kernel

private theorem upper : upperOK (descentCoeffs 68) first gaps = true := by
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

private theorem lower (i : Fin (lastRepresentative 69 - 2)) :
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

theorem original {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 69) :
    StrictNegativeInterlacing (originalQuotient 69 k) (eulerian 68) 66 :=
  original_of_representatives (by decide) actual (by decide) upper lower hk kn

#print axioms original

end LongCycleBounds.DescentNecklace.EulerianBrackets.N069
