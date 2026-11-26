import LongCycleBounds.DescentPackedCutoffs

/-! Radix-coded positive necklace suffix states through degree 127 at alphabet size 1. -/

namespace LongCycleBounds.DescentNecklace.Packed.C127Q001

def code : ℕ → ℕ
  | 128 => 0x1
  | 127 => 0x1
  | 126 => 0x1
  | 125 => 0x1
  | 124 => 0x1
  | 123 => 0x1
  | 122 => 0x1
  | 121 => 0x1
  | 120 => 0x1
  | 119 => 0x1
  | 118 => 0x1
  | 117 => 0x1
  | 116 => 0x1
  | 115 => 0x1
  | 114 => 0x1
  | 113 => 0x1
  | 112 => 0x1
  | 111 => 0x1
  | 110 => 0x1
  | 109 => 0x1
  | 108 => 0x1
  | 107 => 0x1
  | 106 => 0x1
  | 105 => 0x1
  | 104 => 0x1
  | 103 => 0x1
  | 102 => 0x1
  | 101 => 0x1
  | 100 => 0x1
  | 99 => 0x1
  | 98 => 0x1
  | 97 => 0x1
  | 96 => 0x1
  | 95 => 0x1
  | 94 => 0x1
  | 93 => 0x1
  | 92 => 0x1
  | 91 => 0x1
  | 90 => 0x1
  | 89 => 0x1
  | 88 => 0x1
  | 87 => 0x1
  | 86 => 0x1
  | 85 => 0x1
  | 84 => 0x1
  | 83 => 0x1
  | 82 => 0x1
  | 81 => 0x1
  | 80 => 0x1
  | 79 => 0x1
  | 78 => 0x1
  | 77 => 0x1
  | 76 => 0x1
  | 75 => 0x1
  | 74 => 0x1
  | 73 => 0x1
  | 72 => 0x1
  | 71 => 0x1
  | 70 => 0x1
  | 69 => 0x1
  | 68 => 0x1
  | 67 => 0x1
  | 66 => 0x1
  | 65 => 0x1
  | 64 => 0x1
  | 63 => 0x1
  | 62 => 0x1
  | 61 => 0x1
  | 60 => 0x1
  | 59 => 0x1
  | 58 => 0x1
  | 57 => 0x1
  | 56 => 0x1
  | 55 => 0x1
  | 54 => 0x1
  | 53 => 0x1
  | 52 => 0x1
  | 51 => 0x1
  | 50 => 0x1
  | 49 => 0x1
  | 48 => 0x1
  | 47 => 0x1
  | 46 => 0x1
  | 45 => 0x1
  | 44 => 0x1
  | 43 => 0x1
  | 42 => 0x1
  | 41 => 0x1
  | 40 => 0x1
  | 39 => 0x1
  | 38 => 0x1
  | 37 => 0x1
  | 36 => 0x1
  | 35 => 0x1
  | 34 => 0x1
  | 33 => 0x1
  | 32 => 0x1
  | 31 => 0x1
  | 30 => 0x1
  | 29 => 0x1
  | 28 => 0x1
  | 27 => 0x1
  | 26 => 0x1
  | 25 => 0x1
  | 24 => 0x1
  | 23 => 0x1
  | 22 => 0x1
  | 21 => 0x1
  | 20 => 0x1
  | 19 => 0x1
  | 18 => 0x1
  | 17 => 0x1
  | 16 => 0x1
  | 15 => 0x1
  | 14 => 0x1
  | 13 => 0x1
  | 12 => 0x1
  | 11 => 0x1
  | 10 => 0x1
  | 9 => 0x1
  | 8 => 0x1
  | 7 => 0x1
  | 6 => 0x1
  | 5 => 0x1
  | 4 => 0x1
  | 3 => 0x1
  | _ => 0

set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000

private theorem step003 : code 3 =
    codedCutoffStep (cutoffRadix 127 1) 127 3
      (primitiveCount 3 1) (code 4) := by
  decide +kernel

private theorem step004 : code 4 =
    codedCutoffStep (cutoffRadix 127 1) 127 4
      (primitiveCount 4 1) (code 5) := by
  decide +kernel

private theorem step005 : code 5 =
    codedCutoffStep (cutoffRadix 127 1) 127 5
      (primitiveCount 5 1) (code 6) := by
  decide +kernel

private theorem step006 : code 6 =
    codedCutoffStep (cutoffRadix 127 1) 127 6
      (primitiveCount 6 1) (code 7) := by
  decide +kernel

private theorem step007 : code 7 =
    codedCutoffStep (cutoffRadix 127 1) 127 7
      (primitiveCount 7 1) (code 8) := by
  decide +kernel

private theorem step008 : code 8 =
    codedCutoffStep (cutoffRadix 127 1) 127 8
      (primitiveCount 8 1) (code 9) := by
  decide +kernel

private theorem step009 : code 9 =
    codedCutoffStep (cutoffRadix 127 1) 127 9
      (primitiveCount 9 1) (code 10) := by
  decide +kernel

private theorem step010 : code 10 =
    codedCutoffStep (cutoffRadix 127 1) 127 10
      (primitiveCount 10 1) (code 11) := by
  decide +kernel

private theorem step011 : code 11 =
    codedCutoffStep (cutoffRadix 127 1) 127 11
      (primitiveCount 11 1) (code 12) := by
  decide +kernel

private theorem step012 : code 12 =
    codedCutoffStep (cutoffRadix 127 1) 127 12
      (primitiveCount 12 1) (code 13) := by
  decide +kernel

private theorem step013 : code 13 =
    codedCutoffStep (cutoffRadix 127 1) 127 13
      (primitiveCount 13 1) (code 14) := by
  decide +kernel

private theorem step014 : code 14 =
    codedCutoffStep (cutoffRadix 127 1) 127 14
      (primitiveCount 14 1) (code 15) := by
  decide +kernel

private theorem step015 : code 15 =
    codedCutoffStep (cutoffRadix 127 1) 127 15
      (primitiveCount 15 1) (code 16) := by
  decide +kernel

private theorem step016 : code 16 =
    codedCutoffStep (cutoffRadix 127 1) 127 16
      (primitiveCount 16 1) (code 17) := by
  decide +kernel

private theorem step017 : code 17 =
    codedCutoffStep (cutoffRadix 127 1) 127 17
      (primitiveCount 17 1) (code 18) := by
  decide +kernel

private theorem step018 : code 18 =
    codedCutoffStep (cutoffRadix 127 1) 127 18
      (primitiveCount 18 1) (code 19) := by
  decide +kernel

private theorem step019 : code 19 =
    codedCutoffStep (cutoffRadix 127 1) 127 19
      (primitiveCount 19 1) (code 20) := by
  decide +kernel

private theorem step020 : code 20 =
    codedCutoffStep (cutoffRadix 127 1) 127 20
      (primitiveCount 20 1) (code 21) := by
  decide +kernel

private theorem step021 : code 21 =
    codedCutoffStep (cutoffRadix 127 1) 127 21
      (primitiveCount 21 1) (code 22) := by
  decide +kernel

private theorem step022 : code 22 =
    codedCutoffStep (cutoffRadix 127 1) 127 22
      (primitiveCount 22 1) (code 23) := by
  decide +kernel

private theorem step023 : code 23 =
    codedCutoffStep (cutoffRadix 127 1) 127 23
      (primitiveCount 23 1) (code 24) := by
  decide +kernel

private theorem step024 : code 24 =
    codedCutoffStep (cutoffRadix 127 1) 127 24
      (primitiveCount 24 1) (code 25) := by
  decide +kernel

private theorem step025 : code 25 =
    codedCutoffStep (cutoffRadix 127 1) 127 25
      (primitiveCount 25 1) (code 26) := by
  decide +kernel

private theorem step026 : code 26 =
    codedCutoffStep (cutoffRadix 127 1) 127 26
      (primitiveCount 26 1) (code 27) := by
  decide +kernel

private theorem step027 : code 27 =
    codedCutoffStep (cutoffRadix 127 1) 127 27
      (primitiveCount 27 1) (code 28) := by
  decide +kernel

private theorem step028 : code 28 =
    codedCutoffStep (cutoffRadix 127 1) 127 28
      (primitiveCount 28 1) (code 29) := by
  decide +kernel

private theorem step029 : code 29 =
    codedCutoffStep (cutoffRadix 127 1) 127 29
      (primitiveCount 29 1) (code 30) := by
  decide +kernel

private theorem step030 : code 30 =
    codedCutoffStep (cutoffRadix 127 1) 127 30
      (primitiveCount 30 1) (code 31) := by
  decide +kernel

private theorem step031 : code 31 =
    codedCutoffStep (cutoffRadix 127 1) 127 31
      (primitiveCount 31 1) (code 32) := by
  decide +kernel

private theorem step032 : code 32 =
    codedCutoffStep (cutoffRadix 127 1) 127 32
      (primitiveCount 32 1) (code 33) := by
  decide +kernel

private theorem step033 : code 33 =
    codedCutoffStep (cutoffRadix 127 1) 127 33
      (primitiveCount 33 1) (code 34) := by
  decide +kernel

private theorem step034 : code 34 =
    codedCutoffStep (cutoffRadix 127 1) 127 34
      (primitiveCount 34 1) (code 35) := by
  decide +kernel

private theorem step035 : code 35 =
    codedCutoffStep (cutoffRadix 127 1) 127 35
      (primitiveCount 35 1) (code 36) := by
  decide +kernel

private theorem step036 : code 36 =
    codedCutoffStep (cutoffRadix 127 1) 127 36
      (primitiveCount 36 1) (code 37) := by
  decide +kernel

private theorem step037 : code 37 =
    codedCutoffStep (cutoffRadix 127 1) 127 37
      (primitiveCount 37 1) (code 38) := by
  decide +kernel

private theorem step038 : code 38 =
    codedCutoffStep (cutoffRadix 127 1) 127 38
      (primitiveCount 38 1) (code 39) := by
  decide +kernel

private theorem step039 : code 39 =
    codedCutoffStep (cutoffRadix 127 1) 127 39
      (primitiveCount 39 1) (code 40) := by
  decide +kernel

private theorem step040 : code 40 =
    codedCutoffStep (cutoffRadix 127 1) 127 40
      (primitiveCount 40 1) (code 41) := by
  decide +kernel

private theorem step041 : code 41 =
    codedCutoffStep (cutoffRadix 127 1) 127 41
      (primitiveCount 41 1) (code 42) := by
  decide +kernel

private theorem step042 : code 42 =
    codedCutoffStep (cutoffRadix 127 1) 127 42
      (primitiveCount 42 1) (code 43) := by
  decide +kernel

private theorem step043 : code 43 =
    codedCutoffStep (cutoffRadix 127 1) 127 43
      (primitiveCount 43 1) (code 44) := by
  decide +kernel

private theorem step044 : code 44 =
    codedCutoffStep (cutoffRadix 127 1) 127 44
      (primitiveCount 44 1) (code 45) := by
  decide +kernel

private theorem step045 : code 45 =
    codedCutoffStep (cutoffRadix 127 1) 127 45
      (primitiveCount 45 1) (code 46) := by
  decide +kernel

private theorem step046 : code 46 =
    codedCutoffStep (cutoffRadix 127 1) 127 46
      (primitiveCount 46 1) (code 47) := by
  decide +kernel

private theorem step047 : code 47 =
    codedCutoffStep (cutoffRadix 127 1) 127 47
      (primitiveCount 47 1) (code 48) := by
  decide +kernel

private theorem step048 : code 48 =
    codedCutoffStep (cutoffRadix 127 1) 127 48
      (primitiveCount 48 1) (code 49) := by
  decide +kernel

private theorem step049 : code 49 =
    codedCutoffStep (cutoffRadix 127 1) 127 49
      (primitiveCount 49 1) (code 50) := by
  decide +kernel

private theorem step050 : code 50 =
    codedCutoffStep (cutoffRadix 127 1) 127 50
      (primitiveCount 50 1) (code 51) := by
  decide +kernel

private theorem step051 : code 51 =
    codedCutoffStep (cutoffRadix 127 1) 127 51
      (primitiveCount 51 1) (code 52) := by
  decide +kernel

private theorem step052 : code 52 =
    codedCutoffStep (cutoffRadix 127 1) 127 52
      (primitiveCount 52 1) (code 53) := by
  decide +kernel

private theorem step053 : code 53 =
    codedCutoffStep (cutoffRadix 127 1) 127 53
      (primitiveCount 53 1) (code 54) := by
  decide +kernel

private theorem step054 : code 54 =
    codedCutoffStep (cutoffRadix 127 1) 127 54
      (primitiveCount 54 1) (code 55) := by
  decide +kernel

private theorem step055 : code 55 =
    codedCutoffStep (cutoffRadix 127 1) 127 55
      (primitiveCount 55 1) (code 56) := by
  decide +kernel

private theorem step056 : code 56 =
    codedCutoffStep (cutoffRadix 127 1) 127 56
      (primitiveCount 56 1) (code 57) := by
  decide +kernel

private theorem step057 : code 57 =
    codedCutoffStep (cutoffRadix 127 1) 127 57
      (primitiveCount 57 1) (code 58) := by
  decide +kernel

private theorem step058 : code 58 =
    codedCutoffStep (cutoffRadix 127 1) 127 58
      (primitiveCount 58 1) (code 59) := by
  decide +kernel

private theorem step059 : code 59 =
    codedCutoffStep (cutoffRadix 127 1) 127 59
      (primitiveCount 59 1) (code 60) := by
  decide +kernel

private theorem step060 : code 60 =
    codedCutoffStep (cutoffRadix 127 1) 127 60
      (primitiveCount 60 1) (code 61) := by
  decide +kernel

private theorem step061 : code 61 =
    codedCutoffStep (cutoffRadix 127 1) 127 61
      (primitiveCount 61 1) (code 62) := by
  decide +kernel

private theorem step062 : code 62 =
    codedCutoffStep (cutoffRadix 127 1) 127 62
      (primitiveCount 62 1) (code 63) := by
  decide +kernel

private theorem step063 : code 63 =
    codedCutoffStep (cutoffRadix 127 1) 127 63
      (primitiveCount 63 1) (code 64) := by
  decide +kernel

private theorem step064 : code 64 =
    codedCutoffStep (cutoffRadix 127 1) 127 64
      (primitiveCount 64 1) (code 65) := by
  decide +kernel

private theorem step065 : code 65 =
    codedCutoffStep (cutoffRadix 127 1) 127 65
      (primitiveCount 65 1) (code 66) := by
  decide +kernel

private theorem step066 : code 66 =
    codedCutoffStep (cutoffRadix 127 1) 127 66
      (primitiveCount 66 1) (code 67) := by
  decide +kernel

private theorem step067 : code 67 =
    codedCutoffStep (cutoffRadix 127 1) 127 67
      (primitiveCount 67 1) (code 68) := by
  decide +kernel

private theorem step068 : code 68 =
    codedCutoffStep (cutoffRadix 127 1) 127 68
      (primitiveCount 68 1) (code 69) := by
  decide +kernel

private theorem step069 : code 69 =
    codedCutoffStep (cutoffRadix 127 1) 127 69
      (primitiveCount 69 1) (code 70) := by
  decide +kernel

private theorem step070 : code 70 =
    codedCutoffStep (cutoffRadix 127 1) 127 70
      (primitiveCount 70 1) (code 71) := by
  decide +kernel

private theorem step071 : code 71 =
    codedCutoffStep (cutoffRadix 127 1) 127 71
      (primitiveCount 71 1) (code 72) := by
  decide +kernel

private theorem step072 : code 72 =
    codedCutoffStep (cutoffRadix 127 1) 127 72
      (primitiveCount 72 1) (code 73) := by
  decide +kernel

private theorem step073 : code 73 =
    codedCutoffStep (cutoffRadix 127 1) 127 73
      (primitiveCount 73 1) (code 74) := by
  decide +kernel

private theorem step074 : code 74 =
    codedCutoffStep (cutoffRadix 127 1) 127 74
      (primitiveCount 74 1) (code 75) := by
  decide +kernel

private theorem step075 : code 75 =
    codedCutoffStep (cutoffRadix 127 1) 127 75
      (primitiveCount 75 1) (code 76) := by
  decide +kernel

private theorem step076 : code 76 =
    codedCutoffStep (cutoffRadix 127 1) 127 76
      (primitiveCount 76 1) (code 77) := by
  decide +kernel

private theorem step077 : code 77 =
    codedCutoffStep (cutoffRadix 127 1) 127 77
      (primitiveCount 77 1) (code 78) := by
  decide +kernel

private theorem step078 : code 78 =
    codedCutoffStep (cutoffRadix 127 1) 127 78
      (primitiveCount 78 1) (code 79) := by
  decide +kernel

private theorem step079 : code 79 =
    codedCutoffStep (cutoffRadix 127 1) 127 79
      (primitiveCount 79 1) (code 80) := by
  decide +kernel

private theorem step080 : code 80 =
    codedCutoffStep (cutoffRadix 127 1) 127 80
      (primitiveCount 80 1) (code 81) := by
  decide +kernel

private theorem step081 : code 81 =
    codedCutoffStep (cutoffRadix 127 1) 127 81
      (primitiveCount 81 1) (code 82) := by
  decide +kernel

private theorem step082 : code 82 =
    codedCutoffStep (cutoffRadix 127 1) 127 82
      (primitiveCount 82 1) (code 83) := by
  decide +kernel

private theorem step083 : code 83 =
    codedCutoffStep (cutoffRadix 127 1) 127 83
      (primitiveCount 83 1) (code 84) := by
  decide +kernel

private theorem step084 : code 84 =
    codedCutoffStep (cutoffRadix 127 1) 127 84
      (primitiveCount 84 1) (code 85) := by
  decide +kernel

private theorem step085 : code 85 =
    codedCutoffStep (cutoffRadix 127 1) 127 85
      (primitiveCount 85 1) (code 86) := by
  decide +kernel

private theorem step086 : code 86 =
    codedCutoffStep (cutoffRadix 127 1) 127 86
      (primitiveCount 86 1) (code 87) := by
  decide +kernel

private theorem step087 : code 87 =
    codedCutoffStep (cutoffRadix 127 1) 127 87
      (primitiveCount 87 1) (code 88) := by
  decide +kernel

private theorem step088 : code 88 =
    codedCutoffStep (cutoffRadix 127 1) 127 88
      (primitiveCount 88 1) (code 89) := by
  decide +kernel

private theorem step089 : code 89 =
    codedCutoffStep (cutoffRadix 127 1) 127 89
      (primitiveCount 89 1) (code 90) := by
  decide +kernel

private theorem step090 : code 90 =
    codedCutoffStep (cutoffRadix 127 1) 127 90
      (primitiveCount 90 1) (code 91) := by
  decide +kernel

private theorem step091 : code 91 =
    codedCutoffStep (cutoffRadix 127 1) 127 91
      (primitiveCount 91 1) (code 92) := by
  decide +kernel

private theorem step092 : code 92 =
    codedCutoffStep (cutoffRadix 127 1) 127 92
      (primitiveCount 92 1) (code 93) := by
  decide +kernel

private theorem step093 : code 93 =
    codedCutoffStep (cutoffRadix 127 1) 127 93
      (primitiveCount 93 1) (code 94) := by
  decide +kernel

private theorem step094 : code 94 =
    codedCutoffStep (cutoffRadix 127 1) 127 94
      (primitiveCount 94 1) (code 95) := by
  decide +kernel

private theorem step095 : code 95 =
    codedCutoffStep (cutoffRadix 127 1) 127 95
      (primitiveCount 95 1) (code 96) := by
  decide +kernel

private theorem step096 : code 96 =
    codedCutoffStep (cutoffRadix 127 1) 127 96
      (primitiveCount 96 1) (code 97) := by
  decide +kernel

private theorem step097 : code 97 =
    codedCutoffStep (cutoffRadix 127 1) 127 97
      (primitiveCount 97 1) (code 98) := by
  decide +kernel

private theorem step098 : code 98 =
    codedCutoffStep (cutoffRadix 127 1) 127 98
      (primitiveCount 98 1) (code 99) := by
  decide +kernel

private theorem step099 : code 99 =
    codedCutoffStep (cutoffRadix 127 1) 127 99
      (primitiveCount 99 1) (code 100) := by
  decide +kernel

private theorem step100 : code 100 =
    codedCutoffStep (cutoffRadix 127 1) 127 100
      (primitiveCount 100 1) (code 101) := by
  decide +kernel

private theorem step101 : code 101 =
    codedCutoffStep (cutoffRadix 127 1) 127 101
      (primitiveCount 101 1) (code 102) := by
  decide +kernel

private theorem step102 : code 102 =
    codedCutoffStep (cutoffRadix 127 1) 127 102
      (primitiveCount 102 1) (code 103) := by
  decide +kernel

private theorem step103 : code 103 =
    codedCutoffStep (cutoffRadix 127 1) 127 103
      (primitiveCount 103 1) (code 104) := by
  decide +kernel

private theorem step104 : code 104 =
    codedCutoffStep (cutoffRadix 127 1) 127 104
      (primitiveCount 104 1) (code 105) := by
  decide +kernel

private theorem step105 : code 105 =
    codedCutoffStep (cutoffRadix 127 1) 127 105
      (primitiveCount 105 1) (code 106) := by
  decide +kernel

private theorem step106 : code 106 =
    codedCutoffStep (cutoffRadix 127 1) 127 106
      (primitiveCount 106 1) (code 107) := by
  decide +kernel

private theorem step107 : code 107 =
    codedCutoffStep (cutoffRadix 127 1) 127 107
      (primitiveCount 107 1) (code 108) := by
  decide +kernel

private theorem step108 : code 108 =
    codedCutoffStep (cutoffRadix 127 1) 127 108
      (primitiveCount 108 1) (code 109) := by
  decide +kernel

private theorem step109 : code 109 =
    codedCutoffStep (cutoffRadix 127 1) 127 109
      (primitiveCount 109 1) (code 110) := by
  decide +kernel

private theorem step110 : code 110 =
    codedCutoffStep (cutoffRadix 127 1) 127 110
      (primitiveCount 110 1) (code 111) := by
  decide +kernel

private theorem step111 : code 111 =
    codedCutoffStep (cutoffRadix 127 1) 127 111
      (primitiveCount 111 1) (code 112) := by
  decide +kernel

private theorem step112 : code 112 =
    codedCutoffStep (cutoffRadix 127 1) 127 112
      (primitiveCount 112 1) (code 113) := by
  decide +kernel

private theorem step113 : code 113 =
    codedCutoffStep (cutoffRadix 127 1) 127 113
      (primitiveCount 113 1) (code 114) := by
  decide +kernel

private theorem step114 : code 114 =
    codedCutoffStep (cutoffRadix 127 1) 127 114
      (primitiveCount 114 1) (code 115) := by
  decide +kernel

private theorem step115 : code 115 =
    codedCutoffStep (cutoffRadix 127 1) 127 115
      (primitiveCount 115 1) (code 116) := by
  decide +kernel

private theorem step116 : code 116 =
    codedCutoffStep (cutoffRadix 127 1) 127 116
      (primitiveCount 116 1) (code 117) := by
  decide +kernel

private theorem step117 : code 117 =
    codedCutoffStep (cutoffRadix 127 1) 127 117
      (primitiveCount 117 1) (code 118) := by
  decide +kernel

private theorem step118 : code 118 =
    codedCutoffStep (cutoffRadix 127 1) 127 118
      (primitiveCount 118 1) (code 119) := by
  decide +kernel

private theorem step119 : code 119 =
    codedCutoffStep (cutoffRadix 127 1) 127 119
      (primitiveCount 119 1) (code 120) := by
  decide +kernel

private theorem step120 : code 120 =
    codedCutoffStep (cutoffRadix 127 1) 127 120
      (primitiveCount 120 1) (code 121) := by
  decide +kernel

private theorem step121 : code 121 =
    codedCutoffStep (cutoffRadix 127 1) 127 121
      (primitiveCount 121 1) (code 122) := by
  decide +kernel

private theorem step122 : code 122 =
    codedCutoffStep (cutoffRadix 127 1) 127 122
      (primitiveCount 122 1) (code 123) := by
  decide +kernel

private theorem step123 : code 123 =
    codedCutoffStep (cutoffRadix 127 1) 127 123
      (primitiveCount 123 1) (code 124) := by
  decide +kernel

private theorem step124 : code 124 =
    codedCutoffStep (cutoffRadix 127 1) 127 124
      (primitiveCount 124 1) (code 125) := by
  decide +kernel

private theorem step125 : code 125 =
    codedCutoffStep (cutoffRadix 127 1) 127 125
      (primitiveCount 125 1) (code 126) := by
  decide +kernel

private theorem step126 : code 126 =
    codedCutoffStep (cutoffRadix 127 1) 127 126
      (primitiveCount 126 1) (code 127) := by
  decide +kernel

private theorem step127 : code 127 =
    codedCutoffStep (cutoffRadix 127 1) 127 127
      (primitiveCount 127 1) (code 128) := by
  decide +kernel

theorem checked : PackedCutoffChecks 127 1 3 code := by
  refine ⟨by decide +kernel, ?_⟩
  intro k lo hi
  interval_cases k
  · exact step003
  · exact step004
  · exact step005
  · exact step006
  · exact step007
  · exact step008
  · exact step009
  · exact step010
  · exact step011
  · exact step012
  · exact step013
  · exact step014
  · exact step015
  · exact step016
  · exact step017
  · exact step018
  · exact step019
  · exact step020
  · exact step021
  · exact step022
  · exact step023
  · exact step024
  · exact step025
  · exact step026
  · exact step027
  · exact step028
  · exact step029
  · exact step030
  · exact step031
  · exact step032
  · exact step033
  · exact step034
  · exact step035
  · exact step036
  · exact step037
  · exact step038
  · exact step039
  · exact step040
  · exact step041
  · exact step042
  · exact step043
  · exact step044
  · exact step045
  · exact step046
  · exact step047
  · exact step048
  · exact step049
  · exact step050
  · exact step051
  · exact step052
  · exact step053
  · exact step054
  · exact step055
  · exact step056
  · exact step057
  · exact step058
  · exact step059
  · exact step060
  · exact step061
  · exact step062
  · exact step063
  · exact step064
  · exact step065
  · exact step066
  · exact step067
  · exact step068
  · exact step069
  · exact step070
  · exact step071
  · exact step072
  · exact step073
  · exact step074
  · exact step075
  · exact step076
  · exact step077
  · exact step078
  · exact step079
  · exact step080
  · exact step081
  · exact step082
  · exact step083
  · exact step084
  · exact step085
  · exact step086
  · exact step087
  · exact step088
  · exact step089
  · exact step090
  · exact step091
  · exact step092
  · exact step093
  · exact step094
  · exact step095
  · exact step096
  · exact step097
  · exact step098
  · exact step099
  · exact step100
  · exact step101
  · exact step102
  · exact step103
  · exact step104
  · exact step105
  · exact step106
  · exact step107
  · exact step108
  · exact step109
  · exact step110
  · exact step111
  · exact step112
  · exact step113
  · exact step114
  · exact step115
  · exact step116
  · exact step117
  · exact step118
  · exact step119
  · exact step120
  · exact step121
  · exact step122
  · exact step123
  · exact step124
  · exact step125
  · exact step126
  · exact step127

#print axioms checked

end LongCycleBounds.DescentNecklace.Packed.C127Q001
