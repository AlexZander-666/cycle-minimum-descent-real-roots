import LongCycleBounds.DescentPackedCutoffs

/-! Radix-coded positive necklace suffix states through degree 48 at alphabet size 1. -/

namespace LongCycleBounds.DescentNecklace.Packed.C048Q001

def code : ℕ → ℕ
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
    codedCutoffStep (cutoffRadix 48 1) 48 3
      (primitiveCount 3 1) (code 4) := by
  decide +kernel

private theorem step004 : code 4 =
    codedCutoffStep (cutoffRadix 48 1) 48 4
      (primitiveCount 4 1) (code 5) := by
  decide +kernel

private theorem step005 : code 5 =
    codedCutoffStep (cutoffRadix 48 1) 48 5
      (primitiveCount 5 1) (code 6) := by
  decide +kernel

private theorem step006 : code 6 =
    codedCutoffStep (cutoffRadix 48 1) 48 6
      (primitiveCount 6 1) (code 7) := by
  decide +kernel

private theorem step007 : code 7 =
    codedCutoffStep (cutoffRadix 48 1) 48 7
      (primitiveCount 7 1) (code 8) := by
  decide +kernel

private theorem step008 : code 8 =
    codedCutoffStep (cutoffRadix 48 1) 48 8
      (primitiveCount 8 1) (code 9) := by
  decide +kernel

private theorem step009 : code 9 =
    codedCutoffStep (cutoffRadix 48 1) 48 9
      (primitiveCount 9 1) (code 10) := by
  decide +kernel

private theorem step010 : code 10 =
    codedCutoffStep (cutoffRadix 48 1) 48 10
      (primitiveCount 10 1) (code 11) := by
  decide +kernel

private theorem step011 : code 11 =
    codedCutoffStep (cutoffRadix 48 1) 48 11
      (primitiveCount 11 1) (code 12) := by
  decide +kernel

private theorem step012 : code 12 =
    codedCutoffStep (cutoffRadix 48 1) 48 12
      (primitiveCount 12 1) (code 13) := by
  decide +kernel

private theorem step013 : code 13 =
    codedCutoffStep (cutoffRadix 48 1) 48 13
      (primitiveCount 13 1) (code 14) := by
  decide +kernel

private theorem step014 : code 14 =
    codedCutoffStep (cutoffRadix 48 1) 48 14
      (primitiveCount 14 1) (code 15) := by
  decide +kernel

private theorem step015 : code 15 =
    codedCutoffStep (cutoffRadix 48 1) 48 15
      (primitiveCount 15 1) (code 16) := by
  decide +kernel

private theorem step016 : code 16 =
    codedCutoffStep (cutoffRadix 48 1) 48 16
      (primitiveCount 16 1) (code 17) := by
  decide +kernel

private theorem step017 : code 17 =
    codedCutoffStep (cutoffRadix 48 1) 48 17
      (primitiveCount 17 1) (code 18) := by
  decide +kernel

private theorem step018 : code 18 =
    codedCutoffStep (cutoffRadix 48 1) 48 18
      (primitiveCount 18 1) (code 19) := by
  decide +kernel

private theorem step019 : code 19 =
    codedCutoffStep (cutoffRadix 48 1) 48 19
      (primitiveCount 19 1) (code 20) := by
  decide +kernel

private theorem step020 : code 20 =
    codedCutoffStep (cutoffRadix 48 1) 48 20
      (primitiveCount 20 1) (code 21) := by
  decide +kernel

private theorem step021 : code 21 =
    codedCutoffStep (cutoffRadix 48 1) 48 21
      (primitiveCount 21 1) (code 22) := by
  decide +kernel

private theorem step022 : code 22 =
    codedCutoffStep (cutoffRadix 48 1) 48 22
      (primitiveCount 22 1) (code 23) := by
  decide +kernel

private theorem step023 : code 23 =
    codedCutoffStep (cutoffRadix 48 1) 48 23
      (primitiveCount 23 1) (code 24) := by
  decide +kernel

private theorem step024 : code 24 =
    codedCutoffStep (cutoffRadix 48 1) 48 24
      (primitiveCount 24 1) (code 25) := by
  decide +kernel

private theorem step025 : code 25 =
    codedCutoffStep (cutoffRadix 48 1) 48 25
      (primitiveCount 25 1) (code 26) := by
  decide +kernel

private theorem step026 : code 26 =
    codedCutoffStep (cutoffRadix 48 1) 48 26
      (primitiveCount 26 1) (code 27) := by
  decide +kernel

private theorem step027 : code 27 =
    codedCutoffStep (cutoffRadix 48 1) 48 27
      (primitiveCount 27 1) (code 28) := by
  decide +kernel

private theorem step028 : code 28 =
    codedCutoffStep (cutoffRadix 48 1) 48 28
      (primitiveCount 28 1) (code 29) := by
  decide +kernel

private theorem step029 : code 29 =
    codedCutoffStep (cutoffRadix 48 1) 48 29
      (primitiveCount 29 1) (code 30) := by
  decide +kernel

private theorem step030 : code 30 =
    codedCutoffStep (cutoffRadix 48 1) 48 30
      (primitiveCount 30 1) (code 31) := by
  decide +kernel

private theorem step031 : code 31 =
    codedCutoffStep (cutoffRadix 48 1) 48 31
      (primitiveCount 31 1) (code 32) := by
  decide +kernel

private theorem step032 : code 32 =
    codedCutoffStep (cutoffRadix 48 1) 48 32
      (primitiveCount 32 1) (code 33) := by
  decide +kernel

private theorem step033 : code 33 =
    codedCutoffStep (cutoffRadix 48 1) 48 33
      (primitiveCount 33 1) (code 34) := by
  decide +kernel

private theorem step034 : code 34 =
    codedCutoffStep (cutoffRadix 48 1) 48 34
      (primitiveCount 34 1) (code 35) := by
  decide +kernel

private theorem step035 : code 35 =
    codedCutoffStep (cutoffRadix 48 1) 48 35
      (primitiveCount 35 1) (code 36) := by
  decide +kernel

private theorem step036 : code 36 =
    codedCutoffStep (cutoffRadix 48 1) 48 36
      (primitiveCount 36 1) (code 37) := by
  decide +kernel

private theorem step037 : code 37 =
    codedCutoffStep (cutoffRadix 48 1) 48 37
      (primitiveCount 37 1) (code 38) := by
  decide +kernel

private theorem step038 : code 38 =
    codedCutoffStep (cutoffRadix 48 1) 48 38
      (primitiveCount 38 1) (code 39) := by
  decide +kernel

private theorem step039 : code 39 =
    codedCutoffStep (cutoffRadix 48 1) 48 39
      (primitiveCount 39 1) (code 40) := by
  decide +kernel

private theorem step040 : code 40 =
    codedCutoffStep (cutoffRadix 48 1) 48 40
      (primitiveCount 40 1) (code 41) := by
  decide +kernel

private theorem step041 : code 41 =
    codedCutoffStep (cutoffRadix 48 1) 48 41
      (primitiveCount 41 1) (code 42) := by
  decide +kernel

private theorem step042 : code 42 =
    codedCutoffStep (cutoffRadix 48 1) 48 42
      (primitiveCount 42 1) (code 43) := by
  decide +kernel

private theorem step043 : code 43 =
    codedCutoffStep (cutoffRadix 48 1) 48 43
      (primitiveCount 43 1) (code 44) := by
  decide +kernel

private theorem step044 : code 44 =
    codedCutoffStep (cutoffRadix 48 1) 48 44
      (primitiveCount 44 1) (code 45) := by
  decide +kernel

private theorem step045 : code 45 =
    codedCutoffStep (cutoffRadix 48 1) 48 45
      (primitiveCount 45 1) (code 46) := by
  decide +kernel

private theorem step046 : code 46 =
    codedCutoffStep (cutoffRadix 48 1) 48 46
      (primitiveCount 46 1) (code 47) := by
  decide +kernel

private theorem step047 : code 47 =
    codedCutoffStep (cutoffRadix 48 1) 48 47
      (primitiveCount 47 1) (code 48) := by
  decide +kernel

private theorem step048 : code 48 =
    codedCutoffStep (cutoffRadix 48 1) 48 48
      (primitiveCount 48 1) (code 49) := by
  decide +kernel

theorem checked : PackedCutoffChecks 48 1 3 code := by
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

#print axioms checked

end LongCycleBounds.DescentNecklace.Packed.C048Q001
