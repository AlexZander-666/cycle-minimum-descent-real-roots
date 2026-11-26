import LongCycleBounds.DescentPackedData.C127Q001
import LongCycleBounds.DescentPackedData.C127Q002
import LongCycleBounds.DescentPackedData.C127Q003
import LongCycleBounds.DescentPackedData.C127Q004
import LongCycleBounds.DescentPackedData.C127Q005
import LongCycleBounds.DescentPackedData.C127Q006
import LongCycleBounds.DescentPackedData.C127Q007
import LongCycleBounds.DescentPackedData.C127Q008
import LongCycleBounds.DescentPackedData.C127Q009
import LongCycleBounds.DescentPackedData.C127Q010
import LongCycleBounds.DescentPackedData.C127Q011
import LongCycleBounds.DescentPackedData.C127Q012
import LongCycleBounds.DescentPackedData.C127Q013
import LongCycleBounds.DescentPackedData.C127Q014
import LongCycleBounds.DescentPackedData.C127Q015
import LongCycleBounds.DescentPackedData.C127Q016
import LongCycleBounds.DescentPackedData.C127Q017
import LongCycleBounds.DescentPackedData.C127Q018
import LongCycleBounds.DescentPackedData.C127Q019
import LongCycleBounds.DescentPackedData.C127Q020
import LongCycleBounds.DescentPackedData.C127Q021
import LongCycleBounds.DescentPackedData.C127Q022
import LongCycleBounds.DescentPackedData.C127Q023
import LongCycleBounds.DescentPackedData.C127Q024
import LongCycleBounds.DescentPackedData.C127Q025
import LongCycleBounds.DescentPackedData.C127Q026
import LongCycleBounds.DescentPackedData.C127Q027
import LongCycleBounds.DescentPackedData.C127Q028
import LongCycleBounds.DescentPackedData.C127Q029
import LongCycleBounds.DescentPackedData.C127Q030
import LongCycleBounds.DescentPackedData.C127Q031
import LongCycleBounds.DescentPackedData.C127Q032
import LongCycleBounds.DescentPackedData.C127Q033
import LongCycleBounds.DescentPackedData.C127Q034
import LongCycleBounds.DescentPackedData.C127Q035
import LongCycleBounds.DescentPackedData.C127Q036
import LongCycleBounds.DescentPackedData.C127Q037
import LongCycleBounds.DescentPackedData.C127Q038
import LongCycleBounds.DescentPackedData.C127Q039
import LongCycleBounds.DescentPackedData.C127Q040
import LongCycleBounds.DescentPackedData.C127Q041
import LongCycleBounds.DescentPackedData.C127Q042
import LongCycleBounds.DescentPackedData.C127Q043
import LongCycleBounds.DescentPackedData.C127Q044
import LongCycleBounds.DescentPackedData.C127Q045
import LongCycleBounds.DescentPackedData.C127Q046
import LongCycleBounds.DescentPackedData.C127Q047
import LongCycleBounds.DescentPackedData.C127Q048
import LongCycleBounds.DescentPackedData.C127Q049
import LongCycleBounds.DescentPackedData.C127Q050
import LongCycleBounds.DescentPackedData.C127Q051
import LongCycleBounds.DescentPackedData.C127Q052
import LongCycleBounds.DescentPackedData.C127Q053
import LongCycleBounds.DescentPackedData.C127Q054
import LongCycleBounds.DescentPackedData.C127Q055
import LongCycleBounds.DescentPackedData.C127Q056

/-! The first 56 checked alphabets, all computed at degree cap 127. -/

namespace LongCycleBounds.DescentNecklace.Packed.C127L056

def rawCode : ℕ → ℕ → ℕ
  | 0 => C127Q001.code
  | 1 => C127Q002.code
  | 2 => C127Q003.code
  | 3 => C127Q004.code
  | 4 => C127Q005.code
  | 5 => C127Q006.code
  | 6 => C127Q007.code
  | 7 => C127Q008.code
  | 8 => C127Q009.code
  | 9 => C127Q010.code
  | 10 => C127Q011.code
  | 11 => C127Q012.code
  | 12 => C127Q013.code
  | 13 => C127Q014.code
  | 14 => C127Q015.code
  | 15 => C127Q016.code
  | 16 => C127Q017.code
  | 17 => C127Q018.code
  | 18 => C127Q019.code
  | 19 => C127Q020.code
  | 20 => C127Q021.code
  | 21 => C127Q022.code
  | 22 => C127Q023.code
  | 23 => C127Q024.code
  | 24 => C127Q025.code
  | 25 => C127Q026.code
  | 26 => C127Q027.code
  | 27 => C127Q028.code
  | 28 => C127Q029.code
  | 29 => C127Q030.code
  | 30 => C127Q031.code
  | 31 => C127Q032.code
  | 32 => C127Q033.code
  | 33 => C127Q034.code
  | 34 => C127Q035.code
  | 35 => C127Q036.code
  | 36 => C127Q037.code
  | 37 => C127Q038.code
  | 38 => C127Q039.code
  | 39 => C127Q040.code
  | 40 => C127Q041.code
  | 41 => C127Q042.code
  | 42 => C127Q043.code
  | 43 => C127Q044.code
  | 44 => C127Q045.code
  | 45 => C127Q046.code
  | 46 => C127Q047.code
  | 47 => C127Q048.code
  | 48 => C127Q049.code
  | 49 => C127Q050.code
  | 50 => C127Q051.code
  | 51 => C127Q052.code
  | 52 => C127Q053.code
  | 53 => C127Q054.code
  | 54 => C127Q055.code
  | 55 => C127Q056.code
  | _ => fun _ ↦ 0

def codes (i : Fin 56) : ℕ → ℕ := rawCode i.val

set_option maxHeartbeats 6000000 in
theorem checked (i : Fin 56) : PackedCutoffChecks 127 (i.val + 1) 3 (codes i) := by
  obtain ⟨i, fits⟩ := i
  interval_cases i
  · exact C127Q001.checked
  · exact C127Q002.checked
  · exact C127Q003.checked
  · exact C127Q004.checked
  · exact C127Q005.checked
  · exact C127Q006.checked
  · exact C127Q007.checked
  · exact C127Q008.checked
  · exact C127Q009.checked
  · exact C127Q010.checked
  · exact C127Q011.checked
  · exact C127Q012.checked
  · exact C127Q013.checked
  · exact C127Q014.checked
  · exact C127Q015.checked
  · exact C127Q016.checked
  · exact C127Q017.checked
  · exact C127Q018.checked
  · exact C127Q019.checked
  · exact C127Q020.checked
  · exact C127Q021.checked
  · exact C127Q022.checked
  · exact C127Q023.checked
  · exact C127Q024.checked
  · exact C127Q025.checked
  · exact C127Q026.checked
  · exact C127Q027.checked
  · exact C127Q028.checked
  · exact C127Q029.checked
  · exact C127Q030.checked
  · exact C127Q031.checked
  · exact C127Q032.checked
  · exact C127Q033.checked
  · exact C127Q034.checked
  · exact C127Q035.checked
  · exact C127Q036.checked
  · exact C127Q037.checked
  · exact C127Q038.checked
  · exact C127Q039.checked
  · exact C127Q040.checked
  · exact C127Q041.checked
  · exact C127Q042.checked
  · exact C127Q043.checked
  · exact C127Q044.checked
  · exact C127Q045.checked
  · exact C127Q046.checked
  · exact C127Q047.checked
  · exact C127Q048.checked
  · exact C127Q049.checked
  · exact C127Q050.checked
  · exact C127Q051.checked
  · exact C127Q052.checked
  · exact C127Q053.checked
  · exact C127Q054.checked
  · exact C127Q055.checked
  · exact C127Q056.checked

#print axioms checked

end LongCycleBounds.DescentNecklace.Packed.C127L056
