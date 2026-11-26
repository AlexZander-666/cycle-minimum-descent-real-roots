import LongCycleBounds.DescentEulerianBracketsThrough16
import LongCycleBounds.DescentEulerianBracketData.N017
import LongCycleBounds.DescentEulerianBracketData.N018
import LongCycleBounds.DescentEulerianBracketData.N019
import LongCycleBounds.DescentEulerianBracketData.N020
import LongCycleBounds.DescentEulerianBracketData.N021
import LongCycleBounds.DescentEulerianBracketData.N022
import LongCycleBounds.DescentEulerianBracketData.N023
import LongCycleBounds.DescentEulerianBracketData.N024
import LongCycleBounds.DescentEulerianBracketData.N025
import LongCycleBounds.DescentEulerianBracketData.N026
import LongCycleBounds.DescentEulerianBracketData.N027
import LongCycleBounds.DescentEulerianBracketData.N028
import LongCycleBounds.DescentEulerianBracketData.N029
import LongCycleBounds.DescentEulerianBracketData.N030
import LongCycleBounds.DescentEulerianBracketData.N031
import LongCycleBounds.DescentEulerianBracketData.N032
import LongCycleBounds.DescentEulerianBracketData.N033
import LongCycleBounds.DescentEulerianBracketData.N034
import LongCycleBounds.DescentEulerianBracketData.N035
import LongCycleBounds.DescentEulerianBracketData.N036
import LongCycleBounds.DescentEulerianBracketData.N037
import LongCycleBounds.DescentEulerianBracketData.N038
import LongCycleBounds.DescentEulerianBracketData.N039
import LongCycleBounds.DescentEulerianBracketData.N040

/-! Finite original-row Eulerian bracketing through upper size forty. -/

namespace LongCycleBounds.DescentNecklace.EulerianBrackets
open LongCycleFinite LongCycles

theorem original_through40 {n k : ℕ} (lo : 6 ≤ n) (hi : n ≤ 40) (hk : 3 ≤ k) (kn : k ≤ n) :
    StrictNegativeInterlacing (originalQuotient n k) (eulerian (n - 1)) (n - 3) := by
  by_cases small : n ≤ 16
  · exact original_through16 lo small hk kn
  · interval_cases n
    · exact N017.original hk kn
    · exact N018.original hk kn
    · exact N019.original hk kn
    · exact N020.original hk kn
    · exact N021.original hk kn
    · exact N022.original hk kn
    · exact N023.original hk kn
    · exact N024.original hk kn
    · exact N025.original hk kn
    · exact N026.original hk kn
    · exact N027.original hk kn
    · exact N028.original hk kn
    · exact N029.original hk kn
    · exact N030.original hk kn
    · exact N031.original hk kn
    · exact N032.original hk kn
    · exact N033.original hk kn
    · exact N034.original hk kn
    · exact N035.original hk kn
    · exact N036.original hk kn
    · exact N037.original hk kn
    · exact N038.original hk kn
    · exact N039.original hk kn
    · exact N040.original hk kn

#print axioms original_through40

end LongCycleBounds.DescentNecklace.EulerianBrackets
