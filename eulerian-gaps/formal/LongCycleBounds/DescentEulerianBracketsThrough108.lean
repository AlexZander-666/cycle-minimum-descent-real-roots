import LongCycleBounds.DescentEulerianBracketsThrough88
import LongCycleBounds.DescentEulerianBracketData.N089
import LongCycleBounds.DescentEulerianBracketData.N090
import LongCycleBounds.DescentEulerianBracketData.N091
import LongCycleBounds.DescentEulerianBracketData.N092
import LongCycleBounds.DescentEulerianBracketData.N093
import LongCycleBounds.DescentEulerianBracketData.N094
import LongCycleBounds.DescentEulerianBracketData.N095
import LongCycleBounds.DescentEulerianBracketData.N096
import LongCycleBounds.DescentEulerianBracketData.N097
import LongCycleBounds.DescentEulerianBracketData.N098
import LongCycleBounds.DescentEulerianBracketData.N099
import LongCycleBounds.DescentEulerianBracketData.N100
import LongCycleBounds.DescentEulerianBracketData.N101
import LongCycleBounds.DescentEulerianBracketData.N102
import LongCycleBounds.DescentEulerianBracketData.N103
import LongCycleBounds.DescentEulerianBracketData.N104
import LongCycleBounds.DescentEulerianBracketData.N105
import LongCycleBounds.DescentEulerianBracketData.N106
import LongCycleBounds.DescentEulerianBracketData.N107
import LongCycleBounds.DescentEulerianBracketData.N108

/-! Exact Eulerian bracketing of the original ordinary-descent quotients through upper size 108. -/

namespace LongCycleBounds.DescentNecklace.EulerianBrackets

open LongCycleFinite LongCycles

set_option maxHeartbeats 1000000 in
theorem original_through108 {n k : ℕ} (lo : 6 ≤ n) (hi : n ≤ 108)
    (hk : 3 ≤ k) (kn : k ≤ n) :
    StrictNegativeInterlacing (originalQuotient n k) (eulerian (n - 1)) (n - 3) := by
  by_cases small : n ≤ 88
  · exact original_through88 lo small hk kn
  · interval_cases n
    · exact N089.original hk kn
    · exact N090.original hk kn
    · exact N091.original hk kn
    · exact N092.original hk kn
    · exact N093.original hk kn
    · exact N094.original hk kn
    · exact N095.original hk kn
    · exact N096.original hk kn
    · exact N097.original hk kn
    · exact N098.original hk kn
    · exact N099.original hk kn
    · exact N100.original hk kn
    · exact N101.original hk kn
    · exact N102.original hk kn
    · exact N103.original hk kn
    · exact N104.original hk kn
    · exact N105.original hk kn
    · exact N106.original hk kn
    · exact N107.original hk kn
    · exact N108.original hk kn

#print axioms original_through108

end LongCycleBounds.DescentNecklace.EulerianBrackets
