import LongCycleBounds.DescentEulerianBracketsThrough108
import LongCycleBounds.DescentEulerianBracketData.N109
import LongCycleBounds.DescentEulerianBracketData.N110
import LongCycleBounds.DescentEulerianBracketData.N111
import LongCycleBounds.DescentEulerianBracketData.N112
import LongCycleBounds.DescentEulerianBracketData.N113
import LongCycleBounds.DescentEulerianBracketData.N114
import LongCycleBounds.DescentEulerianBracketData.N115
import LongCycleBounds.DescentEulerianBracketData.N116
import LongCycleBounds.DescentEulerianBracketData.N117
import LongCycleBounds.DescentEulerianBracketData.N118
import LongCycleBounds.DescentEulerianBracketData.N119
import LongCycleBounds.DescentEulerianBracketData.N120
import LongCycleBounds.DescentEulerianBracketData.N121
import LongCycleBounds.DescentEulerianBracketData.N122
import LongCycleBounds.DescentEulerianBracketData.N123
import LongCycleBounds.DescentEulerianBracketData.N124
import LongCycleBounds.DescentEulerianBracketData.N125
import LongCycleBounds.DescentEulerianBracketData.N126
import LongCycleBounds.DescentEulerianBracketData.N127

/-! Exact Eulerian bracketing of the original ordinary-descent quotients through upper size 127. -/

namespace LongCycleBounds.DescentNecklace.EulerianBrackets

open LongCycleFinite LongCycles

set_option maxHeartbeats 1000000 in
theorem original_through127 {n k : ℕ} (lo : 6 ≤ n) (hi : n ≤ 127)
    (hk : 3 ≤ k) (kn : k ≤ n) :
    StrictNegativeInterlacing (originalQuotient n k) (eulerian (n - 1)) (n - 3) := by
  by_cases small : n ≤ 108
  · exact original_through108 lo small hk kn
  · interval_cases n
    · exact N109.original hk kn
    · exact N110.original hk kn
    · exact N111.original hk kn
    · exact N112.original hk kn
    · exact N113.original hk kn
    · exact N114.original hk kn
    · exact N115.original hk kn
    · exact N116.original hk kn
    · exact N117.original hk kn
    · exact N118.original hk kn
    · exact N119.original hk kn
    · exact N120.original hk kn
    · exact N121.original hk kn
    · exact N122.original hk kn
    · exact N123.original hk kn
    · exact N124.original hk kn
    · exact N125.original hk kn
    · exact N126.original hk kn
    · exact N127.original hk kn

#print axioms original_through127

end LongCycleBounds.DescentNecklace.EulerianBrackets
