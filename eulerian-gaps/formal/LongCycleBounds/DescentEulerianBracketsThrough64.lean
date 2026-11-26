import LongCycleBounds.DescentEulerianBracketsThrough40
import LongCycleBounds.DescentEulerianBracketData.N041
import LongCycleBounds.DescentEulerianBracketData.N042
import LongCycleBounds.DescentEulerianBracketData.N043
import LongCycleBounds.DescentEulerianBracketData.N044
import LongCycleBounds.DescentEulerianBracketData.N045
import LongCycleBounds.DescentEulerianBracketData.N046
import LongCycleBounds.DescentEulerianBracketData.N047
import LongCycleBounds.DescentEulerianBracketData.N048
import LongCycleBounds.DescentEulerianBracketData.N049
import LongCycleBounds.DescentEulerianBracketData.N050
import LongCycleBounds.DescentEulerianBracketData.N051
import LongCycleBounds.DescentEulerianBracketData.N052
import LongCycleBounds.DescentEulerianBracketData.N053
import LongCycleBounds.DescentEulerianBracketData.N054
import LongCycleBounds.DescentEulerianBracketData.N055
import LongCycleBounds.DescentEulerianBracketData.N056
import LongCycleBounds.DescentEulerianBracketData.N057
import LongCycleBounds.DescentEulerianBracketData.N058
import LongCycleBounds.DescentEulerianBracketData.N059
import LongCycleBounds.DescentEulerianBracketData.N060
import LongCycleBounds.DescentEulerianBracketData.N061
import LongCycleBounds.DescentEulerianBracketData.N062
import LongCycleBounds.DescentEulerianBracketData.N063
import LongCycleBounds.DescentEulerianBracketData.N064

/-! Exact Eulerian bracketing of the original ordinary-descent quotients through upper size 64. -/

namespace LongCycleBounds.DescentNecklace.EulerianBrackets

open LongCycleFinite LongCycles

set_option maxHeartbeats 1000000 in
theorem original_through64 {n k : ℕ} (lo : 6 ≤ n) (hi : n ≤ 64)
    (hk : 3 ≤ k) (kn : k ≤ n) :
    StrictNegativeInterlacing (originalQuotient n k) (eulerian (n - 1)) (n - 3) := by
  by_cases small : n ≤ 40
  · exact original_through40 lo small hk kn
  · interval_cases n
    · exact N041.original hk kn
    · exact N042.original hk kn
    · exact N043.original hk kn
    · exact N044.original hk kn
    · exact N045.original hk kn
    · exact N046.original hk kn
    · exact N047.original hk kn
    · exact N048.original hk kn
    · exact N049.original hk kn
    · exact N050.original hk kn
    · exact N051.original hk kn
    · exact N052.original hk kn
    · exact N053.original hk kn
    · exact N054.original hk kn
    · exact N055.original hk kn
    · exact N056.original hk kn
    · exact N057.original hk kn
    · exact N058.original hk kn
    · exact N059.original hk kn
    · exact N060.original hk kn
    · exact N061.original hk kn
    · exact N062.original hk kn
    · exact N063.original hk kn
    · exact N064.original hk kn

#print axioms original_through64

end LongCycleBounds.DescentNecklace.EulerianBrackets
