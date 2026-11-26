import LongCycleBounds.DescentEulerianBracketsThrough64
import LongCycleBounds.DescentEulerianBracketData.N065
import LongCycleBounds.DescentEulerianBracketData.N066
import LongCycleBounds.DescentEulerianBracketData.N067
import LongCycleBounds.DescentEulerianBracketData.N068
import LongCycleBounds.DescentEulerianBracketData.N069
import LongCycleBounds.DescentEulerianBracketData.N070
import LongCycleBounds.DescentEulerianBracketData.N071
import LongCycleBounds.DescentEulerianBracketData.N072
import LongCycleBounds.DescentEulerianBracketData.N073
import LongCycleBounds.DescentEulerianBracketData.N074
import LongCycleBounds.DescentEulerianBracketData.N075
import LongCycleBounds.DescentEulerianBracketData.N076
import LongCycleBounds.DescentEulerianBracketData.N077
import LongCycleBounds.DescentEulerianBracketData.N078
import LongCycleBounds.DescentEulerianBracketData.N079
import LongCycleBounds.DescentEulerianBracketData.N080
import LongCycleBounds.DescentEulerianBracketData.N081
import LongCycleBounds.DescentEulerianBracketData.N082
import LongCycleBounds.DescentEulerianBracketData.N083
import LongCycleBounds.DescentEulerianBracketData.N084
import LongCycleBounds.DescentEulerianBracketData.N085
import LongCycleBounds.DescentEulerianBracketData.N086
import LongCycleBounds.DescentEulerianBracketData.N087
import LongCycleBounds.DescentEulerianBracketData.N088

/-! Exact Eulerian bracketing of the original ordinary-descent quotients through upper size 88. -/

namespace LongCycleBounds.DescentNecklace.EulerianBrackets

open LongCycleFinite LongCycles

set_option maxHeartbeats 1000000 in
theorem original_through88 {n k : ℕ} (lo : 6 ≤ n) (hi : n ≤ 88)
    (hk : 3 ≤ k) (kn : k ≤ n) :
    StrictNegativeInterlacing (originalQuotient n k) (eulerian (n - 1)) (n - 3) := by
  by_cases small : n ≤ 64
  · exact original_through64 lo small hk kn
  · interval_cases n
    · exact N065.original hk kn
    · exact N066.original hk kn
    · exact N067.original hk kn
    · exact N068.original hk kn
    · exact N069.original hk kn
    · exact N070.original hk kn
    · exact N071.original hk kn
    · exact N072.original hk kn
    · exact N073.original hk kn
    · exact N074.original hk kn
    · exact N075.original hk kn
    · exact N076.original hk kn
    · exact N077.original hk kn
    · exact N078.original hk kn
    · exact N079.original hk kn
    · exact N080.original hk kn
    · exact N081.original hk kn
    · exact N082.original hk kn
    · exact N083.original hk kn
    · exact N084.original hk kn
    · exact N085.original hk kn
    · exact N086.original hk kn
    · exact N087.original hk kn
    · exact N088.original hk kn

#print axioms original_through88

end LongCycleBounds.DescentNecklace.EulerianBrackets
