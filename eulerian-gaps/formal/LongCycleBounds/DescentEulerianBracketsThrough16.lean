import LongCycleBounds.DescentEulerianBracketData.N006
import LongCycleBounds.DescentEulerianBracketData.N007
import LongCycleBounds.DescentEulerianBracketData.N008
import LongCycleBounds.DescentEulerianBracketData.N009
import LongCycleBounds.DescentEulerianBracketData.N010
import LongCycleBounds.DescentEulerianBracketData.N011
import LongCycleBounds.DescentEulerianBracketData.N012
import LongCycleBounds.DescentEulerianBracketData.N013
import LongCycleBounds.DescentEulerianBracketData.N014
import LongCycleBounds.DescentEulerianBracketData.N015
import LongCycleBounds.DescentEulerianBracketData.N016

/-! Exact Eulerian bracketing of every ordinary-descent cutoff representative through 16. -/

namespace LongCycleBounds.DescentNecklace.EulerianBrackets

open LongCycleFinite LongCycles

theorem original_through16 {n k : ℕ} (lo : 6 ≤ n) (hi : n ≤ 16) (hk : 3 ≤ k) (kn : k ≤ n) :
    StrictNegativeInterlacing (originalQuotient n k) (eulerian (n - 1)) (n - 3) := by
  interval_cases n
  · exact N006.original hk kn
  · exact N007.original hk kn
  · exact N008.original hk kn
  · exact N009.original hk kn
  · exact N010.original hk kn
  · exact N011.original hk kn
  · exact N012.original hk kn
  · exact N013.original hk kn
  · exact N014.original hk kn
  · exact N015.original hk kn
  · exact N016.original hk kn

#print axioms original_through16

end LongCycleBounds.DescentNecklace.EulerianBrackets
