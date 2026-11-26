import LongCycleBounds.DescentPackedData.C048Q001
import LongCycleBounds.DescentPackedData.C048Q002
import LongCycleBounds.DescentPackedData.C048Q003
import LongCycleBounds.DescentPackedData.C048Q004
import LongCycleBounds.DescentPackedData.C048Q005
import LongCycleBounds.DescentPackedData.C048Q006

/-! The first 6 checked alphabets, all computed at degree cap 48. -/

namespace LongCycleBounds.DescentNecklace.Packed.C048L006

def rawCode : ℕ → ℕ → ℕ
  | 0 => C048Q001.code
  | 1 => C048Q002.code
  | 2 => C048Q003.code
  | 3 => C048Q004.code
  | 4 => C048Q005.code
  | 5 => C048Q006.code
  | _ => fun _ ↦ 0

def codes (i : Fin 6) : ℕ → ℕ := rawCode i.val

set_option maxHeartbeats 6000000 in
theorem checked (i : Fin 6) : PackedCutoffChecks 48 (i.val + 1) 3 (codes i) := by
  obtain ⟨i, fits⟩ := i
  interval_cases i
  · exact C048Q001.checked
  · exact C048Q002.checked
  · exact C048Q003.checked
  · exact C048Q004.checked
  · exact C048Q005.checked
  · exact C048Q006.checked

#print axioms checked

end LongCycleBounds.DescentNecklace.Packed.C048L006
