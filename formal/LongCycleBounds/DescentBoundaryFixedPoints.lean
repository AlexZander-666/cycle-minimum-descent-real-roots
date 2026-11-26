import LongCycleBounds.DescentBoundaryUnrestricted
import LongCycleBounds.DescentCappedCutoffs
import Mathlib.RingTheory.PowerSeries.WellKnown

noncomputable section
namespace LongCycleBounds.DescentNecklace
open Finset Polynomial DescentTwoLetters
/-- At cutoff one every word is available, including the empty word. -/
theorem count_unrestricted (n q : ℕ) : positiveCountDP n q 1 = q^n := by
  cases n with
  | zero => rfl
  | succ n =>
    have eq := letters_eq_necklace_content (Nat.succ_pos n) q 1
    rw [letters_eq_positiveCountDP (Nat.succ_pos n),unrestricted_necklaces] at eq
    exact_mod_cast eq

theorem fixed_point_convolution (n q : ℕ) :
    q^n = ∑ a ∈ range (n+1), positiveCountDP (n-a) q 2 * q.multichoose a := by
  cases n with
  | zero => simp [positiveCountDP,positiveFactors,countTable,initialTable]
  | succ t =>
    let n := t+1
    let p : ℕ[X] := ∑ d ∈ range (n+1), monomial d (positiveCountDP d q 2)
    have coeff (d : ℕ) (fit : d ≤ n) : p.coeff d = positiveCountDP d q 2 := by
      simp [p,finsetSum_coeff,coeff_monomial,mem_range.mpr (Nat.lt_succ_of_le fit)]
    have c := cappedCutoffState_count (n:=n) (bound:=n) le_rfl q 1
    have one : primitiveCount 1 q = q := by simp [primitiveCount]
    rw [cappedCutoffState_step (by decide) (by dsimp [n]; omega),one,count_unrestricted] at c
    have val := convolveTable_correct (bound:=n) (w:=1) (by decide) q
      (cappedCutoffState n q 2) p (fun d hd ↦ (cappedCutoffState_count hd q 2).trans (coeff d hd).symm)
      (d:=n) le_rfl
    rw [← c,val,coeff_mul_lengthFactor p (by decide) q le_rfl,Nat.div_one]
    apply sum_congr rfl
    intro a _
    rw [Nat.one_mul,coeff _ (Nat.sub_le ..),multiplicityWeight_eq_choose,Nat.multichoose_eq]

#print axioms fixed_point_convolution
end LongCycleBounds.DescentNecklace
