import LongCycleBounds.DescentBoundaryOrderedSigns
import LongCycleBounds.DescentBoundaryExceptions

/-! The all-cutoff mixture statement at sizes one to five. -/
noncomputable section
namespace LongCycleBounds.DescentBoundary
open Finset Polynomial DescentNecklace LongCycleFinite

theorem one_all_weights (w : ℕ → ℝ) :
    (mixture 1 w).Splits ∧ (mixture 1 w).roots.Nodup ∧ ∀ x ∈ (mixture 1 w).roots, x ≤ 0 := by
  have row1 : realRow 1 1 = 1 := by
    rw [realRow, ← ofCoeffs_descentRowDP (by decide),
      show descentRowDP 1 1 = [1] by decide +kernel]
    simp [ofCoeffs]
  have h : mixture 1 w = C (w 1) := by simp [mixture, row1]
  simp [h, Splits.C]

theorem two_all_weights (w : ℕ → ℝ) (hw : ∀ k ∈ Icc 1 2, 0 ≤ w k)
    (pos : ∃ k ∈ Icc 1 2, 0 < w k) :
    (mixture 2 w).Splits ∧ (mixture 2 w).roots.Nodup ∧ ∀ x ∈ (mixture 2 w).roots, x ≤ 0 := by
  have row1 : realRow 2 1 = 1+X := by
    rw [realRow, ← ofCoeffs_descentRowDP (by decide),
      show descentRowDP 2 1 = [1,1] by decide +kernel]
    simp [ofCoeffs]
  have row2 : realRow 2 2 = X := by
    rw [realRow, ← ofCoeffs_descentRowDP (by decide),
      show descentRowDP 2 2 = [0,1] by decide +kernel]
    simp [ofCoeffs]
  have sumPos := sum_pos' hw pos
  have ix : Icc 1 2 = ({1,2}:Finset ℕ) := by decide
  have ab : 0 < w 1+w 2 := by simpa [ix] using sumPos
  have poly : mixture 2 w = C (w 1+w 2)*X + C (w 1) := by
    simp [mixture, ix, row1, row2]; ring
  let r := -(w 1/(w 1+w 2))
  have root : (mixture 2 w).eval r = 0 := by
    rw [poly]; simp [r]; field_simp; ring
  have hne : mixture 2 w ≠ 0 := by
    intro h
    have v := congrArg (fun f : ℝ[X] ↦ f.coeff 1) h
    rw [poly] at v
    simpa using ab.ne' (by simpa using v)
  apply simple_nonpositive_of_witnesses hne {r}
  · simpa using mixture_degree_cap (n := 2) (by decide) w
  · simpa using root
  · simpa [r] using neg_nonpos.mpr (div_nonneg (hw 1 (by decide)) ab.le)

theorem three_all_weights (w : ℕ → ℝ) (hw : ∀ k ∈ Icc 1 3, 0 ≤ w k)
    (pos : ∃ k ∈ Icc 1 3, 0 < w k) :
    (mixture 3 w).Splits ∧ (mixture 3 w).roots.Nodup ∧ ∀ x ∈ (mixture 3 w).roots, x ≤ 0 := by
  apply all_mixtures_of_ordered_signs (by decide) (fun _ ↦ -1) _ _ _ w hw pos
  · intro i j hij
    have hi := i.isLt
    have hj := j.isLt
    change i.val < j.val at hij
    omega
  · intro i; norm_num
  · intro k hk i
    have zero : i.val = 0 := by have h := i.isLt; omega
    obtain ⟨lo, hi⟩ := mem_Icc.mp hk
    rw [realRow, ← ofCoeffs_descentRowDP (by decide)]
    interval_cases k
    · rw [show descentRowDP 3 1 = [1,4,1] by decide +kernel]
      norm_num [zero, ofCoeffs]
    · rw [show descentRowDP 3 2 = [0,2,0] by decide +kernel]
      norm_num [zero, ofCoeffs]
    · rw [show descentRowDP 3 3 = [0,2,0] by decide +kernel]
      norm_num [zero, ofCoeffs]

#print axioms one_all_weights
#print axioms two_all_weights
#print axioms three_all_weights
end LongCycleBounds.DescentBoundary

