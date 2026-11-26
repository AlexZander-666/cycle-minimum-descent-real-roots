import LongCycleBounds.DescentBoundaryManuscript
import LongCycleBounds.DescentLowerPackedData.Through127

noncomputable section
namespace LongCycleBounds.DescentBoundary
open Finset Polynomial DescentNecklace DescentDerangement

/-- All zeros and both exceptional supports, for the sum on the original permutations. -/
theorem all_cutoffs_all_sizes {n : ℕ} (hn : 1 ≤ n) (w : ℕ → ℝ)
    (hw : ∀ k ∈ Icc 1 n, 0 ≤ w k) (pos : ∃ k ∈ Icc 1 n, 0 < w k) :
    (mixture n w ≠ 0) ∧ (mixture n w).Splits ∧ (∀ x ∈ (mixture n w).roots, x ≤ 0) ∧
      ((mixture n w).roots.Nodup ↔ ¬ExceptionalSupport n w) :=
  all_cutoffs_from_finite (fun _ lo hi ↦ LowerPacked.lower_cutoff_mesh_through127 lo hi)
    hn w hw pos

/-- The two supports in ordinary language, using the original nonnegative weights. -/
theorem exceptional_support_iff {n : ℕ} (w : ℕ → ℝ) (hw : ∀ k ∈ Icc 1 n, 0 ≤ w k) :
    ExceptionalSupport n w ↔
      (n = 4 ∧ w 1 = 0 ∧ w 3 = 0 ∧ w 4 = 0) ∨ (n = 5 ∧ w 1 = 0 ∧ w 2 = 0) := by
  constructor
  · rintro (⟨rfl,e⟩ | ⟨rfl,e⟩)
    · have a := hw 1 (by decide)
      have b := hw 3 (by decide)
      have c := hw 4 (by decide)
      exact Or.inl ⟨rfl,by linarith,by linarith,by linarith⟩
    · have a := hw 1 (by decide)
      have b := hw 2 (by decide)
      exact Or.inr ⟨rfl,by linarith,by linarith⟩
  · rintro (⟨rfl,a,b,c⟩|⟨rfl,a,b⟩)
    · exact Or.inl ⟨rfl,by simp [a,b,c]⟩
    · exact Or.inr ⟨rfl,by simp [a,b]⟩

theorem all_cutoffs_manuscript {n : ℕ} (hn : 1 ≤ n) (w : ℕ → ℝ)
    (hw : ∀ k ∈ Icc 1 n, 0 ≤ w k) (hsum : 0 < ∑ k ∈ Icc 1 n, w k) :
    (mixture n w ≠ 0) ∧ (mixture n w).Splits ∧ (∀ x ∈ (mixture n w).roots, x ≤ 0) ∧
      ((mixture n w).roots.Nodup ↔ ¬((n=4 ∧ w 1=0 ∧ w 3=0 ∧ w 4=0) ∨
        (n=5 ∧ w 1=0 ∧ w 2=0))) := by
  have positive : ∃ k ∈ Icc 1 n, 0 < w k := by
    by_contra! none
    have zero := sum_eq_zero (fun k hk ↦ le_antisymm (none k hk) (hw k hk))
    linarith only [hsum,zero]
  simpa only [← exceptional_support_iff w hw] using all_cutoffs_all_sizes hn w hw positive

theorem original_descent_splits {n k : ℕ} (lo : 1 ≤ k) (hi : k ≤ n) : (realRow n k).Splits := by
  let w (j : ℕ) : ℝ := if j=k then 1 else 0
  have hw (j : ℕ) (_ : j ∈ Icc 1 n) : 0 ≤ w j := by dsimp [w]; split <;> norm_num
  have pos : ∃ j ∈ Icc 1 n, 0 < w j := ⟨k,mem_Icc.mpr ⟨lo,hi⟩,by simp [w]⟩
  have e : mixture n w = realRow n k := by
    unfold mixture
    rw [sum_eq_single_of_mem k (mem_Icc.mpr ⟨lo,hi⟩)]
    · simp [w]
    · intro j _ neq
      simp [w,neq]
  exact e ▸ (all_cutoffs_all_sizes (lo.trans hi) w hw pos).2.1

#print axioms all_cutoffs_manuscript
#print axioms original_descent_splits
#print axioms all_cutoffs_all_sizes
#print axioms exceptional_support_iff
#print axioms four_exception
#print axioms five_exception
end LongCycleBounds.DescentBoundary
