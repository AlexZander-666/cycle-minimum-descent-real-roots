import LongCycleBounds.DescentBoundarySmallRoots

/-! A shared alternation test on the original rows implies the all-cutoff mixture theorem. -/
noncomputable section
namespace LongCycleBounds.DescentBoundary
open Finset Polynomial DescentTwoLetters DescentNecklace LongCycleFinite

theorem mixture_degree_cap {n : ℕ} (hn : 0 < n) (w : ℕ → ℝ) :
    (mixture n w).natDegree ≤ n-1 := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  rw [mixture, finsetSum_coeff]
  apply sum_eq_zero
  intro k _
  have cap : (realRow n k).natDegree ≤ n-1 := by
    rw [realRow, ← ofCoeffs_descentRowDP hn]
    simpa [descentRowDP] using ofCoeffs_degree_le (descentRowDP n k)
  rw [coeff_C_mul, natDegree_le_iff_coeff_eq_zero.mp cap j hj, mul_zero]

/-- Nodes run from the most negative to the least negative. The rightmost sign is negative. -/
def OrderedRowSigns {d : ℕ} (a : Fin d → ℝ) (p : ℝ[X]) : Prop :=
  ∀ i, if (d-1-i.val)%2=0 then p.eval (a i) < 0 else 0 < p.eval (a i)

theorem mixture_ordered_signs {n d : ℕ} (a : Fin d → ℝ)
    (rows : ∀ k ∈ Icc 1 n, OrderedRowSigns a (realRow n k))
    (w : ℕ → ℝ) (hw : ∀ k ∈ Icc 1 n, 0 ≤ w k) (pos : ∃ k ∈ Icc 1 n, 0 < w k) :
    OrderedRowSigns a (mixture n w) := by
  obtain ⟨j, hj, hpos⟩ := pos
  intro i
  have ev : (mixture n w).eval (a i) = ∑ k ∈ Icc 1 n, w k * (realRow n k).eval (a i) := by
    simp [mixture, eval_finsetSum]
  rw [ev]
  split <;> rename_i parity
  · have neg k hk := (if_pos parity).mp (rows k hk i)
    exact sum_neg' (fun k hk ↦ mul_nonpos_of_nonneg_of_nonpos (hw k hk) (neg k hk).le)
      ⟨j, hj, mul_neg_of_pos_of_neg hpos (neg j hj)⟩
  · have p k hk := (if_neg parity).mp (rows k hk i)
    exact sum_pos' (fun k hk ↦ mul_nonneg (hw k hk) (p k hk).le)
      ⟨j, hj, mul_pos hpos (p j hj)⟩

theorem all_mixtures_of_ordered_signs {n : ℕ} (hn : 3 ≤ n) (a : Fin (n-2) → ℝ)
    (mono : StrictMono a) (negative : ∀ i, a i < 0)
    (rows : ∀ k ∈ Icc 1 n, OrderedRowSigns a (realRow n k))
    (w : ℕ → ℝ) (hw : ∀ k ∈ Icc 1 n, 0 ≤ w k) (pos : ∃ k ∈ Icc 1 n, 0 < w k) :
    (mixture n w).Splits ∧ (mixture n w).roots.Nodup ∧ ∀ x ∈ (mixture n w).roots, x ≤ 0 := by
  let p := mixture n w
  let d := n-2
  have hd : 0 < d := by dsimp [d]; omega
  let b (i : Fin d) := if next : i.val+1 < d then a ⟨i.val+1, next⟩ else 0
  let first : Fin d := ⟨0, hd⟩
  have sign : OrderedRowSigns a p := mixture_ordered_signs a rows w hw pos
  have origin : 0 ≤ p.eval 0 := by
    rw [← coeff_zero_eq_eval_zero]; exact mixture_coeff_nonneg n w hw 0
  apply simple_nonpositive_from_leading_window (p := p) a b (first := first)
  · intro i
    dsimp only [b]; split
    · exact mono (by change i.val < i.val+1; omega)
    · exact negative i
  · intro i
    dsimp only [b]; split
    · exact (negative _).le
    · exact le_rfl
  · intro i j hij
    have ij : i.val < j.val := hij
    have hj := j.isLt
    simp only [b, dif_pos (by omega : i.val+1 < d)]
    exact mono.monotone (show (⟨i.val+1, by omega⟩ : Fin d) ≤ j from ij)
  · intro i
    have h := sign i
    split at h
    · exact h.ne
    · exact h.ne'
  · intro i
    dsimp only [b]; split
    · rename_i next
      let j : Fin d := ⟨i.val+1,next⟩
      have h := sign i
      have l := sign j
      change (if (d-1-i.val)%2=0 then _ else _) at h
      change (if (d-1-(i.val+1))%2=0 then _ else _) at l
      by_cases even : (d-1-i.val)%2=0
      · rw [if_pos even] at h
        rw [if_neg (by omega : ¬(d-1-(i.val+1))%2=0)] at l
        exact (mul_neg_of_neg_of_pos h l).le
      · rw [if_neg even] at h
        rw [if_pos (by omega : (d-1-(i.val+1))%2=0)] at l
        exact (mul_neg_of_pos_of_neg h l).le
    · rename_i last
      have endSign := sign i
      have hi := i.isLt
      rw [if_pos (by dsimp [d] at *; omega : (n-2-1-i.val)%2=0)] at endSign
      exact mul_nonpos_of_nonpos_of_nonneg endSign.le origin
  · intro i; exact mono.monotone (show first ≤ i from Nat.zero_le _)
  · change (-1:ℝ)^(d+1)*p.eval (a first) < 0
    have h := sign first
    change (if (d-1-0)%2=0 then _ else _) at h
    by_cases even : Even (d+1)
    · have eq := Nat.even_iff.mp even
      rw [if_pos (by omega : (d-1-0)%2=0)] at h
      simpa only [even.neg_one_pow, one_mul] using h
    · have odd := Nat.not_even_iff_odd.mp even
      have eq := Nat.odd_iff.mp odd
      rw [if_neg (by omega : ¬(d-1-0)%2=0)] at h
      simpa only [odd.neg_one_pow, neg_one_mul, neg_lt_zero] using h
  · exact (mixture_degree_cap (by omega) w).trans_eq (by omega)
  · exact mixture_coeff_nonneg _ w hw _

#print axioms mixture_degree_cap
#print axioms all_mixtures_of_ordered_signs
end LongCycleBounds.DescentBoundary

