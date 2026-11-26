import Mathlib

/-! Effective finite tail control for a nonnegative differentiated-convolution recurrence. -/
namespace FiniteConvolutionTail
open Finset
noncomputable section

/-- Future coefficient budget left by the terms of indices strictly below n. -/
def potential (e S : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ range n, e j * S (n-j)

theorem potential_nonneg {e S : ℕ → ℝ} (ep : ∀ j, 0 ≤ e j) (sp : ∀ i, 1 ≤ i → 0 ≤ S i)
    (n : ℕ) : 0 ≤ potential e S n := by
  apply sum_nonneg
  intro j hj
  have le := mem_range.mp hj
  exact mul_nonneg (ep j) (sp _ (by omega))

/-- Moving a prefix boundary forward pays the actual next variation, priced at n−S₁.
No convergence of an infinite series is assumed. -/
theorem step {e t S : ℕ → ℝ} (ep : ∀ j, 0 ≤ e j)
    (tail : ∀ i, 1 ≤ i → t i+S (i+1) ≤ S i) (n : ℕ)
    (rec : n*e n  ≤  ∑ j ∈ range n, e j*t (n-j)) :
    ((n:ℝ)-S 1)*e n+potential e S (n+1)  ≤  potential e S n := by
  have part (j : ℕ) (hj : j ∈ range n) :
      e j*t (n-j)+e j*S (n+1-j)  ≤  e j*S (n-j) := by
    have lt := mem_range.mp hj
    rw [show n+1-j=n-j+1 by omega, ←mul_add]
    exact mul_le_mul_of_nonneg_left (tail _ (by omega)) (ep j)
  have h := sum_le_sum part
  rw [sum_add_distrib] at h
  simp only [potential,sum_range_succ,show n+1-n=1 by omega]
  linarith only [rec,h]

/-- The weighted tail can be stopped at any subsequent rank, including the initial one. -/
theorem stopped {e t S : ℕ → ℝ} (ep : ∀ j, 0 ≤ e j)
    (tail : ∀ i, 1 ≤ i → t i+S (i+1) ≤ S i) (B : ℕ)
    (rec : ∀ n, B ≤ n → n*e n  ≤  ∑ j ∈ range n, e j*t (n-j))
    (M : ℕ) (bound : B ≤ M) :
    ((B:ℝ)-S 1)*(∑ i ∈ Ico B M,e i)+potential e S M  ≤  potential e S B := by
  induction M, bound using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    have st := step ep tail m (rec m hm)
    have bm : (B:ℝ) ≤ m := by exact_mod_cast hm
    rw [sum_Ico_succ_top hm]
    nlinarith only [ih,st,mul_nonneg (sub_nonneg.mpr bm) (ep m)]

/-- A strict margin at B−1, after debiting the full potential, propagates at every rank.
The variation e n is only required to bound the downward movement at its own step. -/
theorem margin_persists {e t S Δ : ℕ → ℝ} (ep : ∀ j, 0 ≤ e j)
    (sp : ∀ i, 1 ≤ i → 0 ≤ S i) (tail : ∀ i, 1 ≤ i → t i+S (i+1) ≤ S i)
    (B : ℕ) (Bp : 1 ≤ B) (gap : S 1 < B)
    (rec : ∀ n,B ≤ n → n*e n  ≤  ∑ j ∈ range n,e j*t (n-j))
    (fall : ∀ n,B ≤ n → Δ (n-1)-Δ n  ≤  e n)
    (init : potential e S B < ((B:ℝ)-S 1)*Δ (B-1)) :
    ∀ n, B-1 ≤ n → 0 < Δ n := by
  have inv (n : ℕ) (hn : B-1 ≤ n) :
      potential e S (n+1) < ((B:ℝ)-S 1)*Δ n := by
    induction n,hn using Nat.le_induction with
    | base => simpa only [show B-1+1=B by omega] using init
    | succ n hn ih =>
      have nb : B ≤ n+1 := by omega
      have nr : (B:ℝ) ≤ (n+1:ℕ) := by exact_mod_cast nb
      have step' := step ep tail (n+1) (rec _ nb)
      have one := fall (n+1) nb
      rw [Nat.add_sub_cancel] at one
      have compare := mul_le_mul_of_nonneg_right (sub_le_sub_right nr (S 1)) (ep (n+1))
      nlinarith only [ih,step',compare,mul_le_mul_of_nonneg_left one (sub_nonneg.mpr gap.le)]
  intro n hn
  exact pos_of_mul_pos_right ((potential_nonneg ep sp (n+1)).trans_lt (inv n hn)) (sub_nonneg.mpr gap.le)

#print axioms step
#print axioms stopped
#print axioms margin_persists
end
end FiniteConvolutionTail
