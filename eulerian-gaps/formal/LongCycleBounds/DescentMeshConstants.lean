import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-! Explicit rational budgets for the admissible-necklace logarithm. -/
noncomputable section
namespace LongCycleBounds.DescentMesh
open Real

/-- Absolute logarithmic envelope with exponents 3 through 7 separated. -/
def badEnvelope (v : ℝ) : ℝ :=
  v^2/3 + v^2/4 + v^4/5 + (v^3+v^4+v^5)/6 + v^6/7 +
    v^4/(1-v) + v^3/(2*(1-v)*(1-v^3))

private def powerTail (n : ℕ) : ℝ := 16 * (n:ℝ)^2 * (3/4:ℝ)^(n/2)

private theorem tail_step (n : ℕ) (hn : 128 ≤ n) : powerTail (n+2) ≤ powerTail n := by
  have nr : (128:ℝ) ≤ n := by exact_mod_cast hn
  rw [powerTail, powerTail, show (n+2)/2=n/2+1 by omega, pow_succ]
  push_cast
  have h : 16*((n:ℝ)+2)^2 * (3/4) ≤ 16*(n:ℝ)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr nr) (show 0 ≤ (n:ℝ)+1 by positivity)]
  calc
    _ = (16*((n:ℝ)+2)^2*(3/4)) * (3/4:ℝ)^(n/2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right h (by positivity)

/-- Integer-exponent version slightly rounds up the Cauchy error in odd degrees. -/
theorem power_tail_small (n : ℕ) (hn : 128 ≤ n) :
    16*(n:ℝ)^2*(3/4:ℝ)^(n/2) < 1/100 := by
  change powerTail n < 1/100
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases a : n=128
    · subst n; norm_num [powerTail]
    by_cases b : n=129
    · subst n; norm_num [powerTail]
    have h := ih (n-2) (by omega) (by omega)
    have step : powerTail n ≤ powerTail (n-2) := by
      simpa [show n-2+2=n by omega] using tail_step (n-2) (by omega)
    exact step.trans_lt h

theorem empty_tail_small (n : ℕ) (hn : 128 ≤ n) :
    16*(n:ℝ)*(3/4:ℝ)^(n/2) < 1/1000 := by
  have nr : (128:ℝ) ≤ n := by exact_mod_cast hn
  have h := power_tail_small n hn
  by_contra! bad
  have m := mul_le_mul_of_nonneg_left bad (show 0 ≤ (n:ℝ) by positivity)
  nlinarith

private theorem exp_K_le {x : ℝ} (hx : x < 1) : exp x-1 ≤ x/(1-x) := by
  have hh : 1-x ≤ exp (-x) := by linarith only [add_one_le_exp (-x)]
  have mul := mul_le_mul_of_nonneg_left hh (exp_nonneg x)
  rw [exp_neg, mul_inv_cancel₀ (exp_ne_zero x)] at mul
  apply (le_div_iff₀ (by linarith)).mpr
  linarith

/-- The radius 2/3 used to reweight the empty-residual or low-order terms. -/
theorem envelope_comparison : exp (badEnvelope (2/3)) < 8 := by
  have h : badEnvelope (2/3) < 2 := by norm_num [badEnvelope]
  apply (exp_lt_exp.mpr h).trans
  rw [show (2:ℝ)=(2:ℕ)*1 by norm_num, exp_nat_mul]
  nlinarith [exp_one_lt_d9, exp_pos 1, sq_nonneg (2.7182818286 - exp 1),
    mul_pos (sub_pos.mpr exp_one_lt_d9) (show 0 < 2.7182818286 + exp 1 by positivity)]

/-- All four pointwise finite rational margins, including the worst end-grid alphabet. -/
theorem envelope_table :
    2*(exp (badEnvelope (1/4))-1)+1/1000 < 1/7 ∧
    2*(exp (badEnvelope (1/3))-1)+1/1000 < 1/3 ∧
    2*(exp (badEnvelope (3/8))-1)+1/1000 < 3/7 ∧
    2*(exp (badEnvelope (1/2))-1)+1/1000 < 2 := by
  have cert {v e : ℝ} (small : badEnvelope v < 1)
      (budget : 2*(badEnvelope v/(1-badEnvelope v))+1/1000<e) :
      2*(exp (badEnvelope v)-1)+1/1000<e := by linarith only [exp_K_le small,budget]
  refine ⟨cert ?_ ?_,cert ?_ ?_,cert ?_ ?_,cert ?_ ?_⟩ <;> norm_num [badEnvelope]

#print axioms power_tail_small
#print axioms empty_tail_small
#print axioms envelope_table
end LongCycleBounds.DescentMesh
