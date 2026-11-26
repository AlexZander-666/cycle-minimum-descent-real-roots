import LongCycleBounds.MultinomialWindow
import Mathlib.Tactic

namespace LongCycleBounds.FixedCycleCount

private theorem binomial_tangent (m : ℕ) {x y : ℝ} (hx : 0≤x) (hy : 0≤y) :
    x^(m+1)+(m+1:ℕ)*x^m*y ≤ (x+y)^(m+1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have times := mul_le_mul_of_nonneg_right ih (add_nonneg hx hy)
    rw [pow_succ (x+y) (m+1)]
    rw [pow_succ x (m+1)]
    rw [pow_succ x m] at times ⊢
    push_cast at *
    nlinarith only [times, mul_nonneg (show 0≤(m+1:ℝ)*x^m by positivity) (sq_nonneg y)]

/-- The marked-factor bound y^h/(y-h+1) is increasing beyond h, uniformly in h. -/
theorem support_ratio_le (m : ℕ) {x C : ℝ} (hx : (m:ℝ)+1≤x) (hc : x≤C) :
    x^(m+1)*(C-m) ≤ C^(m+1)*(x-m) := by
  have xx : 0≤x := by linarith [Nat.cast_nonneg (α:=ℝ) m]
  have y : 0≤C-x := sub_nonneg.mpr hc
  have diff := binomial_tangent m xx y
  rw [show x+(C-x)=C by ring] at diff
  have b := mul_le_mul_of_nonneg_right diff (show 0≤x-m by linarith)
  have extra : 0≤(m:ℝ)*(x-m-1) := mul_nonneg (Nat.cast_nonneg _) (by linarith)
  have e := mul_nonneg (mul_nonneg (pow_nonneg xx m) y) extra
  push_cast at b
  rw [pow_succ x m] at b ⊢
  nlinarith only [b,e]

#print axioms support_ratio_le
end LongCycleBounds.FixedCycleCount
