import LongCycleBounds.DescentActualCentral
import LongCycleBounds.Reciprocity

/-! Reciprocal evaluation at the true ambient degree n−1. -/
noncomputable section
namespace LongCycleBounds.DescentMesh
open Polynomial Finset LongCycles Real DescentTwoLetters FixedCycleCount

def reflectedCoefficients (n : ℕ) (a : ℕ → ℝ) (h : ℕ) := (-1:ℝ)^(n-h)*a h

theorem transform_reflect (n : ℕ) (a : ℕ → ℝ) {t : ℝ} (ht : t ≠ 0) :
    t^(n-1)*(descentTransform n a).eval t⁻¹ =
      (descentTransform n (reflectedCoefficients n a)).eval t := by
  simp only [descentTransform,eval_finsetSum,eval_mul,eval_sub,eval_one,eval_X,eval_C,eval_pow,
    mul_sum,reflectedCoefficients]
  apply sum_congr rfl
  intro h hh
  have bounds := mem_Icc.mp hh
  have eu := eulerian_reciprocity (h-1) ht
  rw [show h-1+1=h by omega] at eu
  have split : t^(n-1)=t^(n-h)*t^(h-1) := by rw [← pow_add]; congr 1; omega
  have base : t*(1-t⁻¹) = (-1)*(1-t) := by field_simp; ring
  have pw := congrArg (fun x : ℝ ↦ x^(n-h)) base
  simp only [mul_pow] at pw
  rw [split]
  calc
    _ = a h*(t^(n-h)*(1-t⁻¹)^(n-h))*(t^(h-1)*(eulerian h).eval t⁻¹) := by ring
    _ = _ := by rw [pw,eu]; ring

theorem reflected_lossNorm (n : ℕ) (a : ℕ → ℝ) (v : ℝ) :
    lossNorm n (reflectedCoefficients n a) v = lossNorm n a v := by
  simp [lossNorm,reflectedCoefficients,abs_mul]

theorem central_sign_actual_reciprocal {n k i : ℕ} (hk : 3≤k) (hn : k≤n) (h128 : 128≤n)
    {θ : ℝ} (lo : π/(2*sqrt ((n:ℝ)+1)) ≤ θ) (top : θ ≤ π/2)
    (phase : ((n:ℝ)+1)*θ=(i:ℝ)*π) :
    let t := -exp (-(π*cos θ/sin θ))
    (-1:ℝ)^i * (t^(n-1)*((row n k).map (Int.castRingHom ℝ)).eval t⁻¹) < 0 := by
  dsimp only
  rw [actual_expanded_readout hk (by omega),transform_reflect _ _ (neg_ne_zero.mpr (exp_ne_zero _))]
  apply central_sign_of_global h128 lo top phase
  · simp only [reflectedCoefficients,Nat.sub_self,pow_zero,one_mul,expanded_top hk (by omega : 0<n) n n n]
    exact lt_of_lt_of_le (by positivity) (Occupancy.allowedFraction_ge_half (by omega : 2≤k) hn)
  · rw [reflected_lossNorm]
    simp only [reflectedCoefficients,Nat.sub_self,pow_zero,one_mul,expanded_top hk (by omega : 0<n) n n n]
    exact (expanded_small hk hn h128 n n n (by norm_num) (by norm_num) envelope_table.2.2.1).le
  · rw [reflected_lossNorm]
    simp only [reflectedCoefficients,Nat.sub_self,pow_zero,one_mul,expanded_top hk (by omega : 0<n) n n n]
    exact expanded_global hk hn n n n

#print axioms transform_reflect
#print axioms central_sign_actual_reciprocal
end LongCycleBounds.DescentMesh
