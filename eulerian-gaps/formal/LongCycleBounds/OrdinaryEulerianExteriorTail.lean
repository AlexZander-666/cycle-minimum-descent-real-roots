import LongCycleBounds.OrdinaryEulerianExteriorDecay
import LongCycleBounds.WeightedOuter

/-! Exterior cancellation after subtracting the color at a neighboring label. -/
noncomputable section
namespace LongCycleBounds.OrdinaryEulerianExterior
open Outer Real

/-- A three-Lipschitz color in positive-label order has an error below 888/2401
times the mode mass outside the central triple, after centering at either neighbor. -/
theorem centered_tail {p : ℕ} (hp : 64 ≤ p) {x : ℝ} (hx : 0 < x)
    (region : 5 * sqrt p / 2 ≤ x) (G : ℕ → ℝ) (s : ℕ)
    (lip : ∀ i j : ℕ, |G i - G j| ≤ 3 * |(i:ℝ) - j|)
    (nearby : |(mode p x hx:ℝ) - s| ≤ 1)
    (hs : Summable (fun i : ℕ ↦ (-1:ℝ)^i * weight p x i * (G i-G s))) :
    let m := mode p x hx
    let f (i : ℕ) := (-1:ℝ)^i * weight p x i * (G i-G s)
    |(∑' i, f i) - (f m + leftAt f m 1 + f (m+1))| ≤ 888/2401 * weight p x m := by
  let m := mode p x hx
  let W := weight p x m
  let r : ℝ := 1/50
  let f (i : ℕ) := (-1:ℝ)^i * weight p x i * (G i-G s)
  let u (j : ℕ) := ((j:ℝ)+3)*r^(j+1)*(3*W)
  have hw : 0 < W := weight_pos ..
  have a (j : ℕ) : |f j| = weight p x j * |G j-G s| := by
    simp [f,abs_mul,abs_of_nonneg (weight_pos p x j).le]
  have summ : HasSum u ((444/2401)*W) := by
    have hr : ‖r‖ < 1 := by norm_num [r,Real.norm_eq_abs]
    have A := (((hasSum_coe_mul_geometric_of_norm_lt_one hr).add
      ((hasSum_geometric_of_norm_lt_one hr).mul_left 3)).mul_right r).mul_right (3*W)
    have e (j : ℕ) : u j = ((j:ℝ)*r^j+3*r^j)*r*(3*W) := by
      dsimp [u]
      rw [pow_succ]
      ring
    have eu : u = (fun j : ℕ ↦ ((j:ℝ)*r^j+3*r^j)*r*(3*W)) := funext e
    rw [eu]
    have total : (444/2401)*W = (r/(1-r)^2+3*(1-r)⁻¹)*r*(3*W) := by
      norm_num [r]
      ring
    rw [total]
    exact A
  have point (i j : ℕ) (dist : |(i:ℝ)-m| ≤ (j:ℝ)+2)
      (far : weight p x i ≤ r^(j+1)*W) : |f i| ≤ u j := by
    have d := abs_sub_le (i:ℝ) m s
    have size : |G i-G s| ≤ 3*((j:ℝ)+3) := (lip i s).trans (by
      change |(m:ℝ)-s| ≤ 1 at nearby
      linarith)
    rw [a]
    exact (mul_le_mul far size (abs_nonneg _) (by positivity)).trans_eq (by dsimp [u];ring)
  have L (j : ℕ) : |leftAt f m (j+2)| ≤ u j := by
    by_cases valid : j+2 ≤ m
    · rw [leftAt,if_pos valid]
      have far := (both_geometric p hp x hx region (j+1)).1
      change leftAt (weight p x) m (j+2) ≤ _ at far
      rw [leftAt,if_pos valid] at far
      apply point _ j _ far
      rw [Nat.cast_sub valid]
      push_cast
      rw [show (m:ℝ)-((j:ℝ)+2)-m = -((j:ℝ)+2) by ring, abs_neg, abs_of_nonneg (by positivity)]
    · rw [leftAt,if_neg valid,abs_zero]
      dsimp [u,r]
      positivity
  have R (j : ℕ) : |f (m+(j+2))| ≤ u j := by
    apply point (m+(j+2)) j _ (both_geometric p hp x hx region (j+1)).2
    push_cast
    rw [show (m:ℝ)+((j:ℝ)+2)-m=(j:ℝ)+2 by ring,abs_of_nonneg (by positivity)]
  exact (three_point_error f m hs summ L R).trans_eq (by ring)

#print axioms centered_tail
end LongCycleBounds.OrdinaryEulerianExterior
