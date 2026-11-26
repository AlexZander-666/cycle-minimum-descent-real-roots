import LongCycleBounds.DescentMeshFactorial
import LongCycleBounds.DescentMeshGeometry
import LongCycleBounds.FixedFour49PoleMass

/-! Two order-sensitive estimates for the actual Eulerian moments in the descent specialization. -/
namespace LongCycleBounds.DescentMesh
noncomputable section
open Real Band PoleBridge

/-- The positive-half pole normalization of the actual order-q Eulerian moment. -/
theorem scaled_moment_mass {q : ℕ} (hq : 2 ≤ q) {x : ℝ} (hx : 0 ≤ x) :
    2*|scaledMoment (radius x) (-exp (-x)) q| ≤ 2+1/((q:ℝ)*(s x)^2) := by
  have sm := summable_norm_signed_odd_pole x hq
  have h := (norm_tsum_le_tsum_norm sm).trans (FixedFour49.ordered_pole_mass x hq)
  rw [signed_odd_pole_tsum x hx hq, norm_mul, Complex.norm_real, Complex.norm_ofNat,
    Real.norm_eq_abs] at h
  exact h

/-- Upper- and lower-order raw pole budgets under the actual grid region inequality. -/
theorem two_tier_eulerian_mass {n h : ℕ} (hn : 2 ≤ n) (hh : 1 ≤ h) {x : ℝ} (hx : 0 ≤ x)
    (region : 2 ≤ ((n:ℝ)+1)*(s x)^2) :
    let U := scaledMoment (radius x) (-exp (-x)) (h+1)
    |U| ≤ (n:ℝ) ∧ (n ≤ 2*h → |U| ≤ 3/2) := by
  have m := scaled_moment_mass (q:=h+1) (by omega) hx
  have s0 : 0 < s x := div_pos pi_pos (radius_pos x)
  have denom : 0 < ((h+1:ℕ):ℝ)*(s x)^2 := by positivity
  have hR : (1:ℝ) ≤ h := by exact_mod_cast hh
  have nR : (2:ℝ) ≤ n := by exact_mod_cast hn
  constructor
  · have cmp : 1/(((h+1:ℕ):ℝ)*(s x)^2) ≤ ((n:ℝ)+1)/4 := by
      apply (div_le_iff₀ denom).mpr
      push_cast
      nlinarith only [region, mul_nonneg (sub_nonneg.mpr hR)
        (mul_nonneg (show 0 ≤ (n:ℝ)+1 by positivity) (sq_nonneg (s x)))]
    linarith
  · intro half
    have hr : (n:ℝ) ≤ 2*(h:ℝ) := by exact_mod_cast half
    have low : 1 ≤ ((h+1:ℕ):ℝ)*(s x)^2 := by
      push_cast
      nlinarith only [region, mul_nonneg (sub_nonneg.mpr hr) (sq_nonneg (s x)),
        sq_nonneg (s x)]
    have := one_div_le_one_div_of_le zero_lt_one low
    linarith

/-- Relative contribution of a true Eulerian moment against the two evaluation radii
used in the coefficient-loss estimate. -/
theorem normalized_eulerian_weights {n h : ℕ} (hn : 2 ≤ n) (hh : 1 ≤ h) (lo : h ≤ n)
    {x : ℝ} (hx : 0 ≤ x) (region : 2 ≤ ((n:ℝ)+1)*(s x)^2)
    (radii : 2*radius x/n ≤ 3/8 ∧ exp 1*radius x/n ≤ 1/2) :
    let term := ((h.factorial:ℝ)/n.factorial)*(radius x)^(n-h) *
      |scaledMoment (radius x) (-exp (-x)) (h+1)|
    (term ≤ (1/2:ℝ)^(n-h)*n) ∧ (n ≤ 2*h → term ≤ (3/8:ℝ)^(n-h)*(3/2)) := by
  have ⟨raw,high⟩ := two_tier_eulerian_mass hn hh hx region
  have hr := (radius_pos x).le
  constructor
  · exact mul_le_mul ((uniform_factorial_weight (by omega) lo hr).trans
      (pow_le_pow_left₀ (by positivity) radii.2 _)) raw (abs_nonneg _) (by positivity)
  · intro half
    exact mul_le_mul ((upper_half_factorial_weight (by omega) lo half hr).trans
      (pow_le_pow_left₀ (by positivity) radii.1 _)) (high half) (abs_nonneg _) (by positivity)

#print axioms normalized_eulerian_weights
end
end LongCycleBounds.DescentMesh
