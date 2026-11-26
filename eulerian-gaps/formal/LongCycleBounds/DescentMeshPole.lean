import LongCycleBounds.PoleBridge
import LongCycleBounds.BandMoments
import Mathlib.Analysis.Complex.Trigonometric

/-! Exact phase and a quarter-unit tail on the angular sign mesh. -/
noncomputable section
namespace LongCycleBounds.DescentMesh
open PoleTails Finset Real

private theorem pole_step {c s : ℝ} (hc : c^2+s^2=1) {N : ℕ}
    (hN : 2 ≤ (N:ℝ)) (hs : 2 ≤ (N:ℝ)*s^2) (i : ℕ) :
    ‖pole c s (2*(i:ℝ)+3)^N‖ ≤ 1/(4*((i:ℝ)+1)) - 1/(4*((i:ℝ)+2)) := by
  let l := 2*(i:ℝ)+3
  have hl : 1 ≤ l := by dsimp [l]; linarith [Nat.cast_nonneg (α := ℝ) i]
  have hg : 0 < l^2-1 := by dsimp [l]; nlinarith [Nat.cast_nonneg (α := ℝ) i]
  have hx : 0 ≤ (l^2-1)*s^2 := mul_nonneg hg.le (sq_nonneg _)
  have bern := one_add_mul_self_le_rpow_one_add (show -1 ≤ (l^2-1)*s^2 by linarith)
    (show 1 ≤ (N:ℝ)/2 by linarith)
  have den : l^2-1 ≤ (1+(l^2-1)*s^2)^((N:ℝ)/2) := by
    apply le_trans _ bern
    nlinarith [mul_nonneg hg.le (sub_nonneg.mpr hs)]
  change ‖pole c s l^N‖ ≤ _
  rw [norm_pole_pow c s l hc hl, amplitude, Real.rpow_neg (by linarith)]
  calc
    _ ≤ 1/(l^2-1) := by simpa [one_div] using one_div_le_one_div_of_le hg den
    _ = _ := by
      rw [show l^2-1=4*((i:ℝ)+1)*((i:ℝ)+2) by dsimp [l]; ring]
      have h1 : 0 < (i:ℝ)+1 := by positivity
      have h2 : 0 < (i:ℝ)+2 := by positivity
      field_simp
      ring

/-- The sum of all nonprincipal positive odd poles costs at most one quarter. -/
theorem mesh_pole_tail {c s : ℝ} (hc : c^2+s^2=1) {N : ℕ}
    (hN : 2 ≤ (N:ℝ)) (hs : 2 ≤ (N:ℝ)*s^2) : ‖Bulk.tail c s N‖ ≤ 1/4 := by
  let f (i : ℕ) := pole c s (2*(i:ℝ)+3)^N
  let g (i : ℕ) : ℝ := 1/(4*((i:ℝ)+1))
  have step (i : ℕ) : ‖f i‖ ≤ g i - g (i+1) := by
    dsimp [f, g]
    rw [Nat.cast_add_one, show (i:ℝ)+1+1=i+2 by ring]
    exact pole_step hc hN hs i
  have partialSum (n : ℕ) : ∑ i ∈ range n, ‖f i‖ ≤ g 0 - g n := by
    induction n with
    | zero => simp
    | succ n ih => rw [sum_range_succ]; linarith [step n]
  have bound (n : ℕ) : ∑ i ∈ range n, ‖f i‖ ≤ 1/4 := by
    have hh := partialSum n
    have hn : 0 ≤ g n := by dsimp [g]; positivity
    have h0 : g 0=1/4 := by norm_num [g]
    exact hh.trans ((sub_le_self _ hn).trans h0.le)
  have sm := summable_of_sum_range_le (fun i ↦ norm_nonneg (f i)) bound
  have est := (norm_tsum_le_tsum_norm sm).trans
    (Real.tsum_le_of_sum_range_le (fun i ↦ norm_nonneg (f i)) bound)
  rw [sm.of_norm.tsum_eq_zero_add] at est
  have parts : Bulk.tail c s N = f 0 + ∑' i, f (i+1) := by
    unfold Bulk.tail
    congr 1
    · simp [f]
    · apply tsum_congr
      intro i
      change pole c s (2 * (i:ℝ) + 5)^N = pole c s (2 * ((i+1:ℕ):ℝ) + 3)^N
      rw [Nat.cast_add_one]
      congr 2
      ring
  rwa [parts]

/-- At an exact angular node, the normalized full pole sum is within a quarter of ±1. -/
theorem mesh_principal_gap {N i : ℕ} {θ : ℝ} (hN : 2 ≤ (N:ℝ))
    (hangle : (N:ℝ)*θ = (i:ℝ)*π) (hs : 2 ≤ (N:ℝ)*(sin θ)^2) :
    |(Bulk.total (cos θ) (sin θ) N).re - (-1:ℝ)^i| ≤ 1/4 := by
  have pole_eq : pole (cos θ) (sin θ) 1 = Complex.exp (((-θ:ℝ):ℂ)*Complex.I) := by
    rw [Complex.exp_ofReal_mul_I]
    apply Complex.ext <;> simp [pole]
    · rw [← Complex.ofReal_cos, Complex.ofReal_re]
    · rw [← Complex.ofReal_sin, Complex.ofReal_re]
  have phase : (pole (cos θ) (sin θ) 1^N).re = (-1:ℝ)^i := by
    rw [pole_eq, ← Complex.exp_nat_mul, ← mul_assoc,
      show (N:ℂ)*((-θ:ℝ):ℂ) = ((-((i:ℝ)*π):ℝ):ℂ) by push_cast; exact_mod_cast (by linarith : (N:ℝ)*(-θ) = -((i:ℝ)*π)),
      Complex.exp_ofReal_mul_I]
    simp [cos_nat_mul_pi]
    have cast : (-1:ℂ)^i = (((-1:ℝ)^i:ℝ):ℂ) := by norm_cast
    rw [cast, Complex.ofReal_re]
  have tail := mesh_pole_tail (cos_sq_add_sin_sq θ) hN hs
  rw [Bulk.total, Complex.add_re, phase, add_sub_cancel_left]
  exact (Complex.abs_re_le_norm _).trans tail

/-- The mesh estimate applies to the actual scaled Eulerian polynomial, including x=0. -/
theorem mesh_scaled_eulerian {N i : ℕ} {θ : ℝ} (hN : 8 ≤ (N:ℝ))
    (phase : (N:ℝ)*θ = (i:ℝ)*π) (hsin : 0 < sin θ) (hcos : 0 ≤ cos θ)
    (hregion : 2 ≤ (N:ℝ)*(sin θ)^2) :
    let x := π*cos θ/sin θ
    |Band.scaledMoment (PoleBridge.radius x) (-exp (-x)) N - (-1:ℝ)^i| ≤ 1/4 := by
  let x := π*cos θ/sin θ
  have hx : 0 ≤ x := div_nonneg (mul_nonneg pi_pos.le hcos) hsin.le
  have radius : PoleBridge.radius x = π/sin θ := by
    apply (sq_eq_sq₀ (PoleBridge.radius_pos _).le (div_pos pi_pos hsin).le).mp
    rw [PoleBridge.radius, sq_sqrt (by positivity)]
    dsimp [x]
    field_simp
    linear_combination cos_sq_add_sin_sq θ
  have hc : PoleBridge.c x = cos θ := by unfold PoleBridge.c; rw [radius]; dsimp [x]; field_simp
  have hs : PoleBridge.s x = sin θ := by unfold PoleBridge.s; rw [radius]; field_simp
  have region : 1 ≤ (N:ℝ)*(PoleBridge.s x)^2 := by rw [hs]; linarith
  have val := congrArg Complex.re (PoleBridge.complete_normalization x N N hN region (by linarith))
  have re : PoleBridge.radius x^N*(oddPoleSum N x).re = 2*(Bulk.total (cos θ) (sin θ) N).re := by
    simpa [Complex.mul_re, ← Complex.ofReal_pow, hc, hs] using val
  change |Band.scaledMoment _ _ _ - _| ≤ _
  rw [Band.scaledMoment_poles _ (by exact_mod_cast (by linarith : 2 ≤ (N:ℝ))) _ _ hx]
  have eq := mesh_principal_gap (le_trans (by norm_num) hN) phase hregion
  rw [show PoleBridge.radius x^N*(oddPoleSum N x).re/2 = (Bulk.total (cos θ) (sin θ) N).re
    by linarith]
  exact eq

#print axioms mesh_scaled_eulerian
#print axioms mesh_pole_tail
#print axioms mesh_principal_gap
end LongCycleBounds.DescentMesh
