import LongCycleBounds.OrdinaryEulerianCentralGap
import LongCycleBounds.BandMoments

noncomputable section
namespace LongCycleBounds.OrdinaryEulerianGap
open PoleBridge Bulk Band Real LongCycles
private theorem scaled_eq_poles {p q : ℕ} (hp : 8 ≤ (p:ℝ)) (hq : (p:ℝ) ≤ 2*(q:ℝ))
    (hq₂ : 2 ≤ q) (x : ℝ) (hx : 0 ≤ x) (ha : 1 ≤ (p:ℝ)*s x^2) :
    scaledMoment (radius x) (-Real.exp (-x)) q = (total (c x) (s x) q).re := by
  rw [scaledMoment_poles _ hq₂ _ _ hx]
  have he := congrArg Complex.re (complete_normalization x p q hp ha hq)
  have eq : radius x^q*(oddPoleSum q x).re=2*(total (c x) (s x) q).re := by
    simpa [Complex.mul_re,← Complex.ofReal_pow] using he
  linarith


theorem central_geometry {n : ℕ} (hn : 128 ≤ n) {x : ℝ} (hx : 0 ≤ x)
    (upper : x ≤ 5/2 * sqrt ((n:ℝ)-1)) :
    radius x < 63/25 * sqrt n ∧ 3/2 ≤ (n:ℝ)*s x^2 ∧ 6/5 < s x * sqrt n := by
  have N : (128:ℝ) ≤ n := by exact_mod_cast hn
  have Np : (0:ℝ) < n := by linarith
  have u := sq_sqrt (by linarith : 0 ≤ (n:ℝ)-1)
  have v := sq_sqrt Np.le
  have xx := mul_self_le_mul_self hx upper
  have rho : radius x ^ 2 = x^2+π^2 := sq_sqrt (by positivity)
  have pihi : π^2 < 10 := by nlinarith only [pi_lt_d2, pi_pos, mul_nonneg pi_pos.le (sub_nonneg.mpr pi_lt_d2.le)]
  have pib : (31/10:ℝ) < π := by linarith only [pi_gt_d2]
  have pi2 := mul_self_lt_mul_self (by norm_num : (0:ℝ)≤31/10) pib
  have rsq : radius x ^ 2 < (63/25)^2 * (n:ℝ) := by nlinarith only [xx,u,rho,pihi,N]
  have bound : radius x < 63/25 * sqrt n := (sq_lt_sq₀ (radius_pos x).le (by positivity)).mp
    (by nlinarith only [rsq,v])
  refine ⟨bound,?_,?_⟩
  · rw [s, div_pow, ← mul_div_assoc, le_div_iff₀ (sq_pos_of_pos (radius_pos x))]
    nlinarith only [rsq,mul_lt_mul_of_pos_left pi2 Np,Np]
  · rw [s, div_mul_eq_mul_div, lt_div_iff₀ (radius_pos x)]
    nlinarith only [bound,mul_lt_mul_of_pos_right pib (sqrt_pos.mpr Np),sqrt_nonneg (n:ℝ)]

theorem actual_eulerian_root_gap {n : ℕ} (hn : 128 ≤ n) {x : ℝ} (hx : 0 ≤ x)
    (upper : x ≤ 5/2 * sqrt ((n:ℝ)-1))
    (zero : (eulerian (n-1)).eval (-exp (-x)) = 0) :
    1 < sqrt n * |scaledMoment (radius x) (-exp (-x)) (n+1)| := by
  obtain ⟨_,angular,sine⟩ := central_geometry hn hx upper
  have eight : 8 ≤ (n:ℝ) := by exact_mod_cast (by omega : 8 ≤ n)
  have U (q : ℕ) (hq : n ≤ q) := scaled_eq_poles (p:=n) (q:=q) eight
    (by exact_mod_cast (by omega : n ≤ 2*q)) (by omega) x hx (by linarith)
  have zeroM : scaledMoment (radius x) (-exp (-x)) n = 0 := by
    simp [scaledMoment, moment, zero]
  have z := (U n le_rfl).symm.trans zeroM
  have sp : 0 < s x := div_pos pi_pos (radius_pos x)
  have h := central_pole_gap (c x) (s x) n (circle x) sp eight angular (by rw [z];norm_num)
  rw [z,mul_zero,sub_zero,← U (n+1) (by omega)] at h
  have pos : 0 < sqrt (n:ℝ) := sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n))
  nlinarith only [mul_lt_mul_of_pos_right h pos,sine]

#print axioms central_geometry
#print axioms actual_eulerian_root_gap
end LongCycleBounds.OrdinaryEulerianGap
