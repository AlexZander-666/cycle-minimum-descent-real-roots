import LongCycleBounds.DescentMeshGeometry
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Certified one-sided logarithmic estimates at the integer peak of an angle node. -/
namespace LongCycleBounds.DescentMesh
open Real

/-- Trapezoidal bound for the increment of the logarithm. -/
theorem log_increment_upper {i : ℝ} (hi : 0 < i) :
    log (1+1/i) ≤ 1/i-1/(2*i*(i+1)) := by
  let a := 1+1/i
  have ha : 0 < a := by dsimp [a]; positivity
  have ha1 : 1 ≤ a := by dsimp [a]; linarith [one_div_pos.mpr hi]
  have h := self_le_sinh_iff.mpr (log_nonneg ha1)
  rw [sinh_eq, exp_neg, exp_log ha] at h
  change log a ≤ _
  apply h.trans
  dsimp [a]
  have hip : 0 < i+1 := by positivity
  field_simp
  ring_nf
  exact le_rfl

/-- A second-order upper bound for the negative logarithmic increment. -/
theorem log_decrement_upper {i : ℝ} (hi : 1 < i) :
    log (1-1/i) ≤ -1/i-1/(2*i^2) := by
  have ip : 0 < i := by linarith
  have im : 0 < i-1 := by linarith
  have h := le_log_one_add_of_nonneg (one_div_nonneg.mpr im.le)
  have mulInv : 1 + 1/(i-1) = (1-1/i)⁻¹ := by field_simp; ring
  rw [mulInv, log_inv] at h
  have small : -(-1/i-1/(2*i^2)) ≤ 2*(1/(i-1))/(1/(i-1)+2) := by
    have y : 0 < 1/(i-1)+2 := by positivity
    field_simp
    nlinarith
  linarith

/-- The cotangent parameter lies between its rational envelope and its quadratic correction. -/
theorem cotangent_bracket {N i θ : ℝ} (hN : 0 < N) (hi : 0 < i)
    (ht : 0 < θ) (htop : θ < π/2) (phase : N*θ=i*π) :
    N/i-π^2*i/(2*N) ≤ π*cos θ/sin θ ∧ π*cos θ/sin θ ≤ N/i := by
  have st : 0 < sin θ := sin_pos_of_pos_of_lt_pi ht (by linarith [pi_pos])
  have ct : 0 < cos θ := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], htop⟩
  have pure : π/θ=N/i := by field_simp; linarith
  constructor
  · calc
      N/i-π^2*i/(2*N) = (π/θ)*(1-θ^2/2) := by
        rw [show θ=i*π/N by apply (eq_div_iff hN.ne').mpr; linarith]
        field_simp
      _ ≤ (π/θ)*cos θ := mul_le_mul_of_nonneg_left one_sub_sq_div_two_le_cos (by positivity)
      _ ≤ π*cos θ/sin θ := by
        rw [div_mul_eq_mul_div]
        exact div_le_div_of_nonneg_left (mul_pos pi_pos ct).le st (sin_le ht.le)
  · rw [← pure]
    have tan := le_tan ht.le htop
    rw [tan_eq_sin_div_cos] at tan
    apply (div_le_div_iff₀ st ht).mpr
    nlinarith only [mul_le_mul_of_nonneg_left ((le_div_iff₀ ct).mp tan) pi_pos.le]

/-- The log of the genuine unweighted raw power-exponential summand. -/
noncomputable def logWeight (n x q : ℝ) := n*log q-x*q

theorem exp_logWeight (n : ℕ) (x : ℝ) {q : ℝ} (hq : 0 < q) :
    exp (logWeight n x q) = q^n * exp (-x*q) := by
  rw [logWeight, sub_eq_add_neg, exp_add, exp_nat_mul, exp_log hq, neg_mul]

/-- Both neighboring log ratios at the angular end nodes with their separate rational costs. -/
theorem mesh_neighbors {n i θ : ℝ} (hn : 0 ≤ n) (hi : 1 < i)
    (ht : 0 < θ) (htop : θ < π/2) (phase : (n+1)*θ=i*π) (small : 4*i^2 ≤ n+1) :
    let x := π*cos θ/sin θ
    (logWeight n x (i+1)-logWeight n x i ≤ 1/(4*i)-n/(2*i*(i+1))) ∧
    (logWeight n x (i-1)-logWeight n x i ≤ 1/i-n/(2*i^2)) := by
  let x := π*cos θ/sin θ
  have ip : 0 < i := by linarith
  have Np : 0 < n+1 := by linarith
  have geo := cotangent_bracket Np ip ht htop phase
  have pi2 : π^2 ≤ 10 := by nlinarith [pi_lt_d2,pi_pos]
  have err : π^2*i/(2*(n+1)) ≤ 5/(4*i) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith only [small, mul_nonneg (sub_nonneg.mpr pi2) (sq_nonneg i)]
  have A : log (i+1)-log i=log (1+1/i) := by
    rw [← log_div (by positivity) ip.ne', show (i+1)/i=1+1/i by field_simp]
  have B : log (i-1)-log i=log (1-1/i) := by
    rw [← log_div (by linarith) ip.ne', show (i-1)/i=1-1/i by field_simp]
  have dx₁ : logWeight n x (i+1)-logWeight n x i=n*log (1+1/i)-x := by
    rw [← A, logWeight, logWeight]; ring
  have dx₂ : logWeight n x (i-1)-logWeight n x i=n*log (1-1/i)+x := by
    rw [← B, logWeight, logWeight]; ring
  have xn : (n+1)/i-5/(4*i) ≤ x := by linarith only [err,geo.1]
  constructor
  · calc
      _ = _ := dx₁
      _ ≤ n*(1/i-1/(2*i*(i+1)))-((n+1)/i-5/(4*i)) :=
        sub_le_sub (mul_le_mul_of_nonneg_left (log_increment_upper ip) hn) xn
      _ = _ := by ring
  · calc
      _ = _ := dx₂
      _ ≤ n*(-1/i-1/(2*i^2))+(n+1)/i :=
        add_le_add (mul_le_mul_of_nonneg_left (log_decrement_upper hi) hn) geo.2
      _ = _ := by ring

/-- At each end grid point, both adjacent positive power-exponential weights are suppressed. -/
theorem mesh_quarter_neighbors {n i θ : ℝ} (hn : 64 ≤ n) (hi : 2 ≤ i)
    (ht : 0 < θ) (htop : θ < π/2) (phase : (n+1)*θ=i*π) (small : 4*i^2 ≤ n+1) :
    let x := π*cos θ/sin θ
    exp (logWeight n x (i+1)-logWeight n x i) < 1/4 ∧
    exp (logWeight n x (i-1)-logWeight n x i) < 1/4 := by
  have ip : 0 < i := by linarith
  have ad := mesh_neighbors (by linarith : 0 ≤ n) (by linarith : 1 < i) ht htop phase small
  have margins : 6*i^2+7*i+1 < 2*n ∧ 3*i^2+2*i < n := by
    by_cases h : 4 ≤ i
    · constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr h) (show 0 ≤ 2*i+1 by linarith)]
    · have g := mul_nonneg (show 0 ≤ 4-i by linarith) (show 0 ≤ 4+i by linarith)
      constructor <;> nlinarith
  have ar : 1/(4*i)-n/(2*i*(i+1)) < -(3/2:ℝ) := by
    field_simp
    nlinarith only [margins.1]
  have al : 1/i-n/(2*i^2) < -(3/2:ℝ) := by
    field_simp
    nlinarith only [margins.2]
  have eb : exp (-(3/2:ℝ)) < 1/4 := by
    rw [exp_neg, ← one_div]
    apply one_div_lt_one_div_of_lt (by norm_num)
    apply (log_lt_iff_lt_exp (by norm_num : 0<(4:ℝ))).mp
    rw [show (4:ℝ)=2^2 by norm_num, log_pow]
    linarith [log_two_lt_d9]
  exact ⟨(exp_lt_exp.mpr (ad.1.trans_lt ar)).trans eb, (exp_lt_exp.mpr (ad.2.trans_lt al)).trans eb⟩

#print axioms mesh_quarter_neighbors
#print axioms mesh_neighbors
#print axioms log_increment_upper
#print axioms log_decrement_upper
#print axioms cotangent_bracket
end LongCycleBounds.DescentMesh
