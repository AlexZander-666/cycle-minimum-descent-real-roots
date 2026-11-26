import LongCycleBounds.DescentMeshCentralWeights
import Mathlib.Analysis.Complex.ExponentialBounds

/-! The Eulerian polynomial transform of a genuine alphabet polynomial. -/
noncomputable section
namespace LongCycleBounds.DescentMesh
open Finset Polynomial LongCycles Real Band PoleBridge

/-- Eulerian transform in a fixed ambient degree n for a zero-constant alphabet polynomial. -/
def descentTransform (n : ℕ) (a : ℕ → ℝ) : Polynomial ℝ :=
  ∑ h ∈ Icc 1 n, C (a h) * (1-X)^(n-h) * eulerian h

private theorem transform_summand {n h : ℕ} (hh : h ≤ n) {r t : ℝ} (ht : t ≠ 1) (a : ℝ) :
    t*r^(n+1)/(2*n.factorial*(1-t)^(n+1)) *
      (a*(1-t)^(n-h)*(eulerian h).eval t) =
    a*((h.factorial:ℝ)/n.factorial)*r^(n-h)*scaledMoment r t (h+1) := by
  have pow (z : ℝ) : z^(n+1)=z^(n-h)*z^(h+1) := by
    rw [← pow_add]; congr 1; omega
  have t0 : 1-t ≠ 0 := sub_ne_zero.mpr (Ne.symm ht)
  simp only [scaledMoment, moment, Nat.add_sub_cancel]
  rw [pow r, pow (1-t)]
  field_simp

/-- Exact scaling. In particular at a negative value of t the prefactor is negative. -/
theorem normalized_transform (n : ℕ) (a : ℕ → ℝ) {r t : ℝ} (ht : t ≠ 1) :
    t*r^(n+1)/(2*n.factorial*(1-t)^(n+1)) * (descentTransform n a).eval t =
      ∑ h ∈ Icc 1 n, a h*((h.factorial:ℝ)/n.factorial)*r^(n-h)*scaledMoment r t (h+1) := by
  simp only [descentTransform, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_sub, eval_one,
    eval_X, mul_sum]
  exact sum_congr rfl fun h hh ↦ transform_summand (mem_Icc.mp hh).2 (r:=r) ht (a h)

/-- At two scalar coefficient budgets the signed transform must lie in the half-plane of the
leading pole. Both the moments and the Eulerian polynomial on the left are the actual ones. -/
theorem central_transform_gap {n : ℕ} (hn : 2 ≤ n) {x : ℝ} (hx : 0 ≤ x)
    (region : 2 ≤ ((n:ℝ)+1)*(s x)^2)
    (radii : 2*radius x/n ≤ 3/8 ∧ exp 1*radius x/n ≤ 1/2)
    (a : ℕ → ℝ)
    (budgetH : ∑ h ∈ Ico 1 n, |a h| *(3/8:ℝ)^(n-h) ≤ (3/7)*a n)
    (budgetL : ∑ h ∈ Ico 1 n, (if n ≤ 2*h then 0 else |a h| *(1/2:ℝ)^(n-h)) ≤
      a n/(100*n)) :
    let t := -exp (-x)
    let r := radius x
    |t*r^(n+1)/(2*n.factorial*(1-t)^(n+1)) * (descentTransform n a).eval t -
      a n * scaledMoment r t (n+1)| ≤ (9/14+1/100)*a n := by
  let t := -exp (-x)
  let r := radius x
  let T (h : ℕ) := ((h.factorial:ℝ)/n.factorial)*r^(n-h)
  let U (h : ℕ) := scaledMoment r t (h+1)
  let H (h : ℕ) := |a h| *(3/8:ℝ)^(n-h)
  let L (h : ℕ) := if n ≤ 2*h then 0 else |a h| *(1/2:ℝ)^(n-h)
  have ht : t ≠ 1 := by dsimp [t]; linarith [exp_pos (-x)]
  have eq := normalized_transform n a (r:=r) ht
  have eLast : T n = 1 := by simp [T, Nat.factorial_ne_zero]
  have zero : ∑ h ∈ Icc 1 n, a h*T h*U h =
      (∑ h ∈ Ico 1 n, a h*T h*U h) + a n*U n := by
    rw [← Finset.Ico_insert_right (by omega : 1 ≤ n), Finset.sum_insert (by simp), eLast]
    ring
  change |t*r^(n+1)/(2*n.factorial*(1-t)^(n+1)) * (descentTransform n a).eval t -
    a n*U n| ≤ _
  rw [eq]
  have regroup : (∑ h ∈ Icc 1 n, a h*((h.factorial:ℝ)/n.factorial)*r^(n-h)*
      scaledMoment r t (h+1)) = ∑ h ∈ Icc 1 n, a h*T h*U h := by
    apply sum_congr rfl
    intro h _
    dsimp [T,U]
    ring
  rw [regroup, zero, add_sub_cancel_right]
  apply (abs_sum_le_sum_abs _ _).trans
  have point (h : ℕ) (mem : h ∈ Ico 1 n) : |a h*T h*U h| ≤ (3/2)*H h+n*L h := by
    have ⟨h1,hl⟩ := mem_Ico.mp mem
    obtain ⟨lw,hi⟩ := normalized_eulerian_weights hn h1 hl.le hx region radii
    have pos : 0 ≤ T h := mul_nonneg (by positivity) (pow_nonneg (radius_pos x).le _)
    rw [abs_mul, abs_mul, abs_of_nonneg pos, mul_assoc]
    by_cases half : n ≤ 2*h
    · simp only [L,if_pos half,mul_zero,add_zero,H]
      have hh := hi half
      change T h * |U h| ≤ (3/8:ℝ)^(n-h)*(3/2) at hh
      calc
        _ ≤ |a h| *((3/8:ℝ)^(n-h)*(3/2)) := mul_le_mul_of_nonneg_left hh (abs_nonneg _)
        _ = _ := by ring
    · simp only [L,if_neg half]
      have add : 0 ≤ (3/2)*H h := by dsimp [H]; positivity
      have bound := mul_le_mul_of_nonneg_left lw (abs_nonneg (a h))
      change |a h| *(T h * |U h|) ≤ _ at bound
      linarith only [bound,add, mul_comm (n:ℝ) (|a h| *(1/2:ℝ)^(n-h))]
  have agg := sum_le_sum point
  rw [sum_add_distrib, ← mul_sum, ← mul_sum] at agg
  have p : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0<n)
  have low : (n:ℝ)*∑ h∈Ico 1 n, L h ≤ a n/100 := by
    calc
      _ ≤ (n:ℝ)*(a n/(100*n)) := mul_le_mul_of_nonneg_left budgetL p.le
      _ = _ := by field_simp
  change ∑ h ∈ Ico 1 n, H h ≤ (3/7)*a n at budgetH
  linarith only [agg, budgetH, low]

/-- Given the two coefficient budgets, the genuine Eulerian transform has the required
strict central mesh sign. All geometric and factorial budgets are discharged here. -/
theorem central_sign_of_budgets {n i : ℕ} (hn : 128 ≤ n) {θ : ℝ}
    (lo : π/(2*sqrt ((n:ℝ)+1)) ≤ θ) (top : θ ≤ π/2)
    (phase : ((n:ℝ)+1)*θ=(i:ℝ)*π) (a : ℕ → ℝ) (positive : 0 < a n)
    (budgetH : ∑ h ∈ Ico 1 n, |a h| *(3/8:ℝ)^(n-h) ≤ (3/7)*a n)
    (budgetL : ∑ h ∈ Ico 1 n, (if n ≤ 2*h then 0 else |a h| *(1/2:ℝ)^(n-h)) ≤
      a n/(100*n)) :
    (-1:ℝ)^i * (descentTransform n a).eval (-exp (-(π*cos θ/sin θ))) < 0 := by
  let x := π*cos θ/sin θ
  let t := -exp (-x)
  have nr : (128:ℝ) ≤ n := by exact_mod_cast hn
  have np : 0 < (n:ℝ) := by linarith
  have spos : 0 < sin θ := sin_pos_of_pos_of_lt_pi (lt_of_lt_of_le (by positivity) lo)
    (by linarith [pi_pos])
  have cpos : 0 ≤ cos θ := cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos, show 0 < π/(2*sqrt ((n:ℝ)+1)) by positivity], top⟩
  have hx : 0 ≤ x := div_nonneg (mul_nonneg pi_pos.le cpos) spos.le
  have rpos := radius_pos x
  have req : radius x = π/sin θ := by
    apply (sq_eq_sq₀ rpos.le (div_pos pi_pos spos).le).mp
    rw [radius, sq_sqrt (by positivity)]
    dsimp [x]
    field_simp
    linear_combination cos_sq_add_sin_sq θ
  have seq : s x = sin θ := by unfold s; rw [req]; field_simp
  have ⟨reg,rad⟩ := central_mesh_geometry (by linarith : 129 ≤ (n:ℝ)+1) lo top
  rw [add_sub_cancel_right, ← req] at rad
  have ss : (113/10:ℝ) ≤ sqrt (n:ℝ) := by
    apply (sq_le_sq₀ (by norm_num) (sqrt_nonneg _)).mp
    rw [sq_sqrt np.le]
    linarith
  have S := mul_le_mul_of_nonneg_right ss (sqrt_nonneg (n:ℝ))
  have nn := sq_sqrt np.le
  have radii : 2*radius x/n ≤ 3/8 ∧ exp 1*radius x/n ≤ 1/2 := by
    constructor <;> apply (div_le_iff₀ np).mpr
    · nlinarith only [rad,S,nn,sqrt_nonneg (n:ℝ)]
    · have e : exp 1 ≤ 11/4 := by linarith [exp_one_lt_d9]
      nlinarith only [rad,S,nn,mul_le_mul_of_nonneg_right e rpos.le,sqrt_nonneg (n:ℝ)]
  have gap := central_transform_gap (by omega : 2≤n) hx (by rwa [seq]) radii a budgetH budgetL
  have leading := mesh_scaled_eulerian (N:=n+1) (i:=i) (by push_cast; linarith)
    (by simpa using phase) spos cpos (by simpa using reg)
  let U := scaledMoment (radius x) t (n+1)
  let C := t*radius x^(n+1)/(2*n.factorial*(1-t)^(n+1))
  change |C*(descentTransform n a).eval t - a n*U| ≤ _ at gap
  change |U-(-1:ℝ)^i| ≤ 1/4 at leading
  have tneg : t < 0 := neg_lt_zero.mpr (exp_pos _)
  have Cneg : C < 0 := div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos tneg (pow_pos rpos _))
    (mul_pos (by positivity) (pow_pos (by linarith) _))
  change (-1:ℝ)^i * (descentTransform n a).eval t < 0
  rcases Nat.even_or_odd i with ev | od
  · rw [ev.neg_one_pow] at leading ⊢
    have lower := mul_le_mul_of_nonneg_left (abs_le.mp leading).1 positive.le
    have h : 0 < C*(descentTransform n a).eval t := by
      linarith only [(abs_le.mp gap).1,lower,positive]
    simpa only [one_mul] using neg_of_mul_pos_right h Cneg.le
  · rw [od.neg_one_pow] at leading ⊢
    have upper := mul_le_mul_of_nonneg_left (abs_le.mp leading).2 positive.le
    have h : C*(descentTransform n a).eval t < 0 := by
      linarith only [(abs_le.mp gap).2,upper,positive]
    simpa only [neg_one_mul,neg_lt_zero] using pos_of_mul_neg_right h Cneg.le

#print axioms central_sign_of_budgets
#print axioms normalized_transform
#print axioms central_transform_gap
end LongCycleBounds.DescentMesh
