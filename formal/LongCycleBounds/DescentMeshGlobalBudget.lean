import LongCycleBounds.DescentMeshConstants
import LongCycleBounds.DescentMeshLoss
import LongCycleBounds.DescentMeshTransform

/-! Reduce the central sign to two ordinary evaluations of the absolute alphabet-degree losses. -/
namespace LongCycleBounds.DescentMesh
open Finset Real
noncomputable section

/-- Absolute norm of all lower alphabet degrees, without dividing by the leading proportion. -/
def lossNorm (n : ℕ) (a : ℕ → ℝ) (v : ℝ) : ℝ :=
  ∑ h ∈ Ico 1 n, |a h| *v^(n-h)

/-- Extract the low-order tail at radius 1/2 from a single larger-radius coefficient norm. -/
theorem low_budget_of_global {n : ℕ} (hn : 128 ≤ n) (a : ℕ → ℝ) (ha : 0 ≤ a n)
    (global : lossNorm n a (2/3) ≤ 16*n*a n) :
    ∑ h ∈ Ico 1 n, (if n ≤ 2*h then 0 else |a h| *(1/2:ℝ)^(n-h)) ≤ a n/(100*n) := by
  let I := (Ico 1 n).filter (fun h ↦ ¬n ≤ 2*h)
  have supp (h : ℕ) (hh : h ∈ I) : n ≤ 2*(n-h) := by have := (mem_filter.mp hh).2; omega
  have raw := reweight_empty I (fun h ↦ n-h) (fun h ↦ |a h|) supp
    (v:=1/2) (V:=2/3) (by norm_num) (by norm_num) (by norm_num)
  have near : 0 ≤ ∑ h∈I, |a h| *(1/2:ℝ)^(n-h) :=
    sum_nonneg fun _ _ ↦ by positivity
  rw [abs_of_nonneg near] at raw
  simp only [abs_abs] at raw
  have larger : ∑ h ∈ I, |a h| *(2/3:ℝ)^(n-h) ≤ lossNorm n a (2/3) := by
    apply sum_le_sum_of_subset_of_nonneg (filter_subset ..)
    intro h _ _
    positivity
  have npos : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0<n)
  have pivot : (1/2:ℝ)/(2/3) = 3/4 := by norm_num
  rw [pivot] at raw
  have pp : (3/4:ℝ)^((n+1)/2) ≤ (3/4:ℝ)^(n/2) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have cap : (3/4:ℝ)^((n+1)/2)*(16*n*a n) ≤ a n/(100*n) := by
    apply (le_div_iff₀ (by positivity)).mpr
    have h := mul_le_mul_of_nonneg_right (power_tail_small n hn).le ha
    have hh := mul_le_mul_of_nonneg_right pp (show 0 ≤ 16*(n:ℝ)^2*a n by positivity)
    nlinarith only [h,hh]
  calc
    _ = ∑ h∈I, |a h| *(1/2:ℝ)^(n-h) := by
      simp only [I, sum_filter]
      apply sum_congr rfl
      intro h _
      split_ifs <;> simp_all
    _ ≤ _ := raw
    _ ≤ _ := mul_le_mul_of_nonneg_left (larger.trans global) (by positivity)
    _ ≤ _ := cap

/-- Full Eulerian transform sign with only two scalar alphabet norm hypotheses left open. -/
theorem central_sign_of_global {n i : ℕ} (hn : 128 ≤ n) {θ : ℝ}
    (lo : π/(2*sqrt ((n:ℝ)+1)) ≤ θ) (top : θ ≤ π/2)
    (phase : ((n:ℝ)+1)*θ=(i:ℝ)*π) (a : ℕ → ℝ) (positive : 0 < a n)
    (high : lossNorm n a (3/8) ≤ (3/7)*a n) (global : lossNorm n a (2/3) ≤ 16*n*a n) :
    (-1:ℝ)^i * (descentTransform n a).eval (-exp (-(π*cos θ/sin θ))) < 0 :=
  central_sign_of_budgets hn lo top phase a positive high (low_budget_of_global hn a positive.le global)

#print axioms central_sign_of_global
end
end LongCycleBounds.DescentMesh
