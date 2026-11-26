import LongCycleBounds.DescentActualReciprocal
import LongCycleBounds.DescentMeshEndSign

/-! The scalar alphabet coefficients control their positive integer evaluations
and the genuine Eulerian-transform series at every positive x. -/
noncomputable section
namespace LongCycleBounds.DescentMesh
open Finset Polynomial Real LongCycles FixedCycleCount

def colorEval (n : ℕ) (a : ℕ→ℝ) (q : ℕ) : ℝ := ∑ h ∈ Icc 1 n, a h*(q:ℝ)^h

theorem color_relative_norm {n : ℕ} (hn : 1 ≤ n) (a : ℕ→ℝ) {j : ℕ} {v : ℝ}
    (hv : 1/((j:ℝ)+1) ≤ v) :
    |colorEval n a (j+1)/((j:ℝ)+1)^n - a n| ≤ lossNorm n a v := by
  let q := (j:ℝ)+1
  have qp : 0<q := by dsimp [q]; positivity
  have s : Icc 1 n=insert n (Ico 1 n) := by ext h; simp; omega
  unfold colorEval
  rw [s,sum_insert (by simp),add_div,Nat.cast_succ]
  change |a n*q^n/q^n+(∑ h ∈ Ico 1 n, a h*q^h)/q^n-a n| ≤ _
  rw [mul_div_cancel_right₀ _ (pow_ne_zero _ qp.ne'),add_sub_cancel_left,sum_div]
  apply (abs_sum_le_sum_abs ..).trans
  unfold lossNorm
  apply sum_le_sum
  intro h hh
  have le := (mem_Ico.mp hh).2.le
  have pow : q^n = q^h*q^(n-h) := by rw [← pow_add, Nat.add_sub_of_le le]
  rw [pow,abs_div,abs_mul,abs_of_pos (pow_pos qp h),abs_of_pos (mul_pos (pow_pos qp _) (pow_pos qp _))]
  have eq : |a h| *q^h/(q^h*q^(n-h))=|a h| *(1/q)^(n-h) := by
    rw [div_pow,one_pow]; field_simp
  rw [eq]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hv _) (abs_nonneg _)

theorem ratio_window {n : ℕ} (hn : 1≤n) (a : ℕ→ℝ) {j : ℕ} {v p e : ℝ}
    (hp : 0<p) (top : a n=p) (hv : 1/((j:ℝ)+1) ≤ v)
    (bound : lossNorm n a v ≤ e*p) :
    1-e ≤ labelRatio n (colorEval n a) p j ∧ labelRatio n (colorEval n a) p j ≤ 1+e := by
  have h := (color_relative_norm hn a hv).trans bound
  rw [top,abs_le] at h
  have eq : labelRatio n (colorEval n a) p j =
      (colorEval n a (j+1)/((j:ℝ)+1)^n)/p := by unfold labelRatio; ring
  rw [eq]
  exact ⟨(le_div_iff₀ hp).mpr (by linarith only [h.1]),(div_le_iff₀ hp).mpr (by linarith only [h.2])⟩

theorem labelSeries_transform (n : ℕ) (a : ℕ→ℝ) {x : ℝ} (hx : 0<x) :
    labelSeries (colorEval n a) x =
      exp (-x)/(1+exp (-x))^(n+1)*(descentTransform n a).eval (-exp (-x)) := by
  let t := -exp (-x)
  have ht : ‖t‖<1 := by
    change ‖-exp (-x)‖<1
    rw [norm_neg,Real.norm_of_nonneg (exp_nonneg _),exp_lt_one_iff]; linarith
  have t0 : t≠0 := neg_ne_zero.mpr (exp_ne_zero _)
  have summ (h : ℕ) (_ : h ∈ Icc 1 n) : Summable (fun j : ℕ ↦ a h*(((j:ℝ)+1)^h*t^j)) := by
    have sh := (summable_nat_add_iff (f:=fun j : ℕ ↦ (j:ℝ)^h*t^j) 1).mpr
      (summable_pow_mul_geometric_of_norm_lt_one h ht)
    apply Summable.mul_left
    apply (sh.mul_right t⁻¹).congr
    intro j
    push_cast
    rw [pow_succ]
    field_simp
  have split : labelSeries (colorEval n a) x =
      exp (-x)*(∑ h ∈ Icc 1 n, a h*shiftedMoment h t) := by
    unfold labelSeries shiftedMoment
    simp_rw [← tsum_mul_left]
    rw [← Summable.tsum_finsetSum summ,← tsum_mul_left]
    apply tsum_congr
    intro j
    simp only [colorEval,Nat.cast_succ,mul_sum,sum_mul,show t=(-1:ℝ)*exp (-x) by dsimp [t]; ring,
      mul_pow,pow_succ (exp (-x))]
    apply sum_congr rfl
    intro h _
    ring
  rw [split]
  simp_rw [shiftedMoment_eq_eulerian _ longEulerian_zero longEulerian_succ _ _ ht]
  rw [mul_sum]
  simp only [descentTransform,eval_finsetSum,eval_mul,eval_C,eval_pow,eval_sub,eval_one,eval_X,mul_sum]
  apply sum_congr rfl
  intro h hh
  have dec : (1+exp (-x))^(n+1) = (1+exp (-x))^(n-h)*(1+exp (-x))^(h+1) := by
    rw [← pow_add]; congr 1; have := (mem_Icc.mp hh).2; omega
  simp only [t,sub_neg_eq_add]
  rw [dec]
  field_simp

#print axioms color_relative_norm
#print axioms labelSeries_transform
end LongCycleBounds.DescentMesh
