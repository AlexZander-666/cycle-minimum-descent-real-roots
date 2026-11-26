import LongCycleBounds.DescentMeshEndTails

/-! Radius budgets at the actual low-alphabet angular nodes. -/
noncomputable section
namespace LongCycleBounds.DescentMesh
open Finset Real Outer

theorem log_weight_exp (n j : ℕ) (x : ℝ) :
    exp (logWeight n x ((j:ℝ)+1)) = weight n x j := by
  rw [exp_logWeight n x (by positivity)]
  unfold weight
  congr 1
  rw [← exp_nat_mul]
  congr 1
  push_cast
  ring

theorem angular_adjacent {n i : ℕ} (hi : 2 ≤ i) (x l r : ℝ)
    (lbound : exp (logWeight n x ((i:ℝ)-1)-logWeight n x i) ≤ l)
    (rbound : exp (logWeight n x ((i:ℝ)+1)-logWeight n x i) ≤ r) :
    weight n x ((i-1)-1) ≤ l*weight n x (i-1) ∧
    weight n x ((i-1)+1) ≤ r*weight n x (i-1) := by
  rw [exp_sub,div_le_iff₀ (exp_pos _)] at lbound rbound
  have a : ((i-1:ℕ):ℝ)+1=i := by rw [Nat.cast_sub (by omega),Nat.cast_one]; ring
  have b : ((i-1-1:ℕ):ℝ)+1=(i:ℝ)-1 := by rw [Nat.cast_sub (by omega),Nat.cast_one]; linarith only [a]
  have c : (((i-1)+1:ℕ):ℝ)+1=(i:ℝ)+1 := by rw [show i-1+1=i by omega]
  simpa only [← log_weight_exp,a,b,c] using And.intro lbound rbound

private theorem exp_five_thirds : (5:ℝ) < exp (5/3) := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 5/3) 5
  norm_num [sum_range_succ] at h
  linarith

theorem regular_adjacent {n i : ℕ} (h128 : 128 ≤ n) (hi : 4 ≤ i) {θ : ℝ}
    (ht : 0<θ) (top : θ<π/2) (phase : ((n:ℝ)+1)*θ=(i:ℝ)*π)
    (small : 4*(i:ℝ)^2 ≤ (n:ℝ)+1) :
    let x := π*cos θ/sin θ
    weight n x (i-1-1) ≤ (1/5)*weight n x (i-1) ∧
    weight n x (i-1+1) ≤ (1/4)*weight n x (i-1) := by
  have ir : (4:ℝ) ≤ i := by exact_mod_cast hi
  have nr : (128:ℝ) ≤ n := by exact_mod_cast h128
  have hh := mesh_neighbors (by linarith : 0 ≤ (n:ℝ)) (by linarith : 1<(i:ℝ)) ht top phase small
  have qq := mesh_quarter_neighbors (by linarith : 64 ≤ (n:ℝ)) (by linarith : 2 ≤ (i:ℝ)) ht top phase small
  have logL : 1/(i:ℝ)-n/(2*(i:ℝ)^2) < -5/3 := by
    field_simp
    nlinarith only [small,ir,mul_nonneg (sub_nonneg.mpr ir) (show 0 ≤ 2*(i:ℝ)+1 by linarith)]
  apply angular_adjacent (by omega)
  · apply (exp_lt_exp.mpr (hh.2.trans_lt logL)).le.trans
    rw [show -(5:ℝ)/3=-(5/3) by ring,exp_neg,← one_div]
    exact one_div_le_one_div_of_le (by norm_num) exp_five_thirds.le
  · exact qq.1.le

private theorem exp_five : (100:ℝ)<exp 5 := by
  apply (show (100:ℝ)<2^7 by norm_num).trans
  apply (log_lt_iff_lt_exp (by positivity)).mp
  rw [log_pow]
  norm_num; linarith [log_two_lt_d9]

theorem three_adjacent {n : ℕ} (h128 : 128 ≤ n) {θ : ℝ}
    (ht : 0<θ) (top : θ<π/2) (phase : ((n:ℝ)+1)*θ=3*π)
    (small : 4*(3:ℝ)^2 ≤ (n:ℝ)+1) :
    let x := π*cos θ/sin θ
    weight n x 1 ≤ (1/100)*weight n x 2 ∧
    weight n x 3 ≤ (1/100)*weight n x 2 := by
  have nr : (128:ℝ) ≤ n := by exact_mod_cast h128
  have hh := mesh_neighbors (by linarith : 0 ≤ (n:ℝ)) (by norm_num : (1:ℝ)<3) ht top phase small
  have sm : exp (-5) ≤ (1:ℝ)/100 := by rw [exp_neg,← one_div]; exact one_div_le_one_div_of_le (by norm_num) exp_five.le
  apply angular_adjacent (i:=3) (by decide)
  · apply (exp_le_exp.mpr (hh.2.trans _)).trans sm
    norm_num; linarith
  · apply (exp_le_exp.mpr (hh.1.trans _)).trans sm
    norm_num; linarith

theorem beta_small {n : ℕ} (h128 : 128 ≤ n) :
    8*(n:ℝ)*exp (1/2-(n:ℝ)/12)<1 := by
  let y := (n:ℝ)/12-1/2
  have nr : (128:ℝ) ≤ n := by exact_mod_cast h128
  have e6 : (256:ℝ)<exp 6 := by
    rw [show (256:ℝ)=2^8 by norm_num]
    apply (log_lt_iff_lt_exp (by positivity)).mp
    rw [log_pow]; norm_num; linarith [log_two_lt_d9]
  have ey : 256*(1+(y-6))<exp y := by
    calc
      _ < exp 6*(1+(y-6)) := (mul_lt_mul_of_pos_right e6 (by dsimp [y]; linarith))
      _ ≤ exp 6*exp (y-6) := mul_le_mul_of_nonneg_left (by linarith only [add_one_le_exp (y-6)]) (exp_nonneg _)
      _ = _ := by rw [← exp_add]; congr 1; ring
  dsimp [y] at ey
  rw [show (1:ℝ)/2-n/12 = -((n:ℝ)/12-1/2) by ring, exp_neg,← div_eq_mul_inv,div_lt_one (exp_pos _)]
  linarith

theorem two_adjacent {n : ℕ} (h128 : 128 ≤ n) {θ : ℝ}
    (ht : 0<θ) (top : θ<π/2) (phase : ((n:ℝ)+1)*θ=2*π)
    (small : 4*(2:ℝ)^2 ≤ (n:ℝ)+1) :
    let x := π*cos θ/sin θ
    let beta := exp (1/2-(n:ℝ)/12)
    weight n x 0 ≤ beta*weight n x 1 ∧ weight n x 2 ≤ beta*weight n x 1 := by
  have nr : (128:ℝ) ≤ n := by exact_mod_cast h128
  have hh := mesh_neighbors (by linarith : 0 ≤ (n:ℝ)) (by norm_num : (1:ℝ)<2) ht top phase small
  apply angular_adjacent (i:=2) (by decide)
  · apply exp_le_exp.mpr (hh.2.trans _); norm_num; linarith
  · apply exp_le_exp.mpr (hh.1.trans _); norm_num

#print axioms regular_adjacent
#print axioms three_adjacent
#print axioms beta_small
#print axioms two_adjacent
end LongCycleBounds.DescentMesh
