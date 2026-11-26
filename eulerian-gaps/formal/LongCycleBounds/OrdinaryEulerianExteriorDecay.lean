import LongCycleBounds.OuterDecay

/-! Concentration of the Eulerian moment at the first ratio crossing in the exterior region. -/
noncomputable section

namespace LongCycleBounds.OrdinaryEulerianExterior
open Real Outer

/-- In positive-label indexing the mode lies at or below half the square root. -/
theorem mode_label_bound (p : ℕ) (hp : 64 ≤ p) (x : ℝ) (hx : 0 < x)
    (region : 5 * sqrt p / 2 ≤ x) : (mode p x hx : ℝ) + 1 ≤ sqrt p / 2 := by
  have base : 8 ≤ sqrt (p : ℝ) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    exact_mod_cast hp
  have M := mode_index_mul_le p x hx
  have A := mul_le_mul_of_nonneg_left region (Nat.cast_nonneg (mode p x hx))
  have square := sq_sqrt (show (0 : ℝ) ≤ p by positivity)
  have cap : 5 * (mode p x hx : ℝ) ≤ 2 * sqrt p := by
    by_contra! bad
    nlinarith [mul_pos (sub_pos.mpr bad) (show 0 < sqrt (p : ℝ) by linarith)]
  by_cases small : mode p x hx ≤ 3
  · have : (mode p x hx : ℝ) ≤ 3 := by exact_mod_cast small
    linarith
  · have : (4 : ℝ) ≤ mode p x hx := by exact_mod_cast (show 4 ≤ mode p x hx by omega)
    linarith

private theorem exp_neg_four : exp (-4) < 1/50 := by
  rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos _) (by norm_num)]
  have E : (27/10 : ℝ) < exp 1 := by linarith [exp_one_gt_d9]
  have H := pow_lt_pow_left₀ E (by norm_num : (0:ℝ) ≤ 27/10) (by decide : 4 ≠ 0)
  rw [← Real.exp_nat_mul] at H
  norm_num at H ⊢
  linarith

/-- Even when the first point to the right of the mode exceeds the
half-square-root threshold, its outward ratio is at most one fiftieth. -/
theorem right_second_ratio (p : ℕ) (hp : 64 ≤ p) (x : ℝ) (hx : 0 < x)
    (region : 5 * sqrt p / 2 ≤ x) : ratio p x (mode p x hx + 1) ≤ 1/50 := by
  let m := mode p x hx
  by_cases short : (m : ℝ) + 2 ≤ sqrt p / 2
  · exact (ratio_contracts p x m short).trans
      (by simpa using mul_le_mul_of_nonneg_left (ratio_mode_le p x hx) (by norm_num : (0:ℝ) ≤ 1/50))
  · have base : 8 ≤ sqrt (p : ℝ) := by
      rw [Real.le_sqrt (by norm_num) (by positivity)]
      exact_mod_cast hp
    have square := sq_sqrt (show (0 : ℝ) ≤ p by positivity)
    have upper : (p : ℝ)/((m : ℝ)+2) ≤ 2 * sqrt p := by
      apply (div_le_iff₀ (by positivity)).mpr
      push Not at short
      nlinarith [mul_nonneg (show 0 ≤ sqrt (p : ℝ) by positivity)
        (sub_nonneg.mpr short.le)]
    apply (ratio_le_exp p x (m+1)).trans ((Real.exp_le_exp.mpr ?_).trans exp_neg_four.le)
    push_cast
    rw [show (m:ℝ)+1+1=(m:ℝ)+2 by ring]
    linarith

theorem right_succ_decay (N : ℕ) (hN : 64 ≤ N) (x : ℝ) (hx : 0 < x)
    (hregion : 5*Real.sqrt N/2 ≤ x) {j : ℕ} (hj : mode N x hx < j) :
    weight N x (j+1) ≤ (1/50 : ℝ) * weight N x j := by
  have cap := right_second_ratio N hN x hx hregion
  rw [weight_succ]
  exact mul_le_mul_of_nonneg_right ((ratio_antitone N x (by omega : mode N x hx+1 ≤ j)).trans cap)
    (weight_pos ..).le

theorem left_succ_decay (N : ℕ) (hN : 64 ≤ N) (x : ℝ) (hx : 0 < x)
    (hregion : 5*Real.sqrt N/2 ≤ x) (d : ℕ) (hd : 1 ≤ d) :
    leftAt (weight N x) (mode N x hx) (d+1) ≤ (1/50 : ℝ)*leftAt (weight N x) (mode N x hx) d := by
  let m := mode N x hx
  by_cases he : d+1 ≤ m
  · let j := m-(d+1)
    have hj : j+1 = m-d := by dsimp [j]; omega
    have hbf : j+1 < mode N x hx := by change j+1 < m; omega
    have hcast : (j:ℝ)+1 ≤ (mode N x hx:ℝ) := by
      exact_mod_cast hbf.le
    have mcap := mode_label_bound N hN x hx hregion
    have ctr : (j:ℝ)+2 ≤ sqrt N/2 := by linarith
    have he' := ratio_contracts N x j ctr
    have hr := (one_lt_ratio_before N x hx hbf).le.trans he'
    change leftAt (weight N x) m (d+1) ≤ _ * leftAt (weight N x) m d
    rw [leftAt, if_pos he, leftAt, if_pos (by omega : d ≤ m), ← hj]
    change weight N x j ≤ _ * weight N x (j+1)
    rw [weight_succ, ← mul_assoc]
    exact le_mul_of_one_le_left (weight_pos ..).le hr
  · change leftAt (weight N x) m (d+1) ≤ _ * leftAt (weight N x) m d
    rw [leftAt, if_neg he]
    exact mul_nonneg (by norm_num) (leftAt_nonneg (fun _ ↦ (weight_pos ..).le) ..)

theorem neighbors_product (N : ℕ) (hN : 64 ≤ N) (x : ℝ) (hx : 0 < x)
    (hregion : 5*Real.sqrt N/2 ≤ x) :
    let m := mode N x hx
    leftAt (weight N x) m 1 * weight N x (m+1) ≤ (1/50 : ℝ)*weight N x m ^ 2 := by
  dsimp only
  generalize hm : mode N x hx = m
  cases m with
  | zero => simp [leftAt]; positivity
  | succ j =>
    have h := mode_label_bound N hN x hx hregion
    rw [hm] at h
    push_cast at h
    have hr := ratio_contracts N x j (by linarith)
    simp only [leftAt, if_pos (show 1 ≤ j+1 by omega), Nat.add_one_sub_one]
    rw [weight_succ N x (j+1), weight_succ N x j]
    nlinarith [mul_le_mul_of_nonneg_right hr
      (mul_nonneg (ratio_pos N x j).le (sq_nonneg (weight N x j)))]

theorem neighbors_min_le (N : ℕ) (hN : 64 ≤ N) (x : ℝ) (hx : 0 < x)
    (hregion : 5*Real.sqrt N/2 ≤ x) :
    let m := mode N x hx
    min (leftAt (weight N x) m 1) (weight N x (m+1)) ≤ weight N x m/7 := by
  dsimp only
  have hp := neighbors_product N hN x hx hregion
  dsimp only at hp
  by_contra! bad
  rw [lt_min_iff] at bad
  have hh := mul_lt_mul_of_pos_left bad.2 (weight_pos N x (mode N x hx))
  have hmp := mul_lt_mul_of_pos_right bad.1 (weight_pos N x (mode N x hx+1))
  nlinarith [sq_pos_of_pos (weight_pos N x (mode N x hx))]

theorem both_geometric (N : ℕ) (hN : 64 ≤ N) (x : ℝ) (hx : 0 < x)
    (hregion : 5*Real.sqrt N/2 ≤ x) (l : ℕ) :
    let m := mode N x hx
    leftAt (weight N x) m (l+1) ≤ (1/50 : ℝ)^l*weight N x m ∧
      weight N x (m+(l+1)) ≤ (1/50 : ℝ)^l*weight N x m := by
  let m := mode N x hx
  change leftAt (weight N x) m (l+1) ≤ _ ∧ weight N x (m+(l+1)) ≤ _
  induction l with
  | zero =>
    simp only [zero_add, pow_zero, one_mul]
    constructor
    · unfold leftAt
      split
      · exact weight_le_mode ..
      · exact (weight_pos ..).le
    · exact weight_le_mode ..
  | succ l ih =>
    have hl := left_succ_decay N hN x hx hregion (l+1) (by omega)
    have hr := right_succ_decay N hN x hx hregion (j := m+(l+1)) (by change m < _; omega)
    constructor
    · exact hl.trans (by rw [pow_succ']; rw [mul_assoc]; exact mul_le_mul_of_nonneg_left ih.1 (by norm_num))
    · exact hr.trans (by rw [pow_succ']; rw [mul_assoc]; exact mul_le_mul_of_nonneg_left ih.2 (by norm_num))

/-- When the mode is at positive label two or three, the weaker neighbor costs
at most one fiftieth of its mass throughout the large-size range. -/
theorem neighbors_small (p : ℕ) (hp : 72 ≤ p) (x : ℝ) (hx : 0 < x)
    (small : mode p x hx ≤ 2) :
    let m := mode p x hx
    min (leftAt (weight p x) m 1) (weight p x (m+1)) ≤ weight p x m / 50 := by
  dsimp only
  generalize hm : mode p x hx = m at *
  cases m with
  | zero =>
    have hz : leftAt (weight p x) 0 1 = 0 := by rfl
    rw [hz]
    exact (min_le_left ..).trans (div_nonneg (weight_pos p x 0).le (by norm_num))
  | succ j =>
    have two : (j : ℝ)+2 ≤ 3 := by
      have : j ≤ 1 := by omega
      exact_mod_cast (show j+2 ≤ 3 by omega)
    have jp : 0 < (j:ℝ)+2 := by positivity
    have J : ((j:ℝ)+2)^2 ≤ 9 := by nlinarith only [sq_le_sq₀ jp.le (by norm_num : (0:ℝ) ≤ 3) |>.2 two]
    have N : (72:ℝ) ≤ p := by exact_mod_cast hp
    let a := 1/((j:ℝ)+2)^2
    have ha : 0 ≤ 1-a := by
      apply sub_nonneg.mpr
      exact (div_le_one (sq_pos_of_pos jp)).mpr (by nlinarith [sq_nonneg (j:ℝ)])
    have factor : (1-a)^p ≤ (1/50:ℝ)^2 := by
      have bound : 1-a ≤ exp (-a) := by linarith [Real.add_one_le_exp (-a)]
      apply (pow_le_pow_left₀ ha bound p).trans
      rw [← Real.exp_nat_mul]
      have h : 8 ≤ (p:ℝ)/((j:ℝ)+2)^2 := (le_div_iff₀ (sq_pos_of_pos jp)).mpr (by linarith)
      calc
        exp ((p:ℝ)* -a) ≤ exp (-4+-4) := Real.exp_le_exp.mpr (by dsimp [a]; linarith [show (p:ℝ)* -(1/((j:ℝ)+2)^2) = -(p/((j:ℝ)+2)^2) by ring])
        _ = exp (-4)^2 := by rw [Real.exp_add,pow_two]
        _ ≤ _ := pow_le_pow_left₀ (Real.exp_nonneg _) exp_neg_four.le _
    have ratioBound : ratio p x (j+1) ≤ (1/50:ℝ)^2 * ratio p x j := by
      rw [ratio_succ_eq]
      exact mul_le_mul_of_nonneg_right factor (ratio_pos ..).le
    simp only [leftAt, if_pos (show 1 ≤ j+1 by omega), Nat.add_one_sub_one]
    have prod : weight p x j * weight p x (j+1+1) ≤ (1/50:ℝ)^2 * weight p x (j+1)^2 := by
      rw [weight_succ p x (j+1),weight_succ p x j]
      nlinarith [mul_le_mul_of_nonneg_right ratioBound
        (mul_nonneg (ratio_pos p x j).le (sq_nonneg (weight p x j)))]
    by_contra! bad
    rw [lt_min_iff] at bad
    have A := mul_lt_mul_of_pos_right bad.1 (weight_pos p x (j+1+1))
    have B := mul_lt_mul_of_pos_left bad.2 (weight_pos p x (j+1))
    nlinarith

#print axioms neighbors_small
#print axioms neighbors_min_le
#print axioms both_geometric
end LongCycleBounds.OrdinaryEulerianExterior
