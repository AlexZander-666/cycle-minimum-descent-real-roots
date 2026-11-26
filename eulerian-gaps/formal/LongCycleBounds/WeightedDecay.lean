import LongCycleBounds.OuterDecay

/-! The sharper discrete tails used with bounded positive transfer weights. -/

noncomputable section

namespace LongCycleBounds.Outer

private theorem exp_neg_eleven_halves_lt : Real.exp (-11 / 2) < 1 / 200 := by
  rw [show (-11 / 2 : ℝ) = -(11 / 2) by ring, Real.exp_neg,
    inv_lt_comm₀ (Real.exp_pos _) (by norm_num)]
  have hbase : (27 / 10 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hpow := pow_lt_pow_left₀ hbase (by norm_num : (0 : ℝ) ≤ 27 / 10) (by decide : 5 ≠ 0)
  rw [← Real.exp_nat_mul] at hpow
  norm_num at hpow ⊢
  have hhalf := Real.add_one_le_exp (1 / 2 : ℝ)
  have hprod := mul_lt_mul_of_pos_right hpow (Real.exp_pos (1 / 2))
  rw [show (11 / 2 : ℝ) = 5 + 1 / 2 by ring, Real.exp_add]
  nlinarith only [hprod, hhalf]

theorem mode_add_two_le_weighted_sqrt (N : ℕ) (hN : 40000 ≤ N) (x : ℝ) (hx : 0 < x)
    (hregion : 5 * Real.sqrt N / 2 ≤ x) :
    (mode N x hx : ℝ) + 2 ≤ (41 / 100 : ℝ) * Real.sqrt N := by
  have hroot : 200 ≤ Real.sqrt (N : ℝ) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    exact_mod_cast hN
  have hpos : 0 < Real.sqrt (N : ℝ) := by linarith
  have hsq := Real.sq_sqrt (show 0 ≤ (N : ℝ) by positivity)
  have hi := mode_index_mul_le N x hx
  have hbound := mul_le_mul_of_nonneg_left hregion (Nat.cast_nonneg (mode N x hx))
  have hm : (5 / 2 : ℝ) * (mode N x hx : ℝ) ≤ Real.sqrt N := by
    apply (mul_le_mul_iff_right₀ hpos).mp
    nlinarith only [hi, hbound, hsq]
  linarith only [hm, hroot]

theorem ratio_contracts_weighted (N : ℕ) (hN : 0 < N) (x : ℝ) (j : ℕ)
    (hj : (j : ℝ) + 2 ≤ (41 / 100 : ℝ) * Real.sqrt N) :
    ratio N x (j + 1) ≤ (1 / 200 : ℝ) * ratio N x j := by
  rw [ratio_succ_eq]
  apply mul_le_mul_of_nonneg_right _ (ratio_pos ..).le
  let a := 1 / ((j : ℝ) + 2)^2
  have ha : 0 ≤ 1 - a := by
    apply sub_nonneg.mpr
    exact (div_le_one (by positivity : 0 < ((j : ℝ) + 2)^2)).mpr
      (by nlinarith [sq_nonneg (j : ℝ)])
  have he : 1 - a ≤ Real.exp (-a) := by linarith [Real.add_one_le_exp (-a)]
  apply (pow_le_pow_left₀ ha he N).trans
  rw [← Real.exp_nat_mul]
  apply le_trans _ exp_neg_eleven_halves_lt.le
  apply Real.exp_le_exp.mpr
  have hs := sq_le_sq' (by linarith [Real.sqrt_nonneg (N : ℝ)] :
    -((41 / 100 : ℝ) * Real.sqrt N) ≤ (j : ℝ) + 2) hj
  have hsq := Real.sq_sqrt (show 0 ≤ (N : ℝ) by positivity)
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have h : (11 / 2 : ℝ) ≤ (N : ℝ) / ((j : ℝ) + 2)^2 :=
    (le_div_iff₀ (by positivity)).mpr (by nlinarith only [hs, hsq, hNr])
  dsimp [a]
  linarith only [h, show (N : ℝ) * (1 / ((j : ℝ) + 2)^2) = N / ((j : ℝ) + 2)^2 by ring]

private theorem weighted_ratio_at_or_before (N : ℕ) (hN : 40000 ≤ N) (x : ℝ)
    (hx : 0 < x) (hregion : 5 * Real.sqrt N / 2 ≤ x) {j : ℕ} (hj : j ≤ mode N x hx) :
    ratio N x (j + 1) ≤ (1 / 200 : ℝ) * ratio N x j := by
  apply ratio_contracts_weighted N (by omega) x j
  have hr : (j : ℝ) ≤ mode N x hx := by exact_mod_cast hj
  linarith [mode_add_two_le_weighted_sqrt N hN x hx hregion]

theorem right_succ_weighted_decay (N : ℕ) (hN : 40000 ≤ N) (x : ℝ) (hx : 0 < x)
    (hregion : 5 * Real.sqrt N / 2 ≤ x) {j : ℕ} (hj : mode N x hx < j) :
    weight N x (j + 1) ≤ (1 / 200 : ℝ) * weight N x j := by
  have he := weighted_ratio_at_or_before N hN x hx hregion (j := mode N x hx) le_rfl
  have h := (ratio_antitone N x (show mode N x hx + 1 ≤ j by omega)).trans he
  rw [weight_succ]
  apply mul_le_mul_of_nonneg_right _ (weight_pos ..).le
  linarith only [h, ratio_mode_le N x hx]

theorem left_succ_weighted_decay (N : ℕ) (hN : 40000 ≤ N) (x : ℝ) (hx : 0 < x)
    (hregion : 5 * Real.sqrt N / 2 ≤ x) (d : ℕ) (hd : 1 ≤ d) :
    leftAt (weight N x) (mode N x hx) (d + 1) ≤
      (1 / 200 : ℝ) * leftAt (weight N x) (mode N x hx) d := by
  let m := mode N x hx
  by_cases he : d + 1 ≤ m
  · let j := m - (d + 1)
    have hj : j + 1 = m - d := by dsimp [j]; omega
    have hbefore : j + 1 < mode N x hx := by change j + 1 < m; omega
    have he' := weighted_ratio_at_or_before N hN x hx hregion (j := j) (by omega)
    have hr := (one_lt_ratio_before N x hx hbefore).le.trans he'
    change leftAt (weight N x) m (d + 1) ≤ _ * leftAt (weight N x) m d
    rw [leftAt, if_pos he, leftAt, if_pos (by omega : d ≤ m), ← hj]
    change weight N x j ≤ _ * weight N x (j + 1)
    rw [weight_succ, ← mul_assoc]
    exact le_mul_of_one_le_left (weight_pos ..).le hr
  · change leftAt (weight N x) m (d + 1) ≤ _ * leftAt (weight N x) m d
    rw [leftAt, if_neg he]
    exact mul_nonneg (by norm_num) (leftAt_nonneg (fun _ ↦ (weight_pos ..).le) ..)

theorem weighted_neighbors_product (N : ℕ) (hN : 40000 ≤ N) (x : ℝ) (hx : 0 < x)
    (hregion : 5 * Real.sqrt N / 2 ≤ x) :
    let m := mode N x hx
    leftAt (weight N x) m 1 * weight N x (m + 1) ≤ (1 / 200 : ℝ) * weight N x m ^ 2 := by
  dsimp only
  have h := fun j hj ↦ weighted_ratio_at_or_before N hN x hx hregion (j := j) hj
  generalize hm : mode N x hx = m at *
  cases m with
  | zero => simp [leftAt]; positivity
  | succ j =>
    have hr := h j (by omega)
    simp only [leftAt, if_pos (show 1 ≤ j + 1 by omega), Nat.add_one_sub_one]
    rw [weight_succ N x (j + 1), weight_succ N x j]
    nlinarith only [mul_le_mul_of_nonneg_right hr
      (mul_nonneg (ratio_pos N x j).le (sq_nonneg (weight N x j)))]

theorem weighted_neighbors_min_le (N : ℕ) (hN : 40000 ≤ N) (x : ℝ) (hx : 0 < x)
    (hregion : 5 * Real.sqrt N / 2 ≤ x) :
    let m := mode N x hx
    min (leftAt (weight N x) m 1) (weight N x (m + 1)) ≤ weight N x m / 14 := by
  dsimp only
  have hp := weighted_neighbors_product N hN x hx hregion
  dsimp only at hp
  by_contra! bad
  rw [lt_min_iff] at bad
  have hm := weight_pos N x (mode N x hx)
  have h := mul_lt_mul_of_pos_left bad.2 (show 0 < weight N x (mode N x hx) / 14 by positivity)
  have h' := mul_lt_mul_of_pos_right bad.1 (weight_pos N x (mode N x hx + 1))
  nlinarith only [hp, h, h', sq_pos_of_pos hm]

theorem weighted_both_geometric (N : ℕ) (hN : 40000 ≤ N) (x : ℝ) (hx : 0 < x)
    (hregion : 5 * Real.sqrt N / 2 ≤ x) (l : ℕ) :
    let m := mode N x hx
    leftAt (weight N x) m (l + 1) ≤ (1 / 200 : ℝ)^l * weight N x m ∧
      weight N x (m + (l + 1)) ≤ (1 / 200 : ℝ)^l * weight N x m := by
  let m := mode N x hx
  change leftAt (weight N x) m (l + 1) ≤ _ ∧ weight N x (m + (l + 1)) ≤ _
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
    have hl := left_succ_weighted_decay N hN x hx hregion (l + 1) (by omega)
    have hr := right_succ_weighted_decay N hN x hx hregion (j := m + (l + 1))
      (by change m < _; omega)
    constructor
    · exact hl.trans (by rw [pow_succ', mul_assoc]; exact mul_le_mul_of_nonneg_left ih.1 (by norm_num))
    · exact hr.trans (by rw [pow_succ', mul_assoc]; exact mul_le_mul_of_nonneg_left ih.2 (by norm_num))

#print axioms weighted_neighbors_min_le
#print axioms weighted_both_geometric

end LongCycleBounds.Outer
