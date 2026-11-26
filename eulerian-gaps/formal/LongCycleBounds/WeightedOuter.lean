import LongCycleBounds.WeightedDecay
import LongCycleBounds.OuterAlternation

/-! A derivative lower bound for a bounded positive weighting of the lattice sum. -/

noncomputable section

namespace LongCycleBounds.Outer

open Finset

private theorem left_tsum (f : ℕ → ℝ) (m : ℕ) :
    ∑' j : ℕ, leftAt f m (j + 1) = ∑ j ∈ range m, f j := by
  rw [tsum_eq_sum (s := range m) (fun j hj ↦ by
    have h : ¬j + 1 ≤ m := by simpa [mem_range] using hj
    simp [leftAt, h])]
  rw [← sum_range_reflect f m]
  apply sum_congr rfl
  intro j hj
  simp only [mem_range] at hj
  simp [leftAt, show j + 1 ≤ m by omega, show m - (j + 1) = m - 1 - j by omega]

/-- A common absolute majorant controls the entire sum outside the peak and its neighbors. -/
theorem three_point_error (f : ℕ → ℝ) (m : ℕ) (hf : Summable f) {u : ℕ → ℝ} {B : ℝ}
    (hu : HasSum u B) (hl : ∀ j, |leftAt f m (j + 2)| ≤ u j)
    (hr : ∀ j, |f (m + (j + 2))| ≤ u j) :
    |(∑' j, f j) - (f m + leftAt f m 1 + f (m + 1))| ≤ 2 * B := by
  have hleft : Summable (fun j : ℕ ↦ leftAt f m (j + 1)) := by
    apply summable_of_ne_finset_zero (s := range m)
    intro j hj
    simp [leftAt, show ¬j + 1 ≤ m by simpa [mem_range] using hj]
  have hright : Summable (fun j : ℕ ↦ f (j + (m + 1))) :=
    (summable_nat_add_iff (m + 1)).mpr hf
  have hL := hleft.tsum_eq_zero_add
  have hR := hright.tsum_eq_zero_add
  rw [left_tsum] at hL
  have hsplit := hf.sum_add_tsum_nat_add (m + 1)
  rw [sum_range_succ] at hsplit
  have he : (∑' j, f j) - (f m + leftAt f m 1 + f (m + 1)) =
      (∑' j : ℕ, leftAt f m (j + 2)) + (∑' j : ℕ, f (m + (j + 2))) := by
    simp only [zero_add] at hL hR
    simp_rw [show ∀ j : ℕ, j + 1 + (m + 1) = m + (j + 2) from fun j ↦ by omega] at hR
    linarith only [hL, hR, hsplit]
  rw [he]
  have bound (v : ℕ → ℝ) (hv : ∀ j, |v j| ≤ u j) : |∑' j, v j| ≤ B := by
    have hn : ∀ j, ‖v j‖ ≤ u j := by simpa [Real.norm_eq_abs] using hv
    have hs := hu.summable.of_nonneg_of_le (fun j ↦ norm_nonneg (v j)) hn
    rw [← hu.tsum_eq, ← Real.norm_eq_abs]
    exact (norm_tsum_le_tsum_norm hs).trans (hs.tsum_le_tsum hn hu.summable)
  exact (abs_add_le ..).trans (by linarith only [bound _ hl, bound _ hr])

private abbrev delta : ℝ := 1 / 200

private theorem plain_tail (M : ℝ) :
    HasSum (fun j : ℕ ↦ delta^(j + 1) * M) ((1 / 199 : ℝ) * M) := by
  have h := ((hasSum_geometric_of_norm_lt_one
    (by norm_num [Real.norm_eq_abs] : ‖delta‖ < 1)).mul_left delta).mul_right M
  have he (j : ℕ) : delta^(j + 1) * M = delta * delta^j * M := by rw [pow_succ']
  simp_rw [he]
  rw [show (1 / 199 : ℝ) * M = delta * (1 - delta)⁻¹ * M by norm_num [delta]]
  exact h

private theorem linear_tail (M : ℝ) :
    HasSum (fun j : ℕ ↦ ((j : ℝ) + 2) * delta^(j + 1) * M) ((399 / 39601 : ℝ) * M) := by
  have hd : ‖delta‖ < 1 := by norm_num [Real.norm_eq_abs]
  have h := (((hasSum_coe_mul_geometric_of_norm_lt_one hd).add
    ((hasSum_geometric_of_norm_lt_one hd).mul_left 2)).mul_right delta).mul_right M
  have hf : (fun j : ℕ ↦ ((j : ℝ) + 2) * delta^(j + 1) * M) =
      fun j : ℕ ↦ ((j : ℝ) * delta^j + 2 * delta^j) * delta * M := by
    funext j
    rw [pow_succ]
    ring
  rw [hf]
  rw [show (399 / 39601 : ℝ) * M = (delta / (1 - delta)^2 + 2 * (1 - delta)⁻¹) * delta * M by
    norm_num [delta]]
  exact h

private def alternatingSign (j : ℕ) : ℝ := (-1)^j

private theorem alternatingSign_abs (j : ℕ) : |alternatingSign j| = 1 := by
  simp [alternatingSign]

private theorem alternatingSign_succ (j : ℕ) : alternatingSign (j + 1) = -alternatingSign j := by
  simp [alternatingSign, pow_succ]

private theorem left_signed_abs (v : ℕ → ℝ) (hv : ∀ j, 0 ≤ v j) (m d : ℕ) :
    |leftAt (fun j ↦ alternatingSign j * v j) m d| = leftAt v m d := by
  unfold leftAt
  split <;> simp [abs_mul, alternatingSign_abs, abs_of_nonneg (hv _)]

private theorem left_centered_abs (v : ℕ → ℝ) (hv : ∀ j, 0 ≤ v j) (m d : ℕ) :
    |leftAt (fun j ↦ ((j : ℝ)-m) * (alternatingSign j * v j)) m d| = (d : ℝ) * leftAt v m d := by
  unfold leftAt
  split
  · rename_i h
    simp [abs_mul, alternatingSign_abs, abs_of_nonneg (hv _), Nat.cast_sub h, sub_sub_cancel_left]
  · simp

private theorem left_signed_first (v : ℕ → ℝ) (m : ℕ) :
    leftAt (fun j ↦ alternatingSign j * v j) m 1 = -alternatingSign m * leftAt v m 1 := by
  cases m <;> simp [leftAt, alternatingSign_succ]

private theorem left_centered_first (v : ℕ → ℝ) (m : ℕ) :
    leftAt (fun j ↦ ((j : ℝ)-m) * (alternatingSign j * v j)) m 1 =
      alternatingSign m * leftAt v m 1 := by
  cases m <;> simp [leftAt, alternatingSign_succ]

/-- The zero of a signed weighted mass forces a large first moment. `m` is
any proposed center for which the one-neighbor and tail inequalities hold. -/
theorem derivative_of_bounded_tails (v : ℕ → ℝ) (m : ℕ) (M : ℝ)
    (hM : 0 < M) (hv : ∀ j, 0 ≤ v j) (hvm : M ≤ v m)
    (hnear : min (leftAt v m 1) (v (m + 1)) ≤ (13 / 56 : ℝ) * M)
    (hfar : ∀ j : ℕ, leftAt v m (j + 2) ≤ (1 / 200 : ℝ)^(j + 1) * ((13 / 4 : ℝ) * M) ∧
      v (m + (j + 2)) ≤ (1 / 200 : ℝ)^(j + 1) * ((13 / 4 : ℝ) * M))
    (hs : Summable (fun j : ℕ ↦ (-1 : ℝ)^j * v j))
    (hd : Summable (fun j : ℕ ↦ ((j : ℝ) + 1) * ((-1 : ℝ)^j * v j)))
    (hz : (∑' j : ℕ, (-1 : ℝ)^j * v j) = 0) :
    (2 / 5 : ℝ) * M < |∑' j : ℕ, ((j : ℝ) + 1) * ((-1 : ℝ)^j * v j)| := by
  let f (j : ℕ) := alternatingSign j * v j
  let g (j : ℕ) := ((j : ℝ)-m) * f j
  let d (j : ℕ) := ((j : ℝ) + 1) * f j
  let L := leftAt v m 1
  let R := v (m + 1)
  change Summable f at hs
  change Summable d at hd
  change (∑' j, f j) = 0 at hz
  have hgs (j : ℕ) : g j = d j - ((m : ℝ) + 1) * f j := by dsimp [d, g]; ring
  have hsg : Summable g := (hd.sub (hs.mul_left ((m : ℝ) + 1))).congr (fun j ↦ (hgs j).symm)
  have hs0 : (∑' j, g j) = ∑' j, d j := by
    simp_rw [hgs]
    rw [hd.tsum_sub (hs.mul_left ((m : ℝ) + 1)), tsum_mul_left, hz, mul_zero, sub_zero]
  have h1 := three_point_error f m hs (plain_tail ((13 / 4 : ℝ) * M))
    (fun j ↦ (left_signed_abs v hv m (j + 2)).le.trans (hfar j).1) (fun j ↦ by
      simp only [f, abs_mul, alternatingSign_abs, abs_of_nonneg (hv _), one_mul]
      exact (hfar j).2)
  have h2 := three_point_error g m hsg (linear_tail ((13 / 4 : ℝ) * M))
    (fun j ↦ by
      rw [show |leftAt g m (j + 2)| = ((j + 2 : ℕ) : ℝ) * leftAt v m (j + 2) from
        left_centered_abs v hv m (j + 2)]
      push_cast
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (hfar j).1 (by positivity)) (fun j ↦ by
      have he : ((m + (j + 2) : ℕ) : ℝ) - (m : ℝ) = (j : ℝ) + 2 := by push_cast; ring
      simp only [g, f, abs_mul, alternatingSign_abs, one_mul, abs_of_nonneg (hv _), he,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ (j : ℝ) + 2)]
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (hfar j).2 (by positivity))
  have hv1 : f m + leftAt f m 1 + f (m + 1) = alternatingSign m * (v m - L - R) := by
    change alternatingSign m * v m + leftAt (fun j ↦ alternatingSign j * v j) m 1 +
      alternatingSign (m + 1) * R = _
    rw [left_signed_first, alternatingSign_succ]
    dsimp only [L]
    ring
  have hv2 : g m + leftAt g m 1 + g (m + 1) = alternatingSign m * (L - R) := by
    rw [show leftAt g m 1 = alternatingSign m * L from left_centered_first v m]
    dsimp only [g, f, R]
    push_cast
    rw [alternatingSign_succ]
    ring
  rw [hz, hv1, zero_sub, abs_neg, abs_mul, alternatingSign_abs, one_mul] at h1
  rw [hs0, hv2] at h2
  have huh : v m - L - R ≤ 2 * ((1 / 199 : ℝ) * ((13 / 4 : ℝ) * M)) :=
    (le_abs_self _).trans h1
  have hdabs : |L - R| ≤ |∑' j, d j| + |(∑' j, d j) - alternatingSign m * (L - R)| := by
    have ht := abs_sub (∑' j, d j) ((∑' j, d j) - alternatingSign m * (L - R))
    rwa [sub_sub_cancel, abs_mul, alternatingSign_abs, one_mul] at ht
  have hpair : L + R - 2 * min L R ≤ |L - R| := by
    rcases le_total L R with h | h
    · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]; linarith
    · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]; linarith
  change (2 / 5 : ℝ) * M < |∑' j, d j|
  change min L R ≤ _ at hnear
  linarith only [hM, hvm, huh, h2, hdabs, hpair, hnear]

/-- The positive label represented by the zero-based variable `i` is `i+1`. -/
def weightedMoment (N : ℕ) (x : ℝ) (T : ℕ → ℝ) : ℝ :=
  ∑' i : ℕ, (-1 : ℝ)^i * weight N x i * T (i + 1)

theorem summable_weightedMoment (N : ℕ) (x : ℝ) (hx : 0 < x) (T : ℕ → ℝ)
    (hT : ∀ l : ℕ, 1 ≤ l → 1 ≤ T l ∧ T l ≤ 13 / 4) :
    Summable (fun i : ℕ ↦ (-1 : ℝ)^i * weight N x i * T (i + 1)) := by
  apply ((summable_weight N x hx).mul_left (13 / 4 : ℝ)).of_norm_bounded
  intro i
  obtain ⟨ht0, ht1⟩ := hT (i + 1) (by omega)
  simp only [Real.norm_eq_abs, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_nonneg (weight_pos N x i).le, abs_of_nonneg (show 0 ≤ T (i + 1) by linarith)]
  exact (mul_le_mul_of_nonneg_left ht1 (weight_pos N x i).le).trans_eq (mul_comm _ _)

/-- The weighted derivative is bounded below using the peak of the original weight sequence. -/
theorem weighted_derivative_bound (N : ℕ) (hN : 999998 ≤ N) (x : ℝ) (hx : 0 < x)
    (hregion : 5 * Real.sqrt N / 2 ≤ x) (T : ℕ → ℝ)
    (hT : ∀ l : ℕ, 1 ≤ l → 1 ≤ T l ∧ T l ≤ 13 / 4) (hz : weightedMoment N x T = 0) :
    (2 / 5 : ℝ) * weight N x (mode N x hx) < |weightedMoment (N + 1) x T| := by
  let m := mode N x hx
  let w := weight N x
  let M := w m
  let v (i : ℕ) := w i * T (i + 1)
  have hpos (i : ℕ) : 0 ≤ T (i + 1) := (by norm_num : (0 : ℝ) ≤ 1).trans (hT _ (by omega)).1
  have hv (i : ℕ) : 0 ≤ v i := mul_nonneg (weight_pos ..).le (hpos _)
  have hVm : M ≤ v m := le_mul_of_one_le_right (weight_pos ..).le (hT _ (by omega)).1
  have hub (i : ℕ) : v i ≤ (13 / 4 : ℝ) * w i := by
    change w i * T (i + 1) ≤ _
    rw [mul_comm (13 / 4 : ℝ)]
    exact mul_le_mul_of_nonneg_left (hT _ (by omega)).2 (weight_pos ..).le
  have hleft (i : ℕ) : leftAt v m i ≤ (13 / 4 : ℝ) * leftAt w m i := by
    unfold leftAt
    split
    · exact hub _
    · simp
  have hnear0 : min (leftAt w m 1) (w (m + 1)) ≤ M / 14 :=
    weighted_neighbors_min_le N (by omega) x hx hregion
  have hnear : min (leftAt v m 1) (v (m + 1)) ≤ (13 / 56 : ℝ) * M := by
    rcases min_le_iff.mp hnear0 with h | h
    · apply (min_le_left _ _).trans
      linarith only [hleft 1, h]
    · apply (min_le_right _ _).trans
      linarith only [hub (m + 1), h]
  have hfar (j : ℕ) : leftAt v m (j + 2) ≤ delta^(j + 1) * ((13 / 4 : ℝ) * M) ∧
      v (m + (j + 2)) ≤ delta^(j + 1) * ((13 / 4 : ℝ) * M) := by
    have hg := weighted_both_geometric N (by omega) x hx hregion (j + 1)
    dsimp only at hg
    constructor
    · apply (hleft (j + 2)).trans
      linarith only [mul_le_mul_of_nonneg_left hg.1 (by norm_num : (0 : ℝ) ≤ 13 / 4)]
    · apply (hub (m + (j + 2))).trans
      linarith only [mul_le_mul_of_nonneg_left hg.2 (by norm_num : (0 : ℝ) ≤ 13 / 4)]
  have hvalue (i : ℕ) : (-1 : ℝ)^i * weight N x i * T (i + 1) = (-1 : ℝ)^i * v i := by
    dsimp [v, w]
    ring
  have hderiv (i : ℕ) : (-1 : ℝ)^i * weight (N + 1) x i * T (i + 1) =
      ((i : ℝ) + 1) * ((-1 : ℝ)^i * v i) := by
    simp only [v, w, weight, pow_succ ((i : ℝ) + 1)]
    ring
  have hs := (summable_weightedMoment N x hx T hT).congr hvalue
  have hd := (summable_weightedMoment (N + 1) x hx T hT).congr hderiv
  have hzero : (∑' i : ℕ, (-1 : ℝ)^i * v i) = 0 := by
    simpa only [weightedMoment, hvalue] using hz
  have hbound := derivative_of_bounded_tails v m M (weight_pos ..) hv hVm hnear hfar hs hd hzero
  unfold weightedMoment
  simp_rw [hderiv]
  exact hbound

#print axioms three_point_error
#print axioms derivative_of_bounded_tails
#print axioms summable_weightedMoment
#print axioms weighted_derivative_bound

end LongCycleBounds.Outer
