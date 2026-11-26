import LongCycleBounds.LinearCenteredPoles

namespace LongCycleBounds.OrdinaryEulerianGap
open PoleTails PoleBridge Bulk
noncomputable section

noncomputable def sharpEnvelope (l : ℝ) : ℝ := 16/(13+3*l^2)

theorem sharp_decay (l s p : ℝ) (k : ℕ) (hl : 1 ≤ l) (hp : 8 ≤ p)
    (ha : 3/2 ≤ p*s^2) {q : ℝ} (hk : p*(k:ℝ) ≤ 4*q) :
    (1+(l^2-1)*s^2)^(-(q/2)) ≤ sharpEnvelope l ^ k := by
  have hL : 0 ≤ l^2-1 := by nlinarith [sq_nonneg (l-1)]
  have xy : 0 ≤ (l^2-1)*s^2 := mul_nonneg hL (sq_nonneg _)
  have hx : 1 ≤ 1+(l^2-1)*s^2 := by linarith
  have hpos : 0 ≤ 1+(l^2-1)*s^2 := by linarith
  have bern := one_add_mul_self_le_rpow_one_add (by linarith : -1 ≤ (l^2-1)*s^2)
    (by linarith : 1 ≤ p/8)
  have den : (13+3*l^2)/16 ≤ (1+(l^2-1)*s^2)^(p/8) := by
    apply le_trans _ bern
    nlinarith [mul_nonneg hL (sub_nonneg.mpr ha)]
  have h := one_div_le_one_div_of_le (by positivity : 0 < (13+3*l^2)/16) den
  have single : (1+(l^2-1)*s^2)^(-(p/8)) ≤ sharpEnvelope l := by
    rw [Real.rpow_neg hpos]
    simpa [sharpEnvelope, div_div_eq_mul_div, one_div_div] using h
  have hh := pow_le_pow_left₀ (Real.rpow_nonneg hpos _) single k
  rw [← Real.rpow_natCast, ← Real.rpow_mul hpos] at hh
  exact (Real.rpow_le_rpow_of_exponent_le hx (by linarith)).trans hh

private theorem sharp_step (j : ℝ) (hj : 0 ≤ j) :
    (2*j+5)*sharpEnvelope (2*j+5)^4 ≤ (1/50)/(j+1) - (1/50)/(j+2) := by
  have h₁ : 0 < j+1 := by positivity
  have h₂ : 0 < j+2 := by positivity
  have h₃ : 0 < 13+3*(2*j+5)^2 := by positivity
  unfold sharpEnvelope
  field_simp
  rw [← sub_nonneg]
  ring_nf
  positivity

private theorem sharp_sum (n : ℕ) :
    ∑ i ∈ Finset.range n, (2*(i:ℝ)+5)*sharpEnvelope (2*i+5)^4 ≤ 1/50 := by
  have strong (m : ℕ) : ∑ i ∈ Finset.range m, (2*(i:ℝ)+5)*sharpEnvelope (2*i+5)^4 ≤
      1/50 - (1/50)/((m:ℝ)+1) := by
    induction m with
    | zero => norm_num
    | succ m ih =>
      rw [Finset.sum_range_succ]
      push_cast
      rw [show (m:ℝ)+1+1=m+2 by ring]
      linarith [sharp_step (m:ℝ) (by positivity)]
  exact (strong n).trans (sub_le_self _ (by positivity))

private def remainder (f : ℝ → ℂ) := f 3 + ∑' i : ℕ, f (2*(i:ℝ)+5)

private theorem remainder_bound {B : ℝ} (hB : 0 < B) (f : ℝ → ℂ)
    (hf : ∀ l ≥ 3, ‖f l‖ ≤ l*sharpEnvelope l^4*B) :
    Summable (fun i : ℕ ↦ f (2*(i:ℝ)+5)) ∧ ‖remainder f‖ < B/10 := by
  let l (i : ℕ) := 2*(i:ℝ)+5
  let M (i : ℕ) := l i * sharpEnvelope (l i)^4
  have hl (i : ℕ) : 3 ≤ l i := by dsimp [l]; linarith [show (0:ℝ) ≤ i by positivity]
  have hm (i : ℕ) : 0 ≤ M i := mul_nonneg (by linarith [hl i]) (by positivity)
  have hsum (n : ℕ) : ∑ i ∈ Finset.range n, M i ≤ 1/50 := sharp_sum n
  have sm := summable_of_sum_range_le hm hsum
  have tm := Real.tsum_le_of_sum_range_le hm hsum
  have cp (i : ℕ) : ‖f (l i)‖ ≤ M i*B := hf _ (hl i)
  have hs := Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) cp (sm.mul_right B)
  refine ⟨hs.of_norm, ?_⟩
  have hh := (norm_tsum_le_tsum_norm hs).trans (Summable.tsum_le_tsum cp hs (sm.mul_right B))
  rw [tsum_mul_right] at hh
  have h3 := hf 3 le_rfl
  norm_num [sharpEnvelope] at h3
  change ‖f 3 + ∑' i, f (l i)‖ < _
  linarith [norm_add_le (f 3) (∑' i, f (l i)),mul_le_mul_of_nonneg_right tm hB.le]

/-- Near a zero of the full preceding row the leading pole controls the centered step. -/
theorem central_pole_gap (c s : ℝ) (p : ℕ) (hu : c^2+s^2=1) (hs : 0 < s)
    (hp : 8 ≤ (p:ℝ)) (ha : 3/2 ≤ (p:ℝ)*s^2) (small : |(total c s p).re| ≤ 1/8) :
    22/25*s < |(total c s (p+1)).re-c*(total c s p).re| := by
  let z := pole c s
  let F (l : ℝ) := z l^p
  let D (l : ℝ) := F l*(z l-(c:ℂ))
  have normF (l : ℝ) (hl : 1 ≤ l) : ‖F l‖ ≤ sharpEnvelope l^4 := by
    change ‖pole c s l^p‖ ≤ _
    rw [norm_pole_pow _ _ _ hu hl]
    exact sharp_decay _ _ _ _ hl hp ha (by push_cast; linarith)
  obtain ⟨sf,bf⟩ := remainder_bound (by norm_num : (0:ℝ)<1/3) F (by
    intro l hl
    have h := mul_nonneg (sub_nonneg.mpr hl) (show 0 ≤ sharpEnvelope l^4 by positivity)
    exact (normF _ (by linarith)).trans (by linarith))
  obtain ⟨sd,bd⟩ := remainder_bound hs D (by
    intro l hl
    obtain hl' : 1 ≤ l := by linarith
    change ‖F l*(z l-(c:ℂ))‖ ≤ _
    rw [norm_mul]
    calc _ ≤ sharpEnvelope l^4*(l*s) := mul_le_mul (normF _ hl')
              (norm_centered _ _ _ hu hl' hs.le) (norm_nonneg _) (by positivity)
         _ = _ := by ring)
  have decomp : total c s (p+1) - (c:ℂ)*total c s p = D 1 + remainder D := by
    have addterm : (∑' i : ℕ, z (2*(i:ℝ)+5)^(p+1)) =
        (c:ℂ)*(∑' i : ℕ, F (2*(i:ℝ)+5)) + ∑' i : ℕ, D (2*(i:ℝ)+5) := by
      rw [← tsum_mul_left, ← (sf.mul_left (c:ℂ)).tsum_add sd]
      apply tsum_congr
      intro i
      dsimp only [D,F]
      ring
    change z 1^(p+1)+(z 3^(p+1)+∑' i : ℕ, z (2*(i:ℝ)+5)^(p+1)) -
      (c:ℂ)*(F 1+(F 3+∑' i : ℕ, F (2*(i:ℝ)+5))) = D 1 + (D 3+_)
    rw [addterm]
    dsimp only [D,F]
    ring
  have first : z 1 = ⟨c,-s⟩ := by apply Complex.ext <;> simp [z,pole]
  have norm1 : ‖F 1‖ = 1 := by
    have h := norm_pole_sq c s 1 hu (by norm_num)
    norm_num at h
    rcases h with h|h
    · simp [F,z,h]
    · linarith [norm_nonneg (pole c s 1)]
  have realSmall : |(F 1).re| < 1/6 := by
    change |(F 1).re+(remainder F).re| ≤ 1/8 at small
    have t := abs_sub ((F 1).re+(remainder F).re) (remainder F).re
    rw [add_sub_cancel_right] at t
    linarith [(Complex.abs_re_le_norm _).trans_lt bf]
  have imLarge : 49/50 < |(F 1).im| := by
    have sq := Complex.sq_norm (F 1)
    rw [norm1,Complex.normSq_apply] at sq
    by_contra! h
    have r := mul_self_le_mul_self (abs_nonneg _) realSmall.le
    have i := mul_self_le_mul_self (abs_nonneg _) h
    rw [← abs_mul,abs_of_nonneg (mul_self_nonneg _)] at r i
    nlinarith
  have dre : (D 1).re = (F 1).im*s := by simp [D,first,Complex.mul_re]
  have eq := congrArg Complex.re decomp
  simp only [Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,
    sub_zero,Complex.add_re,dre] at eq
  have t := abs_sub ((F 1).im*s+(remainder D).re) (remainder D).re
  rw [add_sub_cancel_right,abs_mul,abs_of_pos hs] at t
  rw [eq]
  linarith [mul_lt_mul_of_pos_right imLarge hs,(Complex.abs_re_le_norm _).trans_lt bd]

#print axioms central_pole_gap

end
end LongCycleBounds.OrdinaryEulerianGap
