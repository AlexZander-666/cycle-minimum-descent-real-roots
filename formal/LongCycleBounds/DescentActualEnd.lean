import LongCycleBounds.DescentActualColors

/-! Both end half-mesh signs for the actual one-line descent enumerator, at every
size at least 128 and every admissible long-cycle cutoff. -/
noncomputable section
namespace LongCycleBounds.DescentMesh
open Finset Real Polynomial FixedCycleCount DescentTwoLetters

private theorem actual_end_aux {n k i : ℕ} (hk : 3≤k) (kn : k≤n) (hn : 128≤n) (hi : 2 ≤ i)
    {θ : ℝ} (ht : 0<θ) (top : θ<π/2) (phase : ((n:ℝ)+1)*θ=(i:ℝ)*π)
    (small : 4*(i:ℝ)^2 ≤ (n:ℝ)+1) (a : ℕ→ℝ) (leading : a n=allowedFraction n k)
    (mass : ∀ v, lossNorm n a v=lossNorm n (rowAlphabet n k) v)
    (one : colorEval n a 1=0) (two : (2:ℝ)^n/(2*n) ≤ colorEval n a 2) :
    (-1:ℝ)^i*(descentTransform n a).eval (-exp (-(π*cos θ/sin θ))) < 0 := by
  let p := allowedFraction n k
  let g := colorEval n a
  have kp : 0<(k:ℝ) := by exact_mod_cast (by omega : 0<k)
  have np : 0<(n:ℝ) := by exact_mod_cast (by omega : 0<n)
  have pp : 0<p := lt_of_lt_of_le (by positivity) (Occupancy.allowedFraction_ge_half (by omega : 2≤k) kn)
  have p3 : 3*p≤1 := by
    have k3 : (3:ℝ)≤k := by exact_mod_cast hk
    have b := (allowedFraction_le (by omega : 2≤k) (by omega : 0<n)).trans
      (one_div_le_one_div_of_le (by norm_num : (0:ℝ)<3) k3)
    dsimp [p]; linarith only [b]
  have bound {v K : ℝ} (hv : 0≤v) (half : v≤1/2)
      (budget : 2*(exp (badEnvelope v)-1)+1/1000 < K) : lossNorm n a v ≤ K*p := by
    rw [mass]
    exact (expanded_small hk kn hn n n n hv half budget).le
  have reg (j : ℕ) (hj : 3≤ j) : 6/7 ≤ labelRatio n g p j ∧ labelRatio n g p j ≤ 8/7 := by
    have jr : (3:ℝ) ≤ j := by exact_mod_cast hj
    have h := ratio_window (by omega : 1≤n) a pp leading
      (one_div_le_one_div_of_le (by norm_num : (0:ℝ)<4) (by linarith : (4:ℝ)≤ j+1))
      (bound (by norm_num) (by norm_num) envelope_table.1)
    norm_num at h
    exact h
  have th : 2/3 ≤ labelRatio n g p 2 ∧ labelRatio n g p 2 ≤ 4/3 := by
    have h := ratio_window (j:=2) (by omega : 1≤n) a pp leading
      (by norm_num : (1:ℝ)/((2:ℕ)+1)≤1/3) (bound (by norm_num) (by norm_num) envelope_table.2.1)
    norm_num at h; exact h
  have tu : labelRatio n g p 1 ≤ 3 := by
    have h := ratio_window (j:=1) (by omega : 1≤n) a pp leading
      (by norm_num : (1:ℝ)/((1:ℕ)+1)≤1/2) (bound (by norm_num) (by norm_num) envelope_table.2.2.2)
    linarith only [h.2]
  have tl : 1/(2*(n:ℝ)) ≤ labelRatio n g 1 1 := by
    simp only [labelRatio,Nat.cast_one,one_mul,show (1:ℝ)+1=2 by norm_num]
    rw [le_div_iff₀ (by positivity)]
    calc
      _ = (2:ℝ)^n/(2*n) := by ring
      _ ≤ _ := two
  have raw (j : ℕ) : 0 ≤ g (j+1) ∧ g (j+1) ≤ ((j:ℝ)+1)^n := by
    have win : 0 ≤ labelRatio n g p j ∧ labelRatio n g p j ≤ 3 := by
      by_cases x : j=0
      · subst j; simp [g,labelRatio,one]
      by_cases y : j=1
      · subst j
        exact ⟨div_nonneg ((by positivity : 0 ≤ (2:ℝ)^n/(2*n)).trans two) (by positivity),tu⟩
      by_cases z : j=2
      · subst j; constructor <;> linarith only [th.1,th.2]
      obtain ⟨l,r⟩ := reg j (by omega)
      constructor <;> linarith
    have denom : 0<p*((j:ℝ)+1)^n := by positivity
    have lb : 0 ≤ g (j+1) := by
      by_contra! ng
      exact (not_lt_of_ge win.1) (div_neg_of_neg_of_pos ng denom)
    have ub := (div_le_iff₀ denom).mp win.2
    refine ⟨lb,ub.trans ?_⟩
    have h := mul_le_mul_of_nonneg_right p3 (show 0≤((j:ℝ)+1)^n by positivity)
    linarith only [h]
  have sig := end_sign_of_label_bounds hn hi ht top phase small pp g one raw tl tu th reg
  have xp : 0 < π*cos θ/sin θ := div_pos (mul_pos pi_pos (cos_pos_of_mem_Ioo ⟨by linarith [pi_pos],top⟩))
    (sin_pos_of_pos_of_lt_pi ht (by linarith [pi_pos]))
  change 0<(-1:ℝ)^(i-1)*labelSeries (colorEval n a) _ at sig
  rw [labelSeries_transform n a xp] at sig
  let x := π*cos θ/sin θ
  have pos : 0 < exp (-x)/(1+exp (-x))^(n+1) := by positivity
  have swap : 0 < exp (-x)/(1+exp (-x))^(n+1) * ((-1:ℝ)^(i-1)*(descentTransform n a).eval (-exp (-x))) := by
    rw [mul_left_comm]
    exact sig
  have hsigned := (mul_pos_iff_of_pos_left pos).mp swap
  have signflip : (-1:ℝ)^i = -((-1:ℝ)^(i-1)) := by
    conv_lhs => rw [← Nat.sub_add_cancel (show 1≤ i by omega),pow_succ]
    ring
  rw [signflip,neg_mul]
  exact neg_lt_zero.mpr hsigned

theorem end_sign_actual {n k i : ℕ} (hk : 3≤k) (kn : k≤n) (hn : 128≤n) (hi : 2 ≤ i)
    {θ : ℝ} (ht : 0<θ) (top : θ<π/2) (phase : ((n:ℝ)+1)*θ=(i:ℝ)*π)
    (small : 4*(i:ℝ)^2 ≤ (n:ℝ)+1) :
    (-1:ℝ)^i*((row n k).map (Int.castRingHom ℝ)).eval (-exp (-(π*cos θ/sin θ))) < 0 := by
  rw [actual_expanded_readout hk (by omega)]
  have inputs := first_two_colors hk kn hn
  exact actual_end_aux hk kn hn hi ht top phase small _ (expanded_top hk (by omega) n n n)
    (fun _ ↦ rfl) inputs.1 inputs.2.2.1

theorem end_sign_actual_reciprocal {n k i : ℕ} (hk : 3≤k) (kn : k≤n) (hn : 128≤n) (hi : 2 ≤ i)
    {θ : ℝ} (ht : 0<θ) (top : θ<π/2) (phase : ((n:ℝ)+1)*θ=(i:ℝ)*π)
    (small : 4*(i:ℝ)^2 ≤ (n:ℝ)+1) :
    let t := -exp (-(π*cos θ/sin θ))
    (-1:ℝ)^i*(t^(n-1)*((row n k).map (Int.castRingHom ℝ)).eval t⁻¹) < 0 := by
  dsimp only
  rw [actual_expanded_readout hk (by omega),transform_reflect _ _ (neg_ne_zero.mpr (exp_ne_zero _))]
  have inputs := first_two_colors hk kn hn
  exact actual_end_aux hk kn hn hi ht top phase small _
    (by simp only [reflectedCoefficients,Nat.sub_self,pow_zero,one_mul,expanded_top hk (by omega : 0<n) n n n])
    (fun v ↦ reflected_lossNorm n _ v) inputs.2.1 inputs.2.2.2

#print axioms end_sign_actual
#print axioms end_sign_actual_reciprocal
end LongCycleBounds.DescentMesh
