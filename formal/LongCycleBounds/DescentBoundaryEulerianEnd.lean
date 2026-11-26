import LongCycleBounds.DescentBoundaryUnrestricted
import LongCycleBounds.DescentMeshColor
import LongCycleBounds.DescentGridRoots

noncomputable section
namespace LongCycleBounds.DescentNecklace
open Finset Polynomial DescentTwoLetters DescentMesh Real LongCycles Outer

theorem unrestricted_row {n : ℕ} (hn : 0 < n) :
    (row n 1).map (Int.castRingHom ℝ) = eulerian n := by
  rw [original_eq_descentTransform hn,unrestricted_profile]
  unfold descentTransform
  rw [sum_eq_single_of_mem n (mem_Icc.mpr ⟨hn,le_rfl⟩)]
  · simp
  · intro j _ neq
    simp [coeff_X_pow,neq]

private theorem unrestricted_adjacent {n i : ℕ} (hn : 128 ≤ n) (hi : 2 ≤ i) {θ : ℝ}
    (ht : 0<θ) (top : θ<π/2) (phase : ((n:ℝ)+1)*θ=(i:ℝ)*π)
    (small : 4*(i:ℝ)^2 ≤ (n:ℝ)+1) :
    let x := π*cos θ/sin θ
    weight n x (i-1-1) ≤ (1/4)*weight n x (i-1) ∧
    weight n x (i-1+1) ≤ (1/4)*weight n x (i-1) := by
  let x := π*cos θ/sin θ
  have imp (j m : ℕ) {c : ℝ} (bd : c ≤ 1/4) (h : weight n x j ≤ c*weight n x m) :
      weight n x j ≤ (1/4)*weight n x m :=
    h.trans (mul_le_mul_of_nonneg_right bd (weight_pos ..).le)
  by_cases two : i=2
  · subst i
    obtain ⟨l,r⟩ := two_adjacent hn ht top phase small
    have sm := beta_small hn
    have nr : (128:ℝ) ≤ n := by exact_mod_cast hn
    have bd : exp (1/2-(n:ℝ)/12) ≤ 1/4 := by
      nlinarith only [sm,mul_le_mul_of_nonneg_right nr (exp_pos (1/2-(n:ℝ)/12)).le]
    exact ⟨imp _ _ bd l,imp _ _ bd r⟩
  by_cases three : i=3
  · subst i
    obtain ⟨l,r⟩ := three_adjacent hn ht top phase small
    exact ⟨imp _ _ (by norm_num) l,imp _ _ (by norm_num) r⟩
  obtain ⟨l,r⟩ := regular_adjacent hn (by omega : 4 ≤ i) ht top phase small
  exact ⟨imp _ _ (by norm_num) l,r⟩

theorem unrestricted_end_sign {n i : ℕ} (hn : 128 ≤ n) (hi : 2 ≤ i) {θ : ℝ}
    (ht : 0<θ) (top : θ<π/2) (phase : ((n:ℝ)+1)*θ=(i:ℝ)*π)
    (small : 4*(i:ℝ)^2 ≤ (n:ℝ)+1) :
    (-1:ℝ)^i*((row n 1).map (Int.castRingHom ℝ)).eval (-exp (-(π*cos θ/sin θ))) < 0 := by
  let x := π*cos θ/sin θ
  let a (h : ℕ) : ℝ := ((X^n : ℚ[X]).coeff h : ℝ)
  have np : 1 ≤ n := by omega
  have g (q : ℕ) : colorEval n a q = (q:ℝ)^n := by
    unfold colorEval
    rw [sum_eq_single_of_mem n (mem_Icc.mpr ⟨np,le_rfl⟩)]
    · simp [a]
    · intro j _ neq
      simp [a,coeff_X_pow,neq]
  have rat (j : ℕ) : labelRatio n (colorEval n a) 1 j = 1 := by
    simp [labelRatio,g, show ((j:ℝ)+1)^n ≠ 0 by positivity]
  obtain ⟨l,r⟩ := unrestricted_adjacent hn hi ht top phase small
  have dom := signed_end_of_dominance (m:=i-1) (n:=n) (by omega) x (fun _ ↦ (1:ℝ))
    (l:=1/4) (r:=1/4) (A:=1) (E:=0) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) l r (by simp) (by norm_num)
  have sig : 0 < (-1:ℝ)^(i-1)*labelSeries (colorEval n a) x := by
    rw [normalized_label_series n _ (show (0:ℝ)<1 by norm_num)]
    simpa only [rat,one_mul] using dom
  have xp : 0 < x := div_pos (mul_pos pi_pos (cos_pos_of_mem_Ioo ⟨by linarith [pi_pos],top⟩))
    (sin_pos_of_pos_of_lt_pi ht (by linarith [pi_pos]))
  rw [labelSeries_transform n a xp,mul_left_comm] at sig
  have fac : 0 < exp (-x)/(1+exp (-x))^(n+1) := by positivity
  have z := (mul_pos_iff_of_pos_left fac).mp sig
  have flip : (-1:ℝ)^i = -((-1:ℝ)^(i-1)) := by
    conv_lhs => rw [← Nat.sub_add_cancel (show 1≤ i by omega),pow_succ]
    ring
  rw [original_eq_descentTransform (by omega),unrestricted_profile,flip,neg_mul]
  exact neg_lt_zero.mpr z

#print axioms unrestricted_row
#print axioms unrestricted_end_sign
end LongCycleBounds.DescentNecklace
