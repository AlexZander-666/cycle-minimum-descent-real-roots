import LongCycleBounds.DescentBoundaryEndDominance

noncomputable section
namespace LongCycleBounds.DescentMesh
open Finset Real Outer
theorem end_sign_allowing_one_label {n i : ℕ} (h128 : 128 ≤ n) (hi : 2 ≤ i) {θ p : ℝ}
    (ht : 0<θ) (top : θ<π/2) (phase : ((n:ℝ)+1)*θ=(i:ℝ)*π)
    (small : 4*(i:ℝ)^2 ≤ (n:ℝ)+1) (hp : 0<p) (g : ℕ→ℝ)
    (raw : ∀ j, 0 ≤ g (j+1) ∧ g (j+1) ≤ ((j:ℝ)+1)^n)
    (twoL : 1/(2*(n:ℝ)) ≤ labelRatio n g 1 1) (zeroU : labelRatio n g p 0 ≤ 3)
    (capU : ∀ j, 1 ≤ j → labelRatio n g p j ≤ 4/3)
    (threeL : 2/3 ≤ labelRatio n g p 2)
    (regular : ∀ j, 3 ≤ j → 6/7 ≤ labelRatio n g p j ∧ labelRatio n g p j ≤ 8/7) :
    0 < (-1:ℝ)^(i-1)*labelSeries g (π*cos θ/sin θ) := by
  let x := π*cos θ/sin θ
  have rs {P : ℝ} (hP : 0<P) (j : ℕ) : 0 ≤ labelRatio n g P j :=
    div_nonneg (raw j).1 (by positivity)
  have reduce {P : ℝ} (hP : 0<P)
      (h : 0 < (-1:ℝ)^(i-1)*∑' j, (-1:ℝ)^j*labelRatio n g P j*weight n x j) :
      0 < (-1:ℝ)^(i-1)*labelSeries g x := by
    rw [normalized_label_series n g hP x]
    simpa [mul_left_comm] using mul_pos hP h
  have caps (j : ℕ) : |labelRatio n g p j| ≤ (4/3)+(if j=0 then 5/3 else 0) := by
    rw [abs_of_nonneg (rs hp _)]
    by_cases z : j=0
    · subst j; norm_num; linarith only [zeroU]
    · rw [if_neg z, add_zero]
      exact capU j (by omega)
  have nr : (128:ℝ) ≤ n := by exact_mod_cast h128
  by_cases i2 : i=2
  · subst i
    apply reduce (P:=1) (by norm_num)
    let beta := exp (1/2-(n:ℝ)/12)
    have be0 : 0 ≤ beta := (exp_pos _).le
    have smallB : 8*(n:ℝ)*beta<1 := beta_small h128
    have bh : beta<1/2 := by
      have := mul_le_mul_of_nonneg_right nr be0
      nlinarith
    have adj := two_adjacent h128 ht top phase small
    apply signed_end_of_dominance (m:=1) (l:=beta) (r:=beta) (A:=1) (E:=0)
      (by decide) x _ be0 (by linarith) be0 (by linarith) (by norm_num) (by norm_num) adj.1 adj.2
    · intro j
      simp only [abs_of_nonneg (rs (by norm_num : (0:ℝ)<1) j),ite_self,add_zero]
      unfold labelRatio
      rw [one_mul]
      exact (div_le_one (by positivity)).mpr (raw j).2
    · apply lt_of_lt_of_le _ twoL
      simp only [one_mul,zero_mul,add_zero]
      have D : beta/(1-beta) ≤ 2*beta := (div_le_iff₀ (by linarith)).mpr (by nlinarith)
      apply (lt_div_iff₀ (by positivity)).mpr
      nlinarith only [smallB,mul_le_mul_of_nonneg_right D (show 0≤(n:ℝ) by positivity)]
  by_cases i3 : i=3
  · subst i
    apply reduce hp
    have adj := three_adjacent h128 ht top phase small
    apply signed_end_of_dominance (m:=2) (l:=1/100) (r:=1/100) (A:=3) (E:=0)
      (by decide) x _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) adj.1 adj.2
    · intro j
      have := caps j
      split_ifs at * <;> linarith
    · apply lt_of_lt_of_le _ threeL
      norm_num
  · have i4 : 4 ≤ i := by omega
    apply reduce hp
    have adj := regular_adjacent h128 i4 ht top phase small
    apply single_exception_dominance (m:=i-1) (l:=1/5) (r:=1/4) (A:=4/3) (E:=5/3)
      (by omega) 0 (by omega) x _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) adj.1 adj.2 caps
    apply lt_of_lt_of_le _ (regular (i-1) (by omega)).1
    have s := pow_le_pow_of_le_one (by norm_num : 0≤(1/5:ℝ)) (by norm_num : (1/5:ℝ)≤1)
      (show 3 ≤ i-1-0 by omega)
    norm_num at s ⊢
    linarith


#print axioms end_sign_allowing_one_label
end LongCycleBounds.DescentMesh
