import LongCycleBounds.DescentInverseFiniteHead

noncomputable section
namespace LongCycleBounds.DescentMesh
open Finset Real Polynomial DescentNecklace

private theorem word_cap (k N B T : ℕ) {v c : ℝ} (hv : 0≤v) (cap :
    (∑ z : LogAtom k N B, |atomCoefficient z| * v^(atomLoss z)) ≤ c) :
    (∑ w : LogWord k N B T, |wordCoefficient w| * v^(wordLoss w)) ≤ exp c-1 := by
  classical
  let a := ∑ z : LogAtom k N B, |atomCoefficient z| * v^(atomLoss z)
  have ap : 0≤a := sum_nonneg fun _ _ ↦ by positivity
  have h := Real.sum_le_exp_of_nonneg ap (T+1)
  rw [sum_range_succ',pow_zero,Nat.factorial_zero,Nat.cast_one,div_one] at h
  have eq : (∑ w : LogWord k N B T, |wordCoefficient w| * v^(wordLoss w)) =
      ∑ i ∈ range T, a^(i+1)/((i+1).factorial:ℝ) := by
    rw [Fintype.sum_sigma,←Fin.sum_univ_eq_sum_range]
    apply sum_congr rfl
    intro i _
    rw [←tupleMass_eq (fun z : LogAtom k N B ↦ |atomCoefficient z| * v^(atomLoss z)) (i.val+1)]
    unfold tupleMass
    rw [sum_div]
    apply sum_congr rfl
    intro w _
    simp only [wordCoefficient,wordLoss,abs_div,abs_prod,Nat.abs_cast,prod_mul_distrib,
      prod_pow_eq_pow_sum]
    ring
  change a≤c at cap
  rw [eq]
  linarith only [h,exp_le_exp.mpr cap]

private theorem exp64 {c : ℝ} (h : 0≤c) (hc : c<64) :
    exp c ≤ (1/(1-c/64))^64 := by
  have e := exp_bound_div_one_sub_of_interval (by linarith : 0≤c/64) (by linarith : c/64<1)
  have f := pow_le_pow_left₀ (exp_pos _).le e 64
  rw [←exp_nat_mul] at f
  norm_num only [Nat.cast_ofNat] at f
  rw [show 64*(c/64)=c by ring] at f
  exact f

/-- The strict 4/5 coefficient budget for every genuine row of rank at least 128
and cutoff at least 8. -/
theorem actual_four_fifths_eight {n k : ℕ} (hk : 8≤k) (hn : 128≤n) (kn : k≤n) :
    lossNorm n (fun i ↦ ((profilePolynomial n k).coeff i:ℝ)) (4/5) <
      ((profilePolynomial n k).coeff n:ℝ) := by
  by_cases long : 58≤k
  · exact actual_four_fifths_long long kn
  have small := word_cap k n n n (by norm_num : 0≤(4/5:ℝ)) (InverseHead.atom_small hk n n)
  have big := word_cap k n n n (by norm_num : 0≤(93/100:ℝ)) (InverseHead.atom_large hk n n)
  have e := (exp64 (c:=365/1000) (by norm_num) (by norm_num)).trans
    (show (1/(1-(365/1000:ℝ)/64))^64≤145/100 by norm_num)
  have E := (exp64 (c:=255/100) (by norm_num) (by norm_num)).trans
    (show (1/(1-(255/100:ℝ)/64))^64≤14 by norm_num)
  apply actual_two_mass (m:=45/100) (M:=13) (by omega) kn (by norm_num) (by norm_num : 0<(93/100:ℝ))
    (by norm_num) (by linarith only [small,e]) (by linarith only [big,E])
  norm_num1
  have hk' : (k:ℝ) ≤ 57 := by exact_mod_cast (by omega : k≤57)
  have pw := pow_le_pow_of_le_one (by norm_num : 0≤(80/93:ℝ)) (by norm_num)
    (by omega : 64≤(n+1)/2)
  nlinarith only [mul_le_mul hk' pw (pow_nonneg (by norm_num : 0≤(80/93:ℝ)) _) (by norm_num : (0:ℝ)≤57)]

#print axioms actual_four_fifths_eight
end LongCycleBounds.DescentMesh
