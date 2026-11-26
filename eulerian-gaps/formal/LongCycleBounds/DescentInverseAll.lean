import LongCycleBounds.DescentCollectedBudget

noncomputable section
namespace LongCycleBounds.DescentMesh
open Finset Real Polynomial FixedCycleCount DescentNecklace
open Collected

private theorem exp_upper_64 {c : ℝ} (h : 0 ≤ c) (hc : c<64) :
    exp c ≤ (1/(1-c/64))^64 := by
  have e := exp_bound_div_one_sub_of_interval (by linarith : 0 ≤ c/64) (by linarith : c/64<1)
  have f := pow_le_pow_left₀ (exp_pos _).le e 64
  rw [←exp_nat_mul] at f
  norm_num only [Nat.cast_ofNat] at f
  rwa [show 64*(c/64)=c by ring] at f

private theorem original_leading {k n : ℕ} (hk : 3 ≤ k) (hn : 1 ≤ n) :
    ((profilePolynomial n k).coeff n : ℝ) = allowedFraction n k := by
  have h := congrArg (fun p : ℝ[X] ↦ p.coeff n) (profile_eq_expansion (n:=n) (k:=k) hk hn)
  rw [←expanded_top hk (by omega : 0<n) n n n,←good_mul_badTaylor_coeff n k n n n n]
  have cast (a : ℚ) : (Rat.castHom ℝ) a = (a:ℝ) := rfl
  simpa only [coeff_map,cast,expansionRow] using h

private theorem short_four_fifths {n k : ℕ} (hk : 3 ≤ k) (ku : k ≤ 7) (hn : 128 ≤ n) :
    lossNorm n (fun i ↦ ((profilePolynomial n k).coeff i:ℝ)) (4/5) <
        ((profilePolynomial n k).coeff n:ℝ) := by
  classical
  let p := allowedFraction n k
  let z := (80/93:ℝ)^55
  let u (v : ℝ) (w : Word k n) := |WC w| * v^(WS w)
  have hp : 0<p := lt_of_lt_of_le (by positivity) (Occupancy.allowedFraction_ge_half (by omega) (by omega))
  have hz : 0 ≤ z := by positivity
  have kr : (k:ℝ) ≤ 7 := by exact_mod_cast ku
  have point (w : Word k n) :
      (if WL w ≤ n then allowedFraction (n-WL w) k*u (4/5) w else 0) ≤
        (201/200*p)*u (4/5) w + (14*p*z)*u (93/100) w := by
    have a : 0 ≤ u (4/5) w := mul_nonneg (abs_nonneg _) (by positivity)
    have b : 0 ≤ u (93/100) w := mul_nonneg (abs_nonneg _) (by positivity)
    split_ifs with valid
    · by_cases large : 20 ≤ n-WL w
      · exact (mul_le_mul_of_nonneg_right (ResidualWindow.residual_ratio hk ku (by omega) large) a).trans
          (le_add_of_nonneg_right (by positivity))
      · have half := word_half w
        have size : 55 ≤ WS w := by omega
        have small := pow_le_pow_of_le_one (by norm_num : 0 ≤ (80/93:ℝ)) (by norm_num) size
        have exact_scale : u (4/5) w = (80/93:ℝ)^(WS w)*u (93/100) w := by
          unfold u
          rw [mul_left_comm,←mul_pow]
          norm_num
        have ratio : u (4/5) w ≤ z*u (93/100) w := exact_scale.le.trans (mul_le_mul_of_nonneg_right small b)
        have unit : allowedFraction (n-WL w) k ≤ 1 := by
          by_cases zero : n-WL w=0
          · simp [zero,allowedFraction_zero]
          exact (allowedFraction_le (by omega) (Nat.pos_of_ne_zero zero)).trans
            ((div_le_one (by positivity)).mpr (by exact_mod_cast (by omega : 1 ≤ k)))
        have ep := empty_residual (n:=n) (k:=k) (by omega) (by omega)
        have cap : allowedFraction (n-WL w) k ≤ 14*p := unit.trans (ep.trans (by
          change (2*(k:ℝ))*p ≤ 14*p
          exact mul_le_mul_of_nonneg_right (by linarith) hp.le))
        have prod := mul_le_mul cap ratio a (by positivity : 0 ≤ 14*p)
        exact prod.trans (by nlinarith only [mul_nonneg (by positivity : 0 ≤ 201/200*p) a])
    · positivity
  have eq (i : ℕ) : ((profilePolynomial n k).coeff i:ℝ) = rowCoeff n k i := coeff_actual hk (by omega) _
  rw [original_leading hk (by omega : 1≤n)]
  simp_rw [eq]
  apply (loss_bound n k (by norm_num : 0≤(4/5:ℝ))).trans_lt
  change (∑ w : Word k n, if WL w ≤ n then allowedFraction (n-WL w) k*u (4/5) w else 0) < p
  apply (sum_le_sum (fun w _ ↦ point w)).trans_lt
  rw [sum_add_distrib,←mul_sum,←mul_sum]
  obtain ⟨sm,lg⟩ := word_cost hk ku n
  have c1 : (SignedBounds.cSmall k:ℝ) ≤ 672/1000 := by interval_cases k <;> norm_num [SignedBounds.cSmall]
  have c2 : (SignedBounds.cLarge k:ℝ) ≤ 1573/1000 := by interval_cases k <;> norm_num [SignedBounds.cLarge]
  have E1 := (exp_le_exp.mpr c1).trans ((exp_upper_64 (by norm_num) (by norm_num)).trans
    (by norm_num : (1/(1-(672/1000:ℝ)/64))^64 ≤ 197/100))
  have E2 := (exp_le_exp.mpr c2).trans ((exp_upper_64 (by norm_num) (by norm_num)).trans
    (by norm_num : (1/(1-(1573/1000:ℝ)/64))^64 ≤ 5))
  have A : (∑ w : Word k n,u (4/5) w) ≤ 97/100 := by dsimp only [u]; linarith only [sm,E1]
  have B : (∑ w : Word k n,u (93/100) w) ≤ 4 := by dsimp only [u]; linarith only [lg,E2]
  apply (add_le_add (mul_le_mul_of_nonneg_left A (by positivity))
    (mul_le_mul_of_nonneg_left B (by positivity))).trans_lt
  have fixed : 201/200*(97/100:ℝ)+14*z*4 < 1 := by norm_num [z]
  nlinarith only [mul_lt_mul_of_pos_right fixed hp]

/-- Genuine ordinary-descent inverse-alphabet coefficient dominance at radius 4/5,
uniformly in the original hard cutoff in every rank n≥128. -/
theorem actual_four_fifths_all {n k : ℕ} (hk : 3 ≤ k) (kn : k ≤ n) (hn : 128 ≤ n) :
    lossNorm n (fun i ↦ ((profilePolynomial n k).coeff i:ℝ)) (4/5) <
      ((profilePolynomial n k).coeff n:ℝ) := by
  by_cases cut : 8 ≤ k
  · exact actual_four_fifths_eight cut hn kn
  · exact short_four_fifths hk (by omega) hn

#print axioms actual_four_fifths_all
end LongCycleBounds.DescentMesh
