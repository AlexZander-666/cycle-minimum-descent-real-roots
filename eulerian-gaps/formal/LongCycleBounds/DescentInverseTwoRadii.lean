import LongCycleBounds.DescentInverseLongCutoff

/-! Two independent radii for a positive-loss logarithmic expansion. -/
noncomputable section
namespace LongCycleBounds.DescentMesh
open Finset Polynomial Real FixedCycleCount DescentNecklace

theorem expanded_loss_two_mass {n k : ℕ} (hk : 3≤k) (hn : k≤n) (N B T : ℕ)
    {v V : ℝ} (hv : 0≤v) (hV : 0<V) (vr : v≤V) {m M : ℝ}
    (small : (∑ w : LogWord k N B T, |wordCoefficient w| *v^(wordLoss w)) ≤ m)
    (large : (∑ w : LogWord k N B T, |wordCoefficient w| *V^(wordLoss w)) ≤ M) :
    lossNorm n (expandedCoefficient n k N B T) v ≤ allowedFraction n k *
      (2*m + 2*(k:ℝ)*(v/V)^((n+1)/2)*M) := by
  classical
  let u (x : ℝ) (w : LogWord k N B T) := |wordCoefficient w| * x^(wordLoss w)
  let z := (v/V)^((n+1)/2)
  have z0 : 0 ≤ z := pow_nonneg (div_nonneg hv hV.le) _
  let p := allowedFraction n k
  have p0 : 0 ≤ p := allowedFraction_nonneg .. 
  have point (w : LogWord k N B T) (_ : w ∈ univ) :
      (if wordLength w ≤ n then allowedFraction (n-wordLength w) k * u v w else 0) ≤
      2*p*u v w + (2*(k:ℝ)*p*z)*u V w := by
    have v0 : 0 ≤ u v w := mul_nonneg (abs_nonneg _) (pow_nonneg hv _)
    have V0 : 0 ≤ u V w := mul_nonneg (abs_nonneg _) (pow_nonneg hV.le _)
    split_ifs with valid
    · rcases valid.lt_or_eq with sm | fill
      · exact (mul_le_mul_of_nonneg_right (nonempty_residual (by omega) hn (Nat.sub_pos_of_lt sm)) v0).trans
          (le_add_of_nonneg_right (by positivity))
      · have support (a : LogWord k N B T) (mem : a ∈ ({w}:Finset _)) : n ≤ 2*wordLoss a := by
          obtain rfl := mem_singleton.mp mem
          rw [← fill]; exact word_loss hk _
        have h := reweight_empty {w} wordLoss (fun a ↦ |wordCoefficient a|) support hv hV vr
        simp only [sum_singleton,abs_abs] at h
        rw [abs_of_nonneg v0] at h
        rw [fill,Nat.sub_self,allowedFraction_zero,one_mul]
        have hp := mul_le_mul_of_nonneg_right (empty_residual (by omega) hn) (mul_nonneg z0 V0)
        change u v w ≤ z*u V w at h
        dsimp only [p] at *
        nlinarith only [h,hp,mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) p0) v0]
    · positivity
  refine (expanded_loss_le n k N B T hv).trans ((sum_le_sum point).trans ?_)
  rw [sum_add_distrib, ← mul_sum, ← mul_sum]
  have h1 := mul_le_mul_of_nonneg_left small
    (show 0≤2*p by positivity)
  have h2 := mul_le_mul_of_nonneg_left large
    (show 0≤2*(k:ℝ)*p*z by positivity)
  change 2*p*(∑ w, u v w) ≤ _ at h1
  change 2*(k:ℝ)*p*z*(∑ w, u V w) ≤ _ at h2
  change _ ≤ p*(2*m + 2*(k:ℝ)*z*M)
  linarith only [h1,h2]


/-- This implication exhibits both numerical word-mass budgets required of a finite
box in the actual permutation row. Only the filled residual pays the larger radius. -/
theorem actual_two_mass {n k : ℕ} (hk : 3≤k) (hn : k≤n) {v V m M : ℝ}
    (hv : 0≤v) (hV : 0<V) (vr : v≤V)
    (small : (∑ w : LogWord k n n n, |wordCoefficient w| *v^(wordLoss w)) ≤ m)
    (large : (∑ w : LogWord k n n n, |wordCoefficient w| *V^(wordLoss w)) ≤ M)
    (budget : 2*m+2*(k:ℝ)*(v/V)^((n+1)/2)*M<1) :
    lossNorm n (fun i ↦ ((profilePolynomial n k).coeff i : ℝ)) v <
      ((profilePolynomial n k).coeff n : ℝ) := by
  have eq (i : ℕ) : ((profilePolynomial n k).coeff i : ℝ) = expandedCoefficient n k n n n i := by
    have h := congrArg (fun p : ℝ[X] ↦ p.coeff i) (profile_eq_expansion (n:=n) (k:=k) hk (by omega))
    rw [←good_mul_badTaylor_coeff n k n n n i]
    have cast (a : ℚ) : (Rat.castHom ℝ) a = (a:ℝ) := rfl
    simpa only [coeff_map,cast,expansionRow] using h
  simp only [eq,expanded_top hk (by omega : 0<n)]
  exact (expanded_loss_two_mass hk hn n n n hv hV vr small large).trans_lt
    (by simpa using mul_lt_mul_of_pos_left budget (lt_of_lt_of_le
      (by positivity) (Occupancy.allowedFraction_ge_half (by omega : 2≤k) hn)))

#print axioms expanded_loss_two_mass
#print axioms actual_two_mass
end LongCycleBounds.DescentMesh
