import LongCycleBounds.DescentActualCentral

/-! Binary label lower bound supplied by a single long cycle, including reversal. -/
noncomputable section
namespace LongCycleBounds.DescentMesh
open LongCycles Finset Polynomial DescentTwoLetters DescentNecklace ArithmeticFunction
open scoped Moebius

theorem row_coeff_cutoff_mono (n i : ℕ) {k l : ℕ} (hk : k≤l) :
    (row n l).coeff i ≤ (row n k).coeff i := by
  classical
  rw [coeff_row,coeff_row]
  apply sum_le_sum
  intro σ _
  by_cases h : Allowed l σ ∧ descents σ=i
  · have g : Allowed k σ ∧ descents σ=i := ⟨fun x j hj hlt ↦ h.1 x j hj (hlt.trans_le hk),h.2⟩
    rw [if_pos h,if_pos g]
  · rw [if_neg h]
    split <;> norm_num

theorem letters_mono (n q : ℕ) {d e : ℕ→ℤ} (h : ∀ i, d i ≤ e i) :
    letters n q d ≤ letters n q e :=
  sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_right (h i) (by positivity)

theorem single_alphabet {n : ℕ} (hn : 0<n) :
    (n:ℝ[X])*(profilePolynomial n n).map (Rat.castHom ℝ) = rawDivisors n := by
  rw [← alphabet_product_coeff]
  have h := X_pow_dvd_iff.mp (alphabet_product_ode n n) n (Nat.lt_succ_self n)
  rw [coeff_sub,euler_coeff,alphabet_kernel_eq_raw hn,kernel_step hn (le_refl n)] at h
  have recurrence := (sub_eq_zero.mp h).symm
  simpa [necklaceStep,Nat.div_self hn,alphabet_product_zero] using recurrence

private theorem linear_le_pow {m : ℕ} (hm : 6 ≤ m) : 4*m+2 ≤ 2^m := by
  induction m, hm using Nat.le_induction with
  | base => decide
  | succ m hm ih => rw [pow_succ]; omega

private theorem exponential_margin {n : ℕ} (hn : 128≤n) :
    (n:ℝ)*(2:ℝ)^(n/2) ≤ (2:ℝ)^n/2 := by
  have a := linear_le_pow (m:=n/2) (by omega)
  have b : 2*n ≤ 2^(n-n/2) :=
    (show 2*n ≤ 4*(n/2)+2 by omega).trans (a.trans (Nat.pow_le_pow_right (by decide) (by omega)))
  have c : (2:ℝ)*n ≤ (2:ℝ)^(n-n/2) := by exact_mod_cast b
  have d := mul_le_mul_of_nonneg_right c (by positivity : 0≤(2:ℝ)^(n/2))
  rw [← pow_add,show n-n/2+n/2=n by omega] at d
  linarith

theorem binary_raw_error {n : ℕ} (hn : 128≤n) {x : ℝ} (hx : |x|=2) :
    |(rawDivisors n).eval x-x^n| ≤ (2:ℝ)^n/2 := by
  have pos : 0<n := by omega
  let s := n.divisors.erase 1
  have split : (rawDivisors n).eval x-x^n =
      ∑ d ∈ s, ((μ d : ℤ):ℝ)*x^(n/d) := by
    unfold rawDivisors
    rw [eval_finsetSum,← sum_erase_add _ _ (Nat.one_mem_divisors.mpr pos.ne')]
    simp [s,eval_monomial]
  rw [split]
  calc
    _ ≤ ∑ d ∈ s, |((μ d : ℤ):ℝ)*x^(n/d)| := abs_sum_le_sum_abs ..
    _ ≤ ∑ _ ∈ s, (2:ℝ)^(n/2) := by
      apply sum_le_sum
      intro d hd
      have h := mem_erase.mp hd
      have dp := Nat.pos_of_mem_divisors h.2
      have md : |((μ d:ℤ):ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one
      rw [abs_mul,abs_pow,hx]
      exact (mul_le_of_le_one_left (by positivity) md).trans
        (pow_le_pow_right₀ (by norm_num) (Nat.div_le_div_left (by omega) (by omega)))
    _ ≤ (n:ℝ)*2^(n/2) := by
      simp only [sum_const,nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast (card_le_card (erase_subset 1 n.divisors)).trans (Nat.card_divisors_le_self n)) (by positivity)
    _ ≤ _ := exponential_margin hn

theorem profile_at_integer {n : ℕ} (hn : 0 < n) (k : ℕ) (z : ℤ) :
    ((profilePolynomial n k).map (Rat.castHom ℝ)).eval (z:ℝ) =
      (signedLetters n z (row n k).coeff : ℝ) := by
  rw [← alphabet_eq_profile hn]
  have eq := congrArg (Rat.castHom ℝ) (eval_alphabet_int n z (row n k).coeff)
  rw [← eval_map_apply] at eq
  simpa using eq

private theorem binary_single_value {n : ℕ} (hn : 128≤n) (z : ℤ) (s : ℝ)
    (hz : |(z:ℝ)|=2) (hs : |s|=1) (leading : s*(z:ℝ)^n=2^n) :
    (2:ℝ)^n/(2*n) ≤ s*(signedLetters n z (row n n).coeff:ℝ) := by
  have pos : 0 < n := by omega
  have hn' : 0 < (n:ℝ) := by exact_mod_cast pos
  have ev := congrArg (fun f : ℝ[X] ↦ f.eval (z:ℝ)) (single_alphabet pos)
  simp only [eval_mul,eval_natCast,profile_at_integer pos] at ev
  have base := binary_raw_error hn hz
  have err : |s * (rawDivisors n).eval (z:ℝ)-(2:ℝ)^n| ≤ (2:ℝ)^n/2 := by
    rw [← leading,← mul_sub,abs_mul,hs,one_mul,leading]
    exact base
  apply (div_le_iff₀ (by positivity)).mpr
  rw [← ev] at err
  linarith only [(abs_le.mp err).1, show s*((n:ℝ)*(signedLetters n z (row n n).coeff:ℝ)) =
    (s*(signedLetters n z (row n n).coeff:ℝ))*n by ring]

theorem binary_lower_both {n k : ℕ} (hn : 128≤n) (hk : k≤n) :
    (2:ℝ)^n/(2*n) ≤ (letters n 2 (row n k).coeff : ℝ) ∧
    (2:ℝ)^n/(2*n) ≤ (letters n 2 (reverseList n (row n k).coeff) : ℝ) := by
  have a := binary_single_value hn 2 1 (by norm_num) (by norm_num) (by norm_num)
  have b := binary_single_value hn (-2) ((-1)^n) (by norm_num) (by simp)
    (by rw [← mul_pow]; norm_num)
  have z : (-2:ℤ) = -((2:ℕ):ℤ) := by norm_num
  rw [z,signedLetters_neg] at b
  have signSq : (-1:ℝ)^n*(-1)^n=1 := by rw [← mul_pow]; norm_num
  push_cast at b
  rw [← mul_assoc,signSq,one_mul] at b
  have hpos : signedLetters n 2 (row n n).coeff = letters n 2 (row n n).coeff := signedLetters_nat n 2 _
  rw [hpos,one_mul] at a
  have mono := letters_mono n 2 (fun i ↦ row_coeff_cutoff_mono n i hk)
  have monor := letters_mono n 2 (d:=reverseList n (row n n).coeff) (e:=reverseList n (row n k).coeff)
    (fun i ↦ row_coeff_cutoff_mono n _ hk)
  exact ⟨a.trans (by exact_mod_cast mono),b.trans (by exact_mod_cast monor)⟩

#print axioms binary_lower_both
#print axioms single_alphabet
#print axioms binary_raw_error
end LongCycleBounds.DescentMesh
