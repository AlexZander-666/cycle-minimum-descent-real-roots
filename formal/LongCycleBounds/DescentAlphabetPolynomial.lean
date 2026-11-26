import LongCycleBounds.DescentNumeratorTransform
import LongCycleBounds.DescentSignedSpecialization

/-! The two rational alphabet polynomials agree identically, including at negative arguments. -/
noncomputable section
namespace LongCycleBounds.DescentNecklace
open Polynomial Finset DescentTwoLetters LongCycleBounds.Necklace
open scoped ArithmeticFunction.Moebius

def alphabetPolynomial (n : ℕ) (d : ℕ → ℤ) : ℚ[X] :=
  ∑ i ∈ range n, C (d i : ℚ) * Ring.choose (X + (n:ℚ[X]) - 1 - (i:ℚ[X])) n

theorem eval_alphabet_int (n : ℕ) (q : ℤ) (d : ℕ → ℤ) :
    (alphabetPolynomial n d).eval (q : ℚ) = (signedLetters n q d : ℚ) := by
  unfold alphabetPolynomial signedLetters
  push_cast
  rw [eval_finsetSum]
  apply sum_congr rfl
  intro i _
  rw [eval_mul,eval_C]
  congr 1
  change (evalRingHom (q : ℚ)) (Ring.choose _ _) = (Int.castRingHom ℚ) (Ring.choose _ _)
  rw [Ring.map_choose,Ring.map_choose]
  simp

def mobiusPolynomial (j : ℕ) : ℚ[X] :=
  C ((j:ℚ)⁻¹) * ∑ d ∈ j.divisors, C (μ d : ℚ) * X^(j/d)

theorem eval_mobiusPolynomial {j : ℕ} (hj : 0 < j) (q : ℕ) :
    (mobiusPolynomial j).eval (q:ℚ) = (Fintype.card (PrimitiveNecklace j q) : ℚ) := by
  simp only [mobiusPolynomial,eval_mul,eval_C,eval_finsetSum,eval_pow,eval_X]
  have h : (j:ℚ) * (Fintype.card (PrimitiveNecklace j q) : ℚ) =
      ∑ d ∈ j.divisors, (μ d : ℚ)*(q:ℚ)^(j/d) := by
    exact_mod_cast card_primitiveNecklace_mul hj q
  rw [← h,← mul_assoc,inv_mul_cancel₀ (by exact_mod_cast hj.ne'),one_mul]

def profilePolynomial (n k : ℕ) : ℚ[X] :=
  ∑ p : PositiveLengthProfile n k, ∏ i : Fin n,
    Ring.multichoose (mobiusPolynomial (i.val+1)) (p.val i).val

theorem eval_multichoose_nat (q b : ℕ) :
    Ring.multichoose (q:ℚ) b = (Nat.multichoose q b : ℚ) := by
  cases b with
  | zero => simp
  | succ b =>
    rw [Ring.multichoose_eq, Nat.multichoose_eq]
    have cast : (q:ℚ) + (b+1:ℕ) - 1 = ((q+(b+1)-1 : ℕ) : ℚ) := by
      push_cast
      simp
      ring
    rw [cast,Ring.choose_natCast]

theorem eval_profile_nat (n k q : ℕ) :
    (profilePolynomial n k).eval (q:ℚ) = (Nat.card (NecklaceContent n q k) : ℚ) := by
  rw [card_necklaceContent_eq_positive_sum]
  push_cast
  unfold profilePolynomial
  rw [eval_finsetSum]
  apply sum_congr rfl
  intro p _
  rw [eval_prod]
  apply prod_congr rfl
  intro i _
  change (evalRingHom (q:ℚ)) (Ring.multichoose _ _) = _
  rw [Ring.map_multichoose]
  change Ring.multichoose ((mobiusPolynomial (i.val+1)).eval (q:ℚ)) _ = _
  rw [eval_mobiusPolynomial (Nat.succ_pos _),eval_multichoose_nat]

theorem alphabet_eq_profile {n : ℕ} (hn : 0 < n) (k : ℕ) :
    alphabetPolynomial n (row n k).coeff = profilePolynomial n k := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.infinite_range_of_injective (Nat.cast_injective (R := ℚ))).mono
  rintro _ ⟨q,rfl⟩
  change (alphabetPolynomial n (row n k).coeff).eval (q:ℚ) = _
  have eq := eval_alphabet_int n (q:ℤ) (row n k).coeff
  rw [signedLetters_nat,letters_eq_necklace_content hn] at eq
  simpa only [Int.cast_natCast,eval_profile_nat] using eq

theorem profile_negative {n : ℕ} (hn : 0 < n) (k q : ℕ) :
    (profilePolynomial n k).eval (-(q:ℚ)) =
      ((-1:ℚ)^n) * (letters n q (reverseList n (row n k).coeff) : ℚ) := by
  rw [← alphabet_eq_profile hn]
  have h := eval_alphabet_int n (-(q:ℤ)) (row n k).coeff
  rw [signedLetters_neg] at h
  exact_mod_cast h

theorem alphabet_zero {n : ℕ} (hn : 0 < n) (d : ℕ → ℤ) :
    (alphabetPolynomial n d).coeff 0 = 0 := by
  rw [coeff_zero_eq_eval_zero]
  have h := eval_alphabet_int n (0:ℤ) d
  have z : letters n 0 d = 0 := by
    apply sum_eq_zero
    intro i _
    have less : 0+n-1-i < n := by omega
    rw [Nat.choose_eq_zero_of_lt less, Nat.cast_zero, mul_zero]
  simpa only [Int.cast_zero,show signedLetters n 0 d = 0 from (signedLetters_nat n 0 d).trans z] using h

private def fallingProduct (b : ℚ) (n : ℕ) : ℚ[X] :=
  ∏ j ∈ range n, (X + C (b-j))

private theorem choose_as_product (b : ℚ) (n : ℕ) :
    Ring.choose (X+C b : ℚ[X]) n = C ((n.factorial : ℚ)⁻¹) * fallingProduct b n := by
  have prod (h : ℕ) : (descPochhammer ℤ h).smeval (X+C b : ℚ[X]) = fallingProduct b h := by
    induction h with
    | zero => simp [fallingProduct]
    | succ h ih =>
      rw [descPochhammer_succ_right,smeval_mul,ih]
      simp [fallingProduct,prod_range_succ,smeval_X,smeval_natCast,sub_eq_add_neg,add_assoc]
  have h := Ring.descPochhammer_eq_factorial_smul_choose (X+C b : ℚ[X]) n
  rw [prod,nsmul_eq_mul] at h
  rw [h,← mul_assoc,← C_eq_natCast,← C_mul,inv_mul_cancel₀ (by exact_mod_cast n.factorial_ne_zero),C_1,one_mul]

private theorem degree_falling (b : ℚ) (n : ℕ) : (fallingProduct b n).natDegree = n := by
  rw [fallingProduct,natDegree_prod_of_monic _ _ (fun i _ ↦ monic_X_add_C _)]
  simp only [natDegree_X_add_C, sum_const, card_range, smul_eq_mul, mul_one]

private theorem leading_falling (b : ℚ) (n : ℕ) : (fallingProduct b n).coeff n = 1 := by
  have monic : (fallingProduct b n).Monic := monic_prod_of_monic _ _ (fun i _ ↦ monic_X_add_C _)
  simpa only [degree_falling] using monic.coeff_natDegree

private theorem shift_offset (n i : ℕ) :
    (X+(n:ℚ[X])-1-(i:ℚ[X])) = X + C ((n:ℚ)-1-i) := by simp; ring

theorem alphabet_degree (n : ℕ) (d : ℕ → ℤ) : (alphabetPolynomial n d).natDegree ≤ n := by
  apply natDegree_sum_le_of_forall_le
  intro i _
  rw [shift_offset,choose_as_product]
  exact (natDegree_C_mul_le _ _).trans ((natDegree_C_mul_le _ _).trans_eq (degree_falling _ _))

theorem alphabet_top (n : ℕ) (d : ℕ → ℤ) :
    (alphabetPolynomial n d).coeff n = ((∑ i ∈ range n, d i : ℤ) : ℚ) / n.factorial := by
  simp only [alphabetPolynomial,finsetSum_coeff,shift_offset,choose_as_product,coeff_C_mul,
    leading_falling,mul_one,Int.cast_sum,div_eq_mul_inv,sum_mul]

#print axioms alphabet_top
#print axioms alphabet_eq_profile
end LongCycleBounds.DescentNecklace
