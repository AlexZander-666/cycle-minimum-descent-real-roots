import LongCycleBounds.DescentTwoLetters
import Mathlib.RingTheory.Binomial

/-! Negative alphabet evaluation of the genuine binomial specialization for descent counts. -/

noncomputable section
namespace LongCycleBounds.DescentTwoLetters
open Finset

/-- Generalized binomial specialization, with integral alphabet argument. -/
def signedLetters (n : ℕ) (q : ℤ) (d : ℕ → ℤ) : ℤ :=
  ∑ i ∈ range n, d i * Ring.choose (q+n-1-i) n

theorem signedLetters_nat (n q : ℕ) (d : ℕ → ℤ) : signedLetters n q d = letters n q d := by
  unfold signedLetters letters
  apply sum_congr rfl
  intro i hi
  have hin := mem_range.mp hi
  have cast : (q:ℤ)+n-1-i = ((q+n-1-i:ℕ):ℤ) := by omega
  rw [cast,Ring.choose_natCast]

theorem signedLetters_neg (n q : ℕ) (d : ℕ → ℤ) :
    signedLetters n (-(q:ℤ)) d = (-1:ℤ)^n * letters n q (reverseList n d) := by
  unfold signedLetters letters reverseList
  rw [mul_sum]
  conv_rhs => rw [← Finset.sum_range_reflect]
  apply sum_congr rfl
  intro i hi
  have hin := mem_range.mp hi
  have ix : n-1-(n-1-i)=i := by omega
  have ix' : q+n-1-(n-1-i)=q+i := by omega
  rw [ix, ix', show -(q:ℤ)+n-1-i = -((q:ℤ)-n+1+i) by ring, Ring.choose_neg]
  rw [show ((q:ℤ)-n+1+i)+n-1 = ((q+i:ℕ):ℤ) by push_cast; ring, Ring.choose_natCast]
  change d i * ((Int.negOnePow n : ℤ) * _) = _
  rw [Int.coe_negOnePow_natCast]
  ring

/-- Signed alphabet evaluation recovers the complementary specialization at every natural q. -/
theorem signed_difference (n q : ℕ) (d : ℕ → ℤ) :
    (-1:ℤ)^n*signedLetters n (-(q:ℤ)) d - signedLetters n q d = defect n q d := by
  rw [signedLetters_neg, ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul,
    signedLetters_nat]
  rfl

/-- The two-letter signed-alphabet difference equals the two extreme coefficients of the actual
permutation row when k≥3. -/
theorem signed_two_extremes (m : ℕ) {k : ℕ} (hk : 3 ≤ k) :
    let d := (row (m+2) k).coeff
    (-1:ℤ)^(m+2)*signedLetters (m+2) (-2) d - signedLetters (m+2) 2 d = d m - d 1 :=
  (signed_difference (m+2) 2 _).trans (row_extreme_difference m hk).2

/-- At cutoff two, the same signed alphabet formula retains the n+1 reversing-word correction
exactly when n is even. -/
theorem signed_two_cutoff_two (m : ℕ) :
    let d := (row (m+2) 2).coeff
    (-1:ℤ)^(m+2)*signedLetters (m+2) (-2) d - signedLetters (m+2) 2 d =
      (if Even (m+2) then ((m+3:ℕ):ℤ) else 0) + d m - d 1 :=
  (signed_difference (m+2) 2 _).trans (row_extreme_difference_two m).2

#print axioms signedLetters_neg
#print axioms signed_difference
#print axioms signed_two_extremes
#print axioms signed_two_cutoff_two

end LongCycleBounds.DescentTwoLetters
