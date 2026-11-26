import LongCycleBounds.DescentMeshColor
import LongCycleBounds.DescentTwoLetterLower

/-! Both scalar color readouts from the original labeled permutations, including
the one-letter vanishing and the two-letter lower bound at either end. -/
noncomputable section
namespace LongCycleBounds.DescentMesh
open Finset Polynomial DescentTwoLetters DescentNecklace FixedCycleCount

abbrev rowAlphabet (n k : ℕ) := expandedCoefficient n k n n n

private theorem signed_sum_actual {n k : ℕ} (hk : 3≤k) (hn : 0<n) (z : ℤ) :
    (signedLetters n z (row n k).coeff:ℝ) =
      ∑ h ∈ Icc 1 n, rowAlphabet n k h*(z:ℝ)^h := by
  let P := (profilePolynomial n k).map (Rat.castHom ℝ)
  have delta (h : ℕ) : P.coeff h = rowAlphabet n k h := by
    rw [show P = expansionRow k n n by exact profile_eq_expansion hk hn]
    exact good_mul_badTaylor_coeff n k n n n h
  have deg : P.natDegree ≤ n := by
    unfold P
    rw [← alphabet_eq_profile hn]
    exact (natDegree_map_le ..).trans (alphabet_degree ..)
  have z0 : P.coeff 0=0 := by
    simp [P,← alphabet_eq_profile hn,coeff_map,alphabet_zero hn]
  rw [← profile_at_integer hn k z]
  change P.eval _ = _
  rw [eval_eq_sum_range' (Nat.lt_succ_of_le deg)]
  simp_rw [← delta]
  symm
  apply sum_subset
  · intro h hh; exact mem_range.mpr (Nat.lt_succ_of_le (mem_Icc.mp hh).2)
  · intro h hh outside
    have h0 : h=0 := by have h' := mem_range.mp hh; simp only [mem_Icc,not_and] at outside; omega
    simp [h0,z0]

theorem true_colors {n k : ℕ} (hk : 3≤k) (hn : 0<n) (q : ℕ) :
    colorEval n (rowAlphabet n k) q = (letters n q (row n k).coeff:ℝ) ∧
    colorEval n (reflectedCoefficients n (rowAlphabet n k)) q =
      (letters n q (reverseList n (row n k).coeff):ℝ) := by
  have a := signed_sum_actual hk hn (q:ℤ)
  rw [signedLetters_nat] at a
  refine ⟨by simpa [colorEval] using a.symm,?_⟩
  have b := signed_sum_actual hk hn (-(q:ℤ))
  rw [signedLetters_neg] at b
  push_cast at b
  have b' := congrArg (fun x : ℝ ↦ (-1:ℝ)^n*x) b
  have s2 (r : ℕ) : (-1:ℝ)^r * (-1)^r = 1 := by rw [← mul_pow]; norm_num
  rw [← mul_assoc,s2,one_mul,mul_sum] at b'
  rw [b']
  unfold colorEval
  apply sum_congr rfl
  intro h hh
  have dec : (-1:ℝ)^n = (-1)^(n-h)*(-1)^h := by
    rw [← pow_add,Nat.sub_add_cancel (mem_Icc.mp hh).2]
  rw [dec,reflectedCoefficients,neg_eq_neg_one_mul (q:ℝ),mul_pow]
  linear_combination -((-1:ℝ)^(n-h)*rowAlphabet n k h*(q:ℝ)^h)*(s2 h)

private theorem letters_one {n : ℕ} (hn : 0<n) (a : ℕ→ℤ) : letters n 1 a = a 0 := by
  unfold letters
  rw [sum_eq_single 0]
  · simp
  · intro h _ h0
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp
  · simp [hn]

theorem first_two_colors {n k : ℕ} (hk : 3≤k) (kn : k≤n) (hn : 128≤n) :
    let a := rowAlphabet n k
    let r := reflectedCoefficients n a
    colorEval n a 1=0 ∧ colorEval n r 1=0 ∧
    (2:ℝ)^n/(2*n) ≤ colorEval n a 2 ∧ (2:ℝ)^n/(2*n) ≤ colorEval n r 2 := by
  have hpos : 0<n := by omega
  obtain ⟨one,onerev⟩ := true_colors hk hpos 1
  obtain ⟨two,tworev⟩ := true_colors hk hpos 2
  dsimp only
  rw [one,onerev,two,tworev,letters_one hpos,letters_one hpos]
  have z : (row n k).coeff 0=0 := by
    simpa [show n-1+1=n by omega] using constant_zero (n-1) (by omega : 2≤k)
  have top : (row n k).coeff (n-1)=0 := by
    simpa [show n-1+1=n by omega] using top_zero (n-1) hk
  simpa only [reverseList,Nat.sub_zero,z,top,Int.cast_zero,true_and] using
    (show True ∧ True ∧ _ from ⟨trivial,trivial,binary_lower_both hn kn⟩)

#print axioms true_colors
#print axioms first_two_colors
end LongCycleBounds.DescentMesh
