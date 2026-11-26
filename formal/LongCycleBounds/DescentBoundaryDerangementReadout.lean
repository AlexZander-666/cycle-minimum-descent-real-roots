import LongCycleBounds.DescentBoundaryDerangementProfile
import LongCycleBounds.DescentDerangementInput
import LongCycleBounds.DescentActualReciprocal

noncomputable section
namespace LongCycleBounds.DescentDerangement
open Finset Polynomial DescentNecklace DescentMesh DescentTwoLetters

theorem gn_degree (n : ℕ) : (gn n).natDegree ≤ n := by
  have atom (j : ℕ) : (gnAtom j).natDegree ≤ j := by
    induction j with
    | zero => simp [gnAtom]
    | succ j ih =>
      let u := (X : ℚ[X])*C (j:ℚ)-1
      have small : u.natDegree ≤ 1 := le_trans (natDegree_sub_le ..)
        (max_le ((natDegree_mul_C_le ..).trans (by simp)) (by simp))
      rw [gnAtom]
      apply (natDegree_mul_le ..).trans
      change (C _ * u).natDegree + (gnAtom j).natDegree ≤ j+1
      have z := (natDegree_C_mul_le (1/((j+1:ℕ):ℚ)) u).trans small
      omega
  exact natDegree_sum_le_of_forall_le _ _ (fun j hj ↦
    (atom j).trans (Nat.le_of_lt_succ (mem_range.mp hj)))

theorem original_profile_two {n : ℕ} (hn : 0<n) : profilePolynomial n 2 = reflect n (gn n) := by
  apply profile_two_eq_reflected hn gnAtom rfl _ (gn_degree n)
  intro j
  simp only [gnAtom,Nat.cast_add,Nat.cast_one]

theorem actual_two_readout {n : ℕ} (hn : 0<n) :
    (row n 2).map (Int.castRingHom ℝ) = descentTransform n (gnCoeff n) := by
  rw [original_eq_descentTransform hn,original_profile_two hn]
  unfold descentTransform
  apply sum_congr rfl
  intro h hh
  simp only [coeff_reflect,revAt_le (mem_Icc.mp hh).2,gnCoeff]

theorem actual_two_reciprocal {n : ℕ} (hn : 0<n) {t : ℝ} (ht : t ≠ 0) :
    t^(n-1)*((row n 2).map (Int.castRingHom ℝ)).eval t⁻¹ =
    (descentTransform n (reflectedCoefficients n (gnCoeff n))).eval t := by
  rw [actual_two_readout hn,transform_reflect _ _ ht]

#print axioms original_profile_two
#print axioms actual_two_readout
#print axioms actual_two_reciprocal
end LongCycleBounds.DescentDerangement
