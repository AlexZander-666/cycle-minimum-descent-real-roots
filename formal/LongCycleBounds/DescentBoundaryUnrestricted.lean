import LongCycleBounds.DescentEulerianReadout
import LongCycleBounds.DescentMeshTransform

noncomputable section
namespace LongCycleBounds.DescentNecklace
open Finset Polynomial DescentTwoLetters DescentMesh Real

theorem unrestricted_necklaces (n q : ℕ) : Nat.card (NecklaceContent n q 1) = q^n := by
  let e : AllowedCompatible n q 1 ≃ Compatible n q :=
    { toFun := Subtype.val
      invFun := fun x ↦ ⟨x, fun _ j hj hj' ↦ by omega⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  rw [← Nat.card_congr (originalNecklaceEquiv n q 1), Nat.card_congr e,
    ← Nat.card_congr (wordEquiv n q)]
  simp

theorem unrestricted_profile (n : ℕ) : profilePolynomial n 1 = X^n := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.infinite_range_of_injective (Nat.cast_injective (R := ℚ))).mono
  rintro _ ⟨q,rfl⟩
  change (profilePolynomial n 1).eval (q:ℚ) = _
  simp [eval_profile_nat, unrestricted_necklaces]

theorem unrestricted_central_sign {n i : ℕ} (hn : 128 ≤ n) {θ : ℝ}
    (lo : π/(2*sqrt ((n:ℝ)+1)) ≤ θ) (top : θ ≤ π/2)
    (phase : ((n:ℝ)+1)*θ=(i:ℝ)*π) :
    (-1:ℝ)^i*((row n 1).map (Int.castRingHom ℝ)).eval (-exp (-(π*cos θ/sin θ))) < 0 := by
  rw [original_eq_descentTransform (by omega),unrestricted_profile]
  have z : ∀ h ∈ Ico 1 n, ((X^n : ℚ[X]).coeff h : ℝ) = 0 := by
    intro h hh
    simp [coeff_X_pow, ne_of_lt (mem_Ico.mp hh).2]
  apply central_sign_of_budgets hn lo top phase
  · simp
  · rw [sum_eq_zero (fun h hh ↦ by rw [z h hh, abs_zero, zero_mul])]
    norm_num
  · rw [sum_eq_zero (fun h hh ↦ by simp only [z h hh, abs_zero, zero_mul, ite_self])]
    simp
#print axioms unrestricted_profile
#print axioms unrestricted_central_sign
end LongCycleBounds.DescentNecklace
