import LongCycleBounds.DescentFiveMultiplicity

/-! The repeated-root exception and all its nonzero nonnegative mixtures. -/
noncomputable section
namespace LongCycleBounds.DescentTwoLetters
open Polynomial Finset

theorem five_mixture_roots (w : ℕ → ℝ) (nonneg : ∀ k ∈ Icc 3 5, 0≤w k)
    (positive : ∃ k ∈ Icc 3 5, 0<w k) :
    let p := ∑ k ∈ Icc 3 5, C (w k)*(row 5 k).map (Int.castRingHom ℝ)
    p = C (6*∑ k ∈ Icc 3 5,w k) * (X*(X-C (-1))^2) ∧
    p.Splits ∧ p.roots = ({0}:Multiset ℝ)+2 • ({-1}:Multiset ℝ) := by
  classical
  dsimp only
  have positiveSum : 0 < ∑ k ∈ Icc 3 5,w k := sum_pos' nonneg positive
  have eq : (∑ k ∈ Icc 3 5,C (w k)*(row 5 k).map (Int.castRingHom ℝ)) =
      C (6*∑ k ∈ Icc 3 5,w k)*(X*(X-C (-1))^2) := by
    rw [mul_sum,map_sum,sum_mul]
    apply sum_congr rfl
    intro k hk
    rw [row_five (mem_Icc.mp hk).1 (mem_Icc.mp hk).2]
    simp [C_ofNat]
    ring
  rw [eq]
  refine ⟨rfl, (Splits.C _).mul (Splits.X.mul ((Splits.X_sub_C (-1:ℝ)).pow 2)),?_⟩
  have nz : (X:ℝ[X])*(X-C (-1))^2≠0 :=
    mul_ne_zero X_ne_zero (pow_ne_zero _ (X_sub_C_ne_zero _))
  rw [roots_C_mul _ (by positivity),roots_mul nz,roots_X,roots_pow,roots_X_sub_C]

#print axioms five_mixture_roots
end LongCycleBounds.DescentTwoLetters
