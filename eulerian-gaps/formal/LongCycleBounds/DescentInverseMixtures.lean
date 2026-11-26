import LongCycleBounds.DescentInverseAll

noncomputable section
namespace LongCycleBounds.DescentMesh
open Finset DescentNecklace

/-- Subadditivity with arbitrary nonnegative scalar coefficients, at every
nonnegative loss-weight radius. -/
theorem lossNorm_positive_sum {ι : Type*} (S : Finset ι) (weights : ι→ℝ) (a : ι→ℕ→ℝ)
    (n : ℕ) {r : ℝ} (hr : 0 ≤ r) (pos : ∀ i∈S, 0 ≤ weights i) :
    lossNorm n (fun j ↦ ∑ i∈S,weights i*a i j) r ≤ ∑ i∈S, weights i*lossNorm n (a i) r := by
  unfold lossNorm
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_le_sum
  intro j _
  apply (mul_le_mul_of_nonneg_right (abs_sum_le_sum_abs _ _) (pow_nonneg hr _)).trans
  rw [sum_mul]
  exact sum_le_sum fun i hi ↦ by rw [abs_mul,abs_of_nonneg (pos i hi),mul_assoc]

/-- Fixed-rank nonzero positive mixtures of actual inverse-alphabet inputs
inherit the same strict radius-4/5 coefficient inequality. -/
theorem actual_four_fifths_mix {n : ℕ} (hn : 128 ≤ n) (S : Finset ℕ)
    (valid : ∀ k∈S,3 ≤ k ∧ k ≤ n) (w : ℕ→ℝ)
    (nonneg : ∀ k∈S,0 ≤ w k) (positive : ∃ k∈S,0 < w k) :
    lossNorm n (fun i ↦ ∑ k∈S,w k*((profilePolynomial n k).coeff i:ℝ)) (4/5) <
       ∑ k∈S,w k*((profilePolynomial n k).coeff n:ℝ) := by
  let a := fun k i ↦ ((profilePolynomial n k).coeff i:ℝ)
  apply (lossNorm_positive_sum S w a n (by norm_num) nonneg).trans_lt
  have each (k : ℕ) (h : k∈S) : lossNorm n (a k) (4/5)<a k n :=
    actual_four_fifths_all (valid k h).1 (valid k h).2 hn
  apply sum_lt_sum (fun k hk ↦ mul_le_mul_of_nonneg_left (each k hk).le (nonneg k hk))
  obtain ⟨k,hk,pos⟩ := positive
  exact ⟨k,hk,mul_lt_mul_of_pos_left (each k hk) pos⟩

#print axioms actual_four_fifths_mix
end LongCycleBounds.DescentMesh
