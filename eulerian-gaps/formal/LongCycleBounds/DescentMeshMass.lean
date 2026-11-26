import LongCycleBounds.OccupancyPositiveFloor

/-! Isolate the empty residual permutation in a majorized necklace convolution. -/

namespace LongCycleBounds.DescentMesh
open Finset FixedCycleCount

/-- Nonempty residual permutations have at most twice the full allowed probability. -/
theorem nonempty_residual {k n m : ℕ} (hk : 2 ≤ k) (hn : k ≤ n) (hm : 0 < m) :
    allowedFraction m k ≤ 2 * allowedFraction n k := by
  have kp : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have lo := Occupancy.allowedFraction_ge_half hk hn
  calc
    _ ≤ 1 / (k : ℝ) := allowedFraction_le hk hm
    _ = 2 * (1 / (2 * (k : ℝ))) := by field_simp
    _ ≤ _ := by linarith

/-- The empty residual has weight one; its cost is at most twice the cutoff after scaling. -/
theorem empty_residual {k n : ℕ} (hk : 2 ≤ k) (hn : k ≤ n) :
    1 ≤ (2 * k : ℝ) * allowedFraction n k := by
  have kp : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have h := (div_le_iff₀ (show 0 < 2 * (k : ℝ) by positivity)).mp
    (Occupancy.allowedFraction_ge_half hk hn)
  linarith [mul_comm (allowedFraction n k) (2 * (k : ℝ))]

/-- In the actual admissible-permutation convolution only the last term pays the factor k. -/
theorem residual_convolution {k n : ℕ} (hk : 2 ≤ k) (hn : k ≤ n)
    (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) :
    ∑ j ∈ range (n + 1), allowedFraction (n - j) k * b j ≤
      allowedFraction n k * (2 * ∑ j ∈ range n, b j + (2 * k : ℝ) * b n) := by
  rw [sum_range_succ, Nat.sub_self, allowedFraction_zero, one_mul]
  have hsum : ∑ j ∈ range n, allowedFraction (n - j) k * b j ≤
      (2 * allowedFraction n k) * ∑ j ∈ range n, b j := by
    rw [mul_sum]
    exact sum_le_sum fun j hj ↦ mul_le_mul_of_nonneg_right
      (nonempty_residual hk hn (Nat.sub_pos_of_lt (mem_range.mp hj))) (hb j)
  have hlast := mul_le_mul_of_nonneg_right (empty_residual hk hn) (hb n)
  linarith only [hsum, hlast, mul_comm (allowedFraction n k) (2 * (k : ℝ))]

#print axioms residual_convolution

end LongCycleBounds.DescentMesh
