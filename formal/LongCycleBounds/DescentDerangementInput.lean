import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic

noncomputable section
namespace LongCycleBounds.DescentDerangement
open Finset Polynomial

/-- The signed binomial summand, written with its coefficient reversal in the variable X. -/
def gnAtom : ℕ → ℚ[X]
  | 0 => 1
  | j+1 => C (1 / ((j+1 : ℕ) : ℚ)) * (X * C (j:ℚ) - 1) * gnAtom j

/-- The finite binomial transform of the derangement alphabet input. -/
def gn (n : ℕ) : ℚ[X] := ∑ j ∈ range (n+1), gnAtom j

def gnCoeff (n h : ℕ) : ℝ := ((gn n).coeff (n-h) : ℚ)

theorem gn_succ (j : ℕ) : gn (j+1) = gn j + gnAtom (j+1) := by
  simp [gn, sum_range_succ]

theorem gnAtom_product (j : ℕ) : gnAtom j =
    C (1 / (j.factorial : ℚ)) * ∏ l ∈ range j, (X * C (l:ℚ) - 1) := by
  induction j with
  | zero => simp [gnAtom]
  | succ j ih =>
    rw [gnAtom, ih, prod_range_succ, Nat.factorial_succ, Nat.cast_mul]
    simp only [one_div, mul_inv_rev, map_mul]
    ring

end LongCycleBounds.DescentDerangement
