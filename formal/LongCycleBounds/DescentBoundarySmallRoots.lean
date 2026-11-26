import LongCycleBounds.DescentBoundaryWindows
import Mathlib.Tactic.ComputeDegree

/-! Strict and repeated root cases for the four- and five-letter weighted rows. -/
noncomputable section
namespace LongCycleBounds.DescentBoundary
open Finset Polynomial DescentTwoLetters

theorem mixture_coeff_nonneg (n : ℕ) (w : ℕ → ℝ) (hw : ∀ k ∈ Icc 1 n, 0 ≤ w k)
    (i : ℕ) : 0 ≤ (mixture n w).coeff i := by
  rw [mixture, finsetSum_coeff]
  apply sum_nonneg
  intro k hk
  rw [coeff_C_mul, realRow, coeff_map]
  apply mul_nonneg (hw k hk)
  have count : 0 ≤ (row n k).coeff i := by
    rw [coeff_row]
    exact sum_nonneg fun _ _ ↦ by split <;> norm_num
  change 0 ≤ ((row n k).coeff i : ℝ)
  exact_mod_cast count

theorem four_simple (w : ℕ → ℝ) (hw : ∀ k ∈ Icc 1 4, 0 ≤ w k)
    (regular : 0 < w 1 + (w 3 + w 4)) :
    (mixture 4 w).Splits ∧ (mixture 4 w).roots.Nodup ∧ ∀ x ∈ (mixture 4 w).roots, x ≤ 0 := by
  have a := hw 1 (by decide)
  have b := hw 2 (by decide)
  have c := hw 3 (by decide)
  have e := hw 4 (by decide)
  have pos : 0 < (mixture 4 w).eval (-2) := by
    norm_num [four_mixture]; linarith
  have neg : (mixture 4 w).eval (-(1/2:ℝ)) < 0 := by
    norm_num [four_mixture]; linarith
  have origin : 0 ≤ (mixture 4 w).eval 0 := by simpa [four_mixture] using a
  let lower : Fin 2 → ℝ := ![-2, -(1/2)]
  let upper : Fin 2 → ℝ := ![-(1/2), 0]
  apply simple_nonpositive_from_leading_window lower upper (first := 0)
  · intro i; fin_cases i <;> norm_num [lower, upper]
  · intro i; fin_cases i <;> norm_num [upper]
  · intro i j h; fin_cases i <;> fin_cases j <;> norm_num [lower, upper] at *
  · intro i; fin_cases i
    · exact pos.ne'
    · exact neg.ne
  · intro i; fin_cases i
    · exact (mul_neg_of_pos_of_neg pos neg).le
    · exact mul_nonpos_of_nonpos_of_nonneg neg.le origin
  · intro i; fin_cases i <;> norm_num [lower]
  · norm_num [lower]; exact pos
  · rw [four_mixture]
    compute_degree
  · exact mixture_coeff_nonneg _ w hw _

theorem five_simple (w : ℕ → ℝ) (hw : ∀ k ∈ Icc 1 5, 0 ≤ w k)
    (regular : 0 < w 1 + w 2) :
    (mixture 5 w).Splits ∧ (mixture 5 w).roots.Nodup ∧ ∀ x ∈ (mixture 5 w).roots, x ≤ 0 := by
  have a := hw 1 (by decide)
  have b := hw 2 (by decide)
  have c := hw 3 (by decide)
  have e := hw 4 (by decide)
  have f := hw 5 (by decide)
  have negL : (mixture 5 w).eval (-4) < 0 := by
    norm_num [five_mixture]; linarith
  have pos : 0 < (mixture 5 w).eval (-1) := by
    norm_num [five_mixture]; linarith
  have negR : (mixture 5 w).eval (-(1/4:ℝ)) < 0 := by
    norm_num [five_mixture]; linarith
  have origin : 0 ≤ (mixture 5 w).eval 0 := by simpa [five_mixture] using a
  let lower : Fin 3 → ℝ := ![-4,-1,-(1/4)]
  let upper : Fin 3 → ℝ := ![-1,-(1/4),0]
  apply simple_nonpositive_from_leading_window lower upper (first := 0)
  · intro i; fin_cases i <;> norm_num [lower, upper]
  · intro i; fin_cases i <;> norm_num [upper]
  · intro i j h; fin_cases i <;> fin_cases j <;> norm_num [lower, upper] at *
  · intro i; fin_cases i
    · exact negL.ne
    · exact pos.ne'
    · exact negR.ne
  · intro i; fin_cases i
    · exact (mul_neg_of_neg_of_pos negL pos).le
    · exact (mul_neg_of_pos_of_neg pos negR).le
    · exact mul_nonpos_of_nonpos_of_nonneg negR.le origin
  · intro i; fin_cases i <;> norm_num [lower]
  · norm_num [lower]; exact negL
  · rw [five_mixture]
    compute_degree
  · exact mixture_coeff_nonneg _ w hw _

#print axioms four_simple
#print axioms five_simple
end LongCycleBounds.DescentBoundary

