import LongCycleBounds.DescentMeshLoss
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Divisors

/-! The actual Möbius coefficients of the primitive necklace logarithm. -/
noncomputable section
namespace LongCycleBounds.DescentMesh
open Finset ArithmeticFunction
open scoped Moebius

/-- Absolute nonprincipal amount in the length-j primitive necklace term. -/
def primitiveCost (j : ℕ) (v : ℝ) : ℝ :=
  (∑ d ∈ j.divisors.erase 1, |(μ d:ℝ)| * v^(j-j/d)) / j

theorem nontrivial_divisors_card {j : ℕ} (hj : 0 < j) : (j.divisors.erase 1).card ≤ j/2 := by
  have sz : (j.divisors.erase 1).card = j.properDivisors.card := by
    rw [card_erase_of_mem (Nat.one_mem_divisors.mpr hj.ne'), ← Nat.insert_self_properDivisors hj.ne',
      card_insert_of_notMem Nat.self_notMem_properDivisors]
    omega
  rw [sz]
  have sub : j.properDivisors ⊆ Icc 1 (j/2) := by
    intro d mem
    have dp := Nat.pos_of_mem_properDivisors mem
    obtain ⟨dvd,lt⟩ := Nat.mem_properDivisors.mp mem
    obtain ⟨a,ha⟩ := dvd
    have atwo : 2 ≤ a := by
      by_contra! h
      interval_cases a <;> simp_all
    have hmul := Nat.mul_le_mul_left d atwo
    exact mem_Icc.mpr ⟨dp, by omega⟩
  simpa using card_le_card sub

/-- All real evaluations up to the unit radius have the explicit generic primitive tail. -/
theorem primitiveCost_le {j : ℕ} (hj : 3 ≤ j) {v : ℝ} (hv : 0 ≤ v) (h1 : v ≤ 1) :
    primitiveCost j v ≤ (1/2:ℝ)*v^((j+1)/2) := by
  have jp : 0 < (j:ℝ) := by exact_mod_cast (by omega : 0<j)
  have one (d : ℕ) (mem : d ∈ j.divisors.erase 1) :
      |(μ d:ℝ)| * v^(j-j/d) ≤ v^((j+1)/2) := by
    obtain ⟨d1,divisor⟩ := mem_erase.mp mem
    have dpos := Nat.pos_of_mem_divisors divisor
    have loss := (decoration_loss (b:=1) hj (by omega) dpos (Or.inr d1)).2
    have small : (j+1)/2 ≤ j-j/d := by simp only [Nat.mul_one] at loss; omega
    have abs : |(μ d:ℝ)| ≤ 1 := by exact_mod_cast (abs_moebius_le_one (n:=d))
    exact (mul_le_mul_of_nonneg_right abs (pow_nonneg hv _)).trans
      (by simpa using pow_le_pow_of_le_one hv h1 small)
  unfold primitiveCost
  apply (div_le_iff₀ jp).mpr
  have cc : 2*(j.divisors.erase 1).card ≤ j := by
    have := nontrivial_divisors_card (by omega : 0<j)
    omega
  have rr : 2*((j.divisors.erase 1).card:ℝ) ≤ j := by exact_mod_cast cc
  have sm := sum_le_sum one
  simp only [sum_const, nsmul_eq_mul] at sm
  nlinarith only [sm,mul_nonneg (sub_nonneg.mpr rr) (pow_nonneg hv ((j+1)/2))]

/-- Exact low primitive logarithmic terms, independently of the positive real radius. -/
theorem primitiveCost_small (v : ℝ) :
    primitiveCost 3 v = v^2/3 ∧ primitiveCost 4 v = v^2/4 ∧
    primitiveCost 5 v = v^4/5 ∧ primitiveCost 6 v = (v^3+v^4+v^5)/6 ∧
    primitiveCost 7 v = v^6/7 := by
  have ss3 : (3:ℕ).divisors.erase 1 = {3} := by decide
  have ss4 : (4:ℕ).divisors.erase 1 = {2,4} := by decide
  have ss5 : (5:ℕ).divisors.erase 1 = {5} := by decide
  have ss6 : (6:ℕ).divisors.erase 1 = {2,3,6} := by decide
  have ss7 : (7:ℕ).divisors.erase 1 = {7} := by decide
  have m2 : μ 2 = -1 := moebius_apply_prime (by decide)
  have m3 : μ 3 = -1 := moebius_apply_prime (by decide)
  have m4 : μ 4 = 0 := by decide
  have m5 : μ 5 = -1 := moebius_apply_prime (by decide)
  have m6 : μ 6 = 1 := by
    rw [show 6=2*3 by decide, isMultiplicative_moebius.map_mul_of_coprime (by decide : Nat.Coprime 2 3),m2,m3]
    decide
  have m7 : μ 7 = -1 := moebius_apply_prime (by decide)
  norm_num [primitiveCost,ss3,ss4,ss5,ss6,ss7,m2,m3,m4,m5,m6,m7,add_assoc]

#print axioms primitiveCost_small
#print axioms nontrivial_divisors_card
#print axioms primitiveCost_le
end LongCycleBounds.DescentMesh
