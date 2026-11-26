import LongCycleBounds.DescentEulerJetUniqueness
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.RingTheory.Binomial

/-! The Euler logarithmic derivative of a finite multiset inventory factor. -/
noncomputable section
namespace LongCycleBounds.DescentMesh
open Polynomial Finset
variable {R : Type*} [CommRing R] [IsDomain R] [CharZero R] [BinomialRing R]

theorem multichoose_step (M : R) (a : ℕ) :
    ((a+1:ℕ):R) * Ring.multichoose M (a+1) = (M+(a:R))*Ring.multichoose M a := by
  have h := Ring.factorial_nsmul_multichoose_eq_ascPochhammer M (a+1)
  have g := Ring.factorial_nsmul_multichoose_eq_ascPochhammer M a
  simp only [nsmul_eq_mul, ascPochhammer_smeval_eq_eval] at h g
  rw [ascPochhammer_succ_right] at h
  simp only [eval_mul, eval_add, eval_X, eval_natCast, ← g, Nat.factorial_succ,
    Nat.cast_mul] at h
  apply mul_left_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero a) : (a.factorial:R) ≠ 0)
  linear_combination h

theorem multichoose_hockey (M : R) (a : ℕ) :
    (a:R)*Ring.multichoose M a = (∑ i ∈ range a, Ring.multichoose M i)*M := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [multichoose_step, sum_range_succ]
    linear_combination ih

def coefficientBox (H : ℕ) (v : ℕ → R) : R[X] :=
  ∑ i ∈ range (H+1), monomial i (v i)

omit [IsDomain R] [CharZero R] [BinomialRing R] in
theorem coeff_box {H i : ℕ} (hi : i ≤ H) (v : ℕ → R) :
    (coefficientBox H v).coeff i = v i := by
  simp [coefficientBox, finsetSum_coeff, coeff_monomial, mem_range.mpr (Nat.lt_succ_of_le hi)]

def inventoryFactor (H : ℕ) (M : R) := coefficientBox H (Ring.multichoose M)
def inventoryKernel (H : ℕ) (M : R) := coefficientBox H (fun b ↦ if b=0 then 0 else M)

theorem inventory_factor_ode (H : ℕ) (M : R) :
    X^(H+1) ∣ inventoryKernel H M * inventoryFactor H M - eulerOp (inventoryFactor H M) := by
  apply X_pow_dvd_iff.mpr
  intro n hn
  rw [coeff_sub,euler_coeff,mul_comm (inventoryKernel H M),coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, sum_range_succ]
  simp only [inventoryFactor,inventoryKernel,Nat.sub_self,coeff_box (Nat.zero_le H),if_true,
    mul_zero,add_zero,coeff_box (Nat.le_of_lt_succ hn)]
  apply sub_eq_zero.mpr
  rw [multichoose_hockey, sum_mul]
  apply sum_congr rfl
  intro i hi
  have h := mem_range.mp hi
  rw [coeff_box (by omega : i ≤ H), coeff_box (by omega : n-i ≤ H), if_neg (by omega)]

omit [IsDomain R] [CharZero R] [BinomialRing R] in
theorem euler_expand {j : ℕ} (hj : 0 < j) (f : R[X]) :
    eulerOp (expand R j f) = (j:R[X]) * expand R j (eulerOp f) := by
  simp only [eulerOp,derivative_expand,map_mul,expand_X]
  have hx : (X:R[X])^j = X * X^(j-1) := by
    conv_lhs => rw [← Nat.succ_pred_eq_of_pos hj, pow_succ']
    rfl
  rw [hx]
  ring

theorem expanded_inventory_ode (H : ℕ) {j : ℕ} (hj : 0 < j) (M : R) :
    X^(H+1) ∣ ((j:R[X])*expand R j (inventoryKernel H M)) * expand R j (inventoryFactor H M)
      - eulerOp (expand R j (inventoryFactor H M)) := by
  obtain ⟨p,hp⟩ := inventory_factor_ode H M
  have hx := congrArg (expand R j) hp
  simp only [map_sub,map_mul,map_pow,expand_X,← pow_mul] at hx
  have he : H+1 ≤ j*(H+1) := Nat.le_mul_of_pos_left _ hj
  rw [euler_expand hj, mul_assoc, ← mul_sub, hx]
  exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_left (pow_dvd_pow X he) _) _

omit [IsDomain R] [CharZero R] [BinomialRing R] in
/-- Truncated logarithmic derivatives add under products of independent lengths. -/
theorem product_inventory_ode {ι : Type*} (s : Finset ι) (F K : ι → R[X]) (H : ℕ)
    (h : ∀ i ∈ s, X^(H+1) ∣ K i*F i-eulerOp (F i)) :
    X^(H+1) ∣ (∑ i ∈ s, K i)*(∏ i ∈ s, F i) - eulerOp (∏ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [eulerOp]
  | insert i t hi ih =>
    rw [sum_insert hi,prod_insert hi,euler_product]
    have u := h i (mem_insert_self i t)
    have v := ih (fun j hj ↦ h j (mem_insert_of_mem hj))
    have w := dvd_add (dvd_mul_of_dvd_left u (∏ j ∈ t, F j)) (dvd_mul_of_dvd_right v (F i))
    convert w using 1
    ring

#print axioms expanded_inventory_ode
#print axioms product_inventory_ode

#print axioms inventory_factor_ode
end LongCycleBounds.DescentMesh
