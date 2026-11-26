import LongCycleBounds.DescentMeshGoodODE

/-! Uniqueness through a finite cutoff for the Euler logarithmic derivative. -/
noncomputable section
namespace LongCycleBounds.DescentMesh
open Finset Polynomial

theorem euler_jet_unique {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    {N : ℕ} {L p q : R[X]} (hL : L.coeff 0 = 0)
    (h0 : p.coeff 0 = q.coeff 0)
    (hp : X^(N+1) ∣ L*p - eulerOp p) (hq : X^(N+1) ∣ L*q - eulerOp q)
    {n : ℕ} (hn : n ≤ N) : p.coeff n = q.coeff n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn0 : n = 0
    · simpa [hn0] using h0
    have prodEq : (p*L).coeff n = (q*L).coeff n := by
      simp only [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
        sum_range_succ, Nat.sub_self, hL, mul_zero, add_zero]
      apply sum_congr rfl
      intro i hi
      rw [ih i (mem_range.mp hi) (by have h := mem_range.mp hi; omega)]
    have ep := X_pow_dvd_iff.mp hp n (by omega)
    have eqn := X_pow_dvd_iff.mp hq n (by omega)
    rw [coeff_sub, euler_coeff, mul_comm L p] at ep
    rw [coeff_sub, euler_coeff, mul_comm L q] at eqn
    exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr hn0 : (n:R) ≠ 0)
      ((sub_eq_zero.mp ep).symm.trans (prodEq.trans (sub_eq_zero.mp eqn)))
#print axioms euler_jet_unique
end LongCycleBounds.DescentMesh
