import LongCycleBounds.DescentBoundaryFixedPoints
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.Binomial

noncomputable section
namespace LongCycleBounds.DescentNecklace
open Finset PowerSeries

private theorem coeff_fixed_multiset (q a : ℕ) :
    coeff a ((invOneSubPow ℚ q).val) = (q.multichoose a : ℚ) := by
  cases q with
  | zero =>
    cases a <;> simp [invOneSubPow_zero,coeff_one]
  | succ q =>
    rw [invOneSubPow_val_succ_eq_mk_add_choose,coeff_mk,Nat.multichoose_eq]
    norm_cast
    rw [show q+1+a-1=q+a by omega,Nat.choose_symm_of_eq_add (a:=q) (b:=a) rfl]

theorem derangement_alphabet_series (q : ℕ) :
    (mk fun n ↦ (positiveCountDP n q 2 : ℚ)) =
      (1-X : ℚ⟦X⟧)^q * (mk fun n ↦ (q:ℚ)^n) := by
  let u := invOneSubPow ℚ q
  let f := mk fun n ↦ (positiveCountDP n q 2 : ℚ)
  have conv : u.val*f = mk (fun n ↦ (q:ℚ)^n) := by
    ext n
    simp only [coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      u,coeff_fixed_multiset,f,coeff_mk]
    have z := fixed_point_convolution n q
    exact_mod_cast (by simpa only [mul_comm] using z.symm :
      ∑ a ∈ range (n+1), q.multichoose a * positiveCountDP (n-a) q 2 = q^n)
  rw [← conv, ← invOneSubPow_inv_eq_one_sub_pow, ← mul_assoc]
  change f = u.inv*u.val*f
  rw [u.inv_val,one_mul]

private theorem coeff_exclude_fixed (q a : ℕ) :
    coeff a ((1-X : ℚ⟦X⟧)^q) = (-1:ℚ)^a * q.choose a := by
  have eq : rescale (-1:ℚ) ((1+X : ℚ⟦X⟧)^q) = (1-X)^q := by
    simp [sub_eq_add_neg]
  rw [← eq,coeff_rescale]
  have poly : (1+X : ℚ⟦X⟧)^q = (((1 : Polynomial ℚ)+Polynomial.X)^q).toPowerSeries := by simp
  rw [poly,Polynomial.coeff_coe,Polynomial.coeff_one_add_X_pow]

theorem derangement_alphabet_exact (n q : ℕ) :
    (positiveCountDP n q 2 : ℚ) =
      ∑ a ∈ range (n+1), ((-1:ℚ)^a * q.choose a) * (q:ℚ)^(n-a) := by
  have e := congrArg (coeff (R:=ℚ) n) (derangement_alphabet_series q)
  simpa only [coeff_mk,coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    coeff_exclude_fixed] using e

#print axioms derangement_alphabet_series
#print axioms derangement_alphabet_exact
end LongCycleBounds.DescentNecklace
