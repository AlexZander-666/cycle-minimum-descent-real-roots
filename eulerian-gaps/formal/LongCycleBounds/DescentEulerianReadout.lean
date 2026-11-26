import LongCycleBounds.DescentAlphabetPolynomial
import LongCycleBounds.DescentMeshTransform

/-! From the original permutation row to the Eulerian transform used in the analytic bounds. -/
noncomputable section
namespace LongCycleBounds.DescentNecklace
open LongCycles DescentTwoLetters Finset

theorem full_letters {n : ℕ} (hn : 0 < n) (q : ℕ) :
    letters n q (row n 0).coeff = (q:ℤ)^n := by
  have unit : ∀ u : Compatible n q, Allowed 0 u.val.1 := fun _ _ _ _ h ↦ (Nat.not_lt_zero _ h).elim
  let e : AllowedCompatible n q 0 ≃ (Fin n → Fin q) :=
    (Equiv.subtypeUnivEquiv unit).trans (wordEquiv n q).symm
  rw [← card_allowedCompatible_eq_letters hn, Nat.card_congr e, Nat.card_fun]
  simp

theorem full_row (n : ℕ) : (row n 0).map (Int.castRingHom ℝ) = eulerian n := by
  classical
  simp [row,eulerian,Allowed,Polynomial.map_sum]

theorem coe_row_numerator {n : ℕ} (hn : 0 < n) (k : ℕ) :
    ((row n k : Polynomial ℤ) : PowerSeries ℤ) = numerator n (row n k).coeff := by
  ext r
  rw [Polynomial.coeff_coe]
  by_cases hr : r < n
  · exact (coeff_numerator _ _ _ hr).symm
  have bounds (σ : Equiv.Perm (Fin n)) : descents σ < n := by
    cases n with
    | zero => omega
    | succ m =>
      rw [descents_eq_card]
      exact (card_filter_le _ _).trans_lt (by simp)
  have z : (row n k).coeff r = 0 := by
    rw [coeff_row]
    apply sum_eq_zero
    intro σ _
    exact if_neg fun ⟨_,eq⟩ ↦ hr (eq ▸ bounds σ)
  rw [z]
  simp only [numerator,map_sum,PowerSeries.coeff_C_mul_X_pow]
  symm
  apply sum_eq_zero
  intro i hi
  exact if_neg (show r ≠ i from fun eq ↦ hr (eq.symm ▸ mem_range.mp hi))

theorem original_row_series {n : ℕ} (hn : 0 < n) (k : ℕ) :
    (((row n k).map (Int.castRingHom ℝ) : Polynomial ℝ) : PowerSeries ℝ) =
      (1-PowerSeries.X)^(n+1) *
        PowerSeries.mk (fun j ↦ (letters n (j+1) (row n k).coeff : ℝ)) := by
  have h := (coe_row_numerator hn k).trans (numerator_from_letters hn _)
  have mapped := congrArg (PowerSeries.map (Int.castRingHom ℝ)) h
  rw [Polynomial.polynomial_map_coe]
  convert mapped using 1
  rw [map_mul,map_pow,map_sub,map_one,PowerSeries.map_X]
  congr 1

theorem eulerian_series {h : ℕ} (hh : 0 < h) :
    (eulerian h : PowerSeries ℝ) = (1-PowerSeries.X)^(h+1) *
      PowerSeries.mk (fun j : ℕ ↦ ((j:ℝ)+1)^h) := by
  simpa only [full_row,full_letters hh,Int.cast_pow,Int.cast_natCast,Nat.cast_add,Nat.cast_one,Int.cast_add,Int.cast_one]
    using original_row_series hh 0

theorem alphabet_expansion {n : ℕ} (hn : 0 < n) (d : ℕ → ℤ) (q : ℕ) :
    (letters n q d : ℝ) =
      ∑ h ∈ Icc 1 n, ((alphabetPolynomial n d).coeff h : ℝ) * (q:ℝ)^h := by
  have ev := eval_alphabet_int n (q:ℤ) d
  rw [signedLetters_nat,Polynomial.eval_eq_sum_range'
    (Nat.lt_succ_of_le (alphabet_degree n d))] at ev
  have rat : (letters n q d : ℚ) =
      ∑ h ∈ Icc 1 n, (alphabetPolynomial n d).coeff h * (q:ℚ)^h := by
    rw [← ev,Int.cast_natCast]
    symm
    apply sum_subset
    · intro i hi
      exact mem_range.mpr (Nat.lt_succ_of_le (mem_Icc.mp hi).2)
    · intro i hi outside
      have eq : i = 0 := by
        simp only [mem_Icc,not_and] at outside
        have := mem_range.mp hi
        omega
      simp [eq,alphabet_zero hn]
  exact_mod_cast rat

private theorem alphabet_series {n : ℕ} (hn : 0 < n) (d : ℕ → ℤ) :
    PowerSeries.mk (fun j ↦ (letters n (j+1) d : ℝ)) =
      ∑ h ∈ Icc 1 n, PowerSeries.C ((alphabetPolynomial n d).coeff h : ℝ) *
        PowerSeries.mk (fun j : ℕ ↦ ((j:ℝ)+1)^h) := by
  ext j
  simp only [PowerSeries.coeff_mk,map_sum,PowerSeries.coeff_C_mul]
  simpa only [Nat.cast_add,Nat.cast_one] using alphabet_expansion hn d (j+1)

/-- The polynomial bounded on the analytic grid is the ordinary descent row on actual permutations. -/
theorem original_eq_descentTransform {n : ℕ} (hn : 0 < n) (k : ℕ) :
    (row n k).map (Int.castRingHom ℝ) = DescentMesh.descentTransform n
      (fun h ↦ ((profilePolynomial n k).coeff h : ℝ)) := by
  rw [← alphabet_eq_profile hn]
  apply Polynomial.coe_injective (R := ℝ)
  rw [original_row_series hn,alphabet_series hn,mul_sum]
  change _ = Polynomial.coeToPowerSeries.ringHom (∑ h ∈ Icc 1 n, _)
  rw [map_sum]
  apply sum_congr rfl
  intro h hh
  have bounds := mem_Icc.mp hh
  simp only [map_mul,Polynomial.coeToPowerSeries.ringHom_apply,
    Polynomial.coe_C,Polynomial.coe_pow,Polynomial.coe_sub,Polynomial.coe_one,Polynomial.coe_X]
  rw [eulerian_series bounds.1]
  rw [show n+1 = (n-h)+(h+1) by omega,pow_add]
  ring

#print axioms original_eq_descentTransform
#print axioms original_row_series
#print axioms eulerian_series
end LongCycleBounds.DescentNecklace
