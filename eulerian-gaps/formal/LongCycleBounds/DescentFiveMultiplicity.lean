import LongCycleBounds.DescentTwoLetters

/-! Exact adjacent-descent rows on five letters and their double root. -/

namespace LongCycleBounds.DescentTwoLetters

open Finset Polynomial LongCycles

private def allowedFive (k : ℕ) (σ : Equiv.Perm (Fin 5)) : Prop :=
  ∀ x : Fin 5, ∀ j : Fin 5, 0 < j.val → j.val < k → (σ ^ j.val) x ≠ x

private instance (k : ℕ) (σ : Equiv.Perm (Fin 5)) : Decidable (allowedFive k σ) :=
  inferInstanceAs (Decidable (∀ x : Fin 5, ∀ j : Fin 5,
    0 < j.val → j.val < k → (σ ^ j.val) x ≠ x))

private def adjacentFive (σ : Equiv.Perm (Fin 5)) : ℕ :=
  (univ.filter fun i : Fin 4 ↦ σ i.succ < σ i.castSucc).card

private def countFive (k i : ℕ) : ℤ :=
  ∑ σ ∈ permsOfFinset (univ : Finset (Fin 5)),
    if allowedFive k σ ∧ adjacentFive σ = i then 1 else 0

private def expected (i : ℕ) : ℤ :=
  if i = 1 then 6 else if i = 2 then 12 else if i = 3 then 6 else 0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem count_table :
    ∀ k : Fin 3, ∀ i : Fin 5, countFive (k.val + 3) i.val = expected i.val := by
  decide +kernel

private theorem allowedFive_iff {k : ℕ} (hk : k ≤ 5) (σ : Equiv.Perm (Fin 5)) :
    allowedFive k σ ↔ Allowed k σ :=
  ⟨fun h x j hj hjk ↦ h x ⟨j, hjk.trans_le hk⟩ hj hjk, fun h x j hj hjk ↦ h x j.val hj hjk⟩

private theorem coeff_countFive {k : ℕ} (hk : k ≤ 5) (i : ℕ) :
    (row 5 k).coeff i = countFive k i := by
  classical
  rw [coeff_row]
  unfold countFive
  have allPerms : permsOfFinset (univ : Finset (Fin 5)) = univ := by
    ext σ
    simp [mem_perms_of_finset_iff]
  rw [allPerms]
  apply sum_congr rfl
  intro σ _
  simp only [allowedFive_iff hk, adjacentFive, ← descents_eq_card]

private theorem countFive_eq {k : ℕ} (lo : 3 ≤ k) (hi : k ≤ 5) (i : ℕ) :
    countFive k i = expected i := by
  by_cases hi' : i < 5
  · let kk : Fin 3 := ⟨k - 3, by omega⟩
    have index : kk.val + 3 = k := by dsimp [kk]; omega
    simpa only [index] using count_table kk ⟨i, hi'⟩
  · have d (σ : Equiv.Perm (Fin 5)) : adjacentFive σ ≤ 4 :=
      (card_filter_le _ _).trans_eq (by simp)
    have z : countFive k i = 0 := by
      unfold countFive
      apply sum_eq_zero
      intro σ _
      apply if_neg
      intro h
      exact hi' (h.2 ▸ Nat.lt_succ_of_le (d σ))
    rw [z]
    simp [expected, show i ≠ 1 by omega, show i ≠ 2 by omega, show i ≠ 3 by omega]

/-- The original descent row is the same at each cutoff between three and five. -/
theorem row_five {k : ℕ} (lo : 3 ≤ k) (hi : k ≤ 5) :
    row 5 k = 6 * X * (1 + X) ^ 2 := by
  rw [show (6 : ℤ[X]) * X * (1 + X) ^ 2 = C 6 * X + C 12 * X ^ 2 + C 6 * X ^ 3 by
    simp only [C_ofNat]
    ring]
  ext i
  rw [coeff_countFive hi, countFive_eq lo hi]
  simp only [expected, coeff_add, coeff_C_mul_X, coeff_C_mul_X_pow]
  split_ifs <;> simp_all

/-- The genuine five-letter descent row has a root of multiplicity two at -1. -/
theorem row_five_rootMultiplicity {k : ℕ} (lo : 3 ≤ k) (hi : k ≤ 5) :
    (row 5 k).rootMultiplicity (-1) = 2 := by
  have hroot : ¬ IsRoot (6 * X : ℤ[X]) (-1) := by norm_num [IsRoot]
  have hn : (6 * X : ℤ[X]) ≠ 0 := by
    intro hz
    exact hroot (by simp [hz])
  have shift : (1 + X : ℤ[X]) = X - C (-1) := by simp [add_comm]
  rw [row_five lo hi, shift, rootMultiplicity_mul_X_sub_C_pow hn,
    rootMultiplicity_eq_zero hroot, zero_add]

/-- The same multiplicity holds after reading the integral row as a real polynomial. -/
theorem row_five_real_rootMultiplicity {k : ℕ} (lo : 3 ≤ k) (hi : k ≤ 5) :
    ((row 5 k).map (Int.castRingHom ℝ)).rootMultiplicity (-1) = 2 := by
  have hm := eq_rootMultiplicity_map (p := row 5 k)
    (f := Int.castRingHom ℝ) Int.cast_injective (-1 : ℤ)
  simpa using hm.symm.trans (row_five_rootMultiplicity lo hi)

#print axioms count_table
#print axioms row_five
#print axioms row_five_rootMultiplicity
#print axioms row_five_real_rootMultiplicity

end LongCycleBounds.DescentTwoLetters
