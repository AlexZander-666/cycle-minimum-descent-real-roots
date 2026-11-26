import LongCycleBounds.DescentNecklaceDP

/-! Agreement of positive counting tables on smaller total weights. -/

namespace LongCycleBounds.DescentNecklace

open Finset Polynomial

private theorem countTable_cons_at (bound : ℕ) {w M d : ℕ}
    (hw : 0 < w) (fits : d ≤ bound) (l : List (ℕ × ℕ))
    (positive : ∀ pair ∈ l, 0 < pair.1) :
    (countTable bound ((w, M) :: l)).getD d 0 =
      ∑ a ∈ range (d / w + 1),
        (countTable bound l).getD (d - w * a) 0 * multiplicityWeight M a := by
  have all : ∀ pair ∈ (w, M) :: l, 0 < pair.1 := by
    intro p hp
    rcases List.mem_cons.mp hp with h | h
    · simpa [h] using hw
    · exact positive p h
  rw [countTable_correct bound _ all fits, List.map_cons, List.prod_cons, mul_comm,
    coeff_mul_lengthFactor _ hw M fits]
  refine sum_congr rfl fun a _ ↦ ?_
  rw [countTable_correct bound l positive ((Nat.sub_le ..).trans fits)]

private theorem countTable_largeLengths (bound d : ℕ) (fits : d ≤ bound)
    (l : List (ℕ × ℕ)) (above : ∀ pair ∈ l, d < pair.1) :
    (countTable bound l).getD d 0 = (initialTable bound).getD d 0 := by
  induction l with
  | nil => rfl
  | cons pair rest ih =>
    rcases pair with ⟨w, M⟩
    have hw : d < w := above _ List.mem_cons_self
    have tail : ∀ p ∈ rest, d < p.1 := fun p hp ↦ above p (List.mem_cons_of_mem _ hp)
    rw [countTable_cons_at bound (Nat.zero_lt_of_lt hw) fits rest
      (fun p hp ↦ Nat.zero_lt_of_lt (tail p hp))]
    simpa [Nat.div_eq_of_lt hw, multiplicityWeight] using ih tail

/-- Truncation to smaller weights commutes with deleting a suffix of heavier factors. -/
theorem countTable_trim {small large : ℕ} (cap : small ≤ large)
    (kept extra : List (ℕ × ℕ)) (positive : ∀ p ∈ kept, 0 < p.1)
    (above : ∀ p ∈ extra, small < p.1) {d : ℕ} (fits : d ≤ small) :
    (countTable large (kept ++ extra)).getD d 0 = (countTable small kept).getD d 0 := by
  induction kept generalizing d with
  | nil =>
    simp only [List.nil_append]
    rw [countTable_largeLengths large d (fits.trans cap) extra
      (fun p hp ↦ fits.trans_lt (above p hp))]
    simp [countTable, initialTable, fits, fits.trans cap]
  | cons pair rest ih =>
    rcases pair with ⟨w, M⟩
    have hw : 0 < w := positive _ List.mem_cons_self
    have tail : ∀ p ∈ rest, 0 < p.1 := fun p hp ↦ positive p (List.mem_cons_of_mem _ hp)
    have combined : ∀ p ∈ rest ++ extra, 0 < p.1 := by
      intro p hp
      rcases List.mem_append.mp hp with h | h
      · exact tail p h
      · exact Nat.zero_lt_of_lt (above p h)
    rw [List.cons_append, countTable_cons_at large hw (fits.trans cap) _ combined,
      countTable_cons_at small hw fits _ tail]
    exact sum_congr rfl fun a _ ↦
      congrArg (· * multiplicityWeight M a) (ih tail ((Nat.sub_le ..).trans fits))

/-- One counting table built at a larger cap also answers every smaller size. -/
theorem positiveCountDP_at_cap {n bound : ℕ} (fits : n ≤ bound) (q k : ℕ) :
    (countTable bound (positiveFactors bound q k)).getD n 0 = positiveCountDP n q k := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le fits
  let remaining := List.ofFn fun i : Fin m ↦
    (n + i.val + 1, if n + i.val + 1 < k then 0 else primitiveCount (n + i.val + 1) q)
  have split : positiveFactors (n + m) q k = positiveFactors n q k ++ remaining := by
    rw [positiveFactors, List.ofFn_add]
    rfl
  have positive : ∀ p ∈ positiveFactors n q k, 0 < p.1 := by
    intro p hp
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
    exact Nat.succ_pos i.val
  have above : ∀ p ∈ remaining, n < p.1 := by
    intro p hp
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
    change n < n + i.val + 1
    omega
  rw [split]
  exact countTable_trim (by omega) _ _ positive above le_rfl

#print axioms countTable_trim
#print axioms positiveCountDP_at_cap
end LongCycleBounds.DescentNecklace
