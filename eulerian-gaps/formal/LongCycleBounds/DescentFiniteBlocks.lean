import LongCycleBounds.DescentFiniteRoots
import LongCycleBounds.DescentFiveMultiplicity
import LongCycles.PermCycleBridge

/-! Assembly of finite ordinary-descent row certificates, with single-cycle cutoff reuse. -/

namespace LongCycleBounds.DescentNecklace

open Finset LongCycles LongCycleFinite Polynomial
open scoped Classical

private theorem allowed_iff_single_cycleType {n k : ℕ} (hk : 2 ≤ k) (kn : k ≤ n)
    (one : n < 2 * k) (σ : Equiv.Perm (Fin n)) :
    Allowed k σ ↔ σ.cycleType = {n} := by
  constructor
  · intro allowed
    have sum : σ.cycleType.toList.sum = n := by
      simp [Equiv.Perm.sum_cycleType, support_univ_of_allowed allowed hk]
    have lower : ∀ j ∈ σ.cycleType.toList, k ≤ j :=
      fun j hj ↦ le_of_mem_cycleType allowed (by simpa using hj)
    have single : σ.cycleType.toList = [n] := by
      generalize σ.cycleType.toList = l at sum lower ⊢
      cases l with
      | nil => simp at sum; omega
      | cons a rest =>
        cases rest with
        | nil => simpa using sum
        | cons b rest =>
          have ha := lower a (by simp)
          have hb := lower b (by simp)
          simp at sum
          omega
    simpa using congrArg (fun words : List ℕ ↦ (words : Multiset ℕ)) single
  · intro single
    apply allowed_of_cycleType_lower
    · apply Finset.eq_univ_of_card
      rw [← Equiv.Perm.sum_cycleType, single, Fintype.card_fin]
      simp
    · intro j hj
      rw [single, Multiset.mem_singleton] at hj
      exact hj.symm ▸ kn

/-- The last distinct cutoff needed at size n is the first that permits only one cycle. -/
def lastRepresentative (n : ℕ) : ℕ := max 3 (n / 2 + 1)

theorem row_eq_representative {n k : ℕ} (hk : 3 ≤ k) (kn : k ≤ n) :
    DescentTwoLetters.row n k =
      DescentTwoLetters.row n (min k (lastRepresentative n)) := by
  by_cases below : k ≤ lastRepresentative n
  · rw [min_eq_left below]
  · have h := Nat.lt_of_not_ge below
    have atLeast : 3 ≤ lastRepresentative n := le_max_left ..
    have larger : n / 2 + 1 ≤ lastRepresentative n := le_max_right ..
    rw [min_eq_right h.le]
    unfold DescentTwoLetters.row
    apply sum_congr rfl
    intro σ _
    rw [allowed_iff_single_cycleType (by omega) kn (by omega),
      allowed_iff_single_cycleType (by omega) (h.le.trans kn) (by omega)]

/-- Predicate for a simple zero and exactly n-3 distinct negative roots of the original row. -/
def SimpleDescentRootPattern (n k : ℕ) : Prop :=
  let p := (DescentTwoLetters.row n k).map (Int.castRingHom ℝ)
  p.Splits ∧ p.roots.Nodup ∧ 0 ∈ p.roots ∧ p.roots.card = n - 2 ∧
    (p.roots.filter (· < 0)).card = n - 3

/-- One finite input row for each cutoff representative at a given size. -/
def RepresentativeChecks (n : ℕ) (nodes : Array LongCycleFinite.Dyadic)
    (coefficients : Array (List ℤ)) : Prop :=
  ∀ i : Fin (lastRepresentative n - 2),
    descentRowDP n (i.val + 3) = (0 :: coefficients.getD i.val []) ++ [0] ∧
      negativeMeshOK (coefficients.getD i.val []) nodes = true

/-- Decode one checked block at a fixed size into a result for every original cutoff. -/
theorem simpleDescentRoots_of_representativeChecks {n : ℕ}
    (hn : 3 ≤ n) {nodes : Array LongCycleFinite.Dyadic} (size : nodes.size = n - 2)
    {coefficients : Array (List ℤ)} (checks : RepresentativeChecks n nodes coefficients)
    {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ n) : SimpleDescentRootPattern n k := by
  let cutoff := min k (lastRepresentative n)
  have cutLower : 3 ≤ cutoff := le_min hk (le_max_left ..)
  let ci : Fin (lastRepresentative n - 2) := ⟨cutoff - 3, by
    have le : cutoff ≤ lastRepresentative n := min_le_right ..
    omega⟩
  have hcut : ci.val + 3 = cutoff := Nat.sub_add_cancel cutLower
  obtain ⟨counts, signs⟩ := checks ci
  rw [hcut] at counts
  unfold SimpleDescentRootPattern
  rw [row_eq_representative hk kn]
  have h := original_root_count_of_checks (by omega : 0 < n) counts signs
  have hh : nodes.size - 1 = n - 3 := by omega
  have plus : n - 3 + 1 = n - 2 := by omega
  simpa only [hh, plus, cutoff] using h

/-- The exceptional five-letter factorization has a repeated negative root. -/
theorem row_five_splits {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 5) :
    ((DescentTwoLetters.row 5 k).map (Int.castRingHom ℝ)).Splits := by
  rw [DescentTwoLetters.row_five hk kn]
  have h : ((6 : ℤ[X]) * X * (1 + X) ^ 2).Splits := by
    simpa [add_comm] using
      (Splits.X.C_mul (6 : ℤ)).mul ((Splits.X_add_C (1 : ℤ)).pow 2)
  exact h.map (Int.castRingHom ℝ)

#print axioms row_eq_representative
#print axioms simpleDescentRoots_of_representativeChecks
#print axioms row_five_splits
end LongCycleBounds.DescentNecklace
