import LongCycleBounds.DescentVerifiedRanges

/-! Common isolating intervals for all nonzero nonnegative mixtures of original rows. -/
noncomputable section
namespace LongCycleBounds.DescentNecklace
open Finset Polynomial DescentTwoLetters

private theorem exhaust_negative_roots {p : ℝ[X]} {d : ℕ} {r : Fin d → ℝ}
    (hp : p ≠ 0) (inj : Function.Injective r) (negative : ∀ i, r i < 0)
    (root : ∀ i, p.eval (r i) = 0) (count : (p.roots.filter (· < 0)).card = d)
    {y : ℝ} (hy : y < 0) (ey : p.eval y = 0) : ∃ j, r j = y := by
  classical
  let points := (univ : Finset (Fin d)).map ⟨r, inj⟩
  let negatives := (p.roots.filter (· < 0)).toFinset
  have incl : points ⊆ negatives := by
    intro x hx
    obtain ⟨j, _, rfl⟩ := mem_map.mp hx
    exact Multiset.mem_toFinset.mpr (Multiset.mem_filter.mpr
      ⟨(mem_roots hp).mpr (root j), negative j⟩)
  have size : points.card = d := by simp [points]
  have eq : points = negatives := eq_of_subset_of_card_le incl
    (((Multiset.toFinset_card_le _).trans_eq count).trans_eq size.symm)
  have mem : y ∈ negatives := Multiset.mem_toFinset.mpr (Multiset.mem_filter.mpr
    ⟨(mem_roots hp).mpr ey, hy⟩)
  obtain ⟨j, _, h⟩ := mem_map.mp (eq.symm ▸ mem : y ∈ points)
  exact ⟨j, h⟩

/-- The intervals depend only on the permutation size, including when the weights vary. -/
def CommonIsolatingIntervals (n : ℕ) : Prop :=
  ∃ lower upper : Fin (n-3) → ℝ, (∀ i, upper i < 0) ∧
    Pairwise (fun i j ↦ Disjoint (Set.Ioo (lower i) (upper i)) (Set.Ioo (lower j) (upper j))) ∧
    ∀ w : ℕ → ℝ, (∀ k ∈ Icc 3 n, 0 ≤ w k) → (∃ k ∈ Icc 3 n, 0 < w k) →
      let p := ∑ k ∈ Icc 3 n, C (w k) * (row n k).map (Int.castRingHom ℝ)
      (∀ i, ∃! y, y ∈ Set.Ioo (lower i) (upper i) ∧ p.eval y = 0) ∧
      p.Splits ∧ p.roots.Nodup ∧ 0 ∈ p.roots ∧ p.natDegree = n-2 ∧
      (p.roots.filter (· < 0)).card = n-3

theorem isolating_of_shared {n : ℕ} (shared : SharedRootIntervals n) :
    CommonIsolatingIntervals n := by
  obtain ⟨lower, upper, below, separated, allWeights⟩ := shared
  refine ⟨lower, upper, below, separated, ?_⟩
  intro w hw pos
  obtain ⟨r, inj, loc, split, nodup, zero, degree, count⟩ := allWeights w hw pos
  refine ⟨?_, split, nodup, zero, degree, count⟩
  intro i
  refine ⟨r i, ⟨⟨(loc i).1, (loc i).2.1⟩, (loc i).2.2.2⟩, ?_⟩
  rintro y ⟨inside, ey⟩
  obtain ⟨j, rfl⟩ := exhaust_negative_roots (ne_zero_of_mem_roots zero) inj
    (fun j ↦ (loc j).2.2.1) (fun j ↦ (loc j).2.2.2) count (inside.2.trans (below i)) ey
  by_cases eq : i = j
  · rw [eq]
  · exact False.elim (Set.disjoint_left.mp (separated eq) inside ⟨(loc j).1, (loc j).2.1⟩)

#print axioms isolating_of_shared
end LongCycleBounds.DescentNecklace

