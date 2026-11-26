import LongCycleBounds.DescentManuscriptIsolation

/-! The manuscript conclusions from common intervals, including the exceptional five-letter row. -/
noncomputable section
namespace LongCycleBounds.DescentNecklace
open Finset Polynomial DescentTwoLetters

/-- Taking one positive weight recovers the original cutoff polynomial. -/
theorem single_cutoff_mixture {n k : ℕ} (hk : 3 ≤ k) (kn : k ≤ n) :
    (∑ j ∈ Icc 3 n, C (if j = k then (1:ℝ) else 0) *
      (row n j).map (Int.castRingHom ℝ)) = (row n k).map (Int.castRingHom ℝ) := by
  classical
  rw [sum_eq_single_of_mem k (mem_Icc.mpr ⟨hk,kn⟩)]
  · simp
  · intro j _ ne
    simp [ne]

/-- The true cutoff rows inherit every simple-root assertion for nonexceptional sizes. -/
theorem original_from_isolation {n k : ℕ} (hk : 3 ≤ k) (kn : k ≤ n)
    (mesh : CommonIsolatingIntervals n) :
    let p := (row n k).map (Int.castRingHom ℝ)
    p.Splits ∧ p.roots.Nodup ∧ 0 ∈ p.roots ∧ p.natDegree = n-2 ∧
      (p.roots.filter (· < 0)).card = n-3 := by
  obtain ⟨_, _, _, _, allWeights⟩ := mesh
  let w : ℕ → ℝ := fun j ↦ if j = k then 1 else 0
  have hw (j : ℕ) (_ : j ∈ Icc 3 n) : 0 ≤ w j := by simp [w, apply_ite]
  have pos : ∃ j ∈ Icc 3 n, 0 < w j := ⟨k, mem_Icc.mpr ⟨hk,kn⟩, by simp [w]⟩
  simpa only [w, single_cutoff_mixture hk kn] using (allWeights w hw pos).2

/-- A finite certificate covers its designated sizes and the analytic proof covers the whole tail. -/
theorem isolating_from_prefix {bound n : ℕ} (hn : 3 ≤ n) (five : n ≠ 5)
    (finite : ∀ {m : ℕ}, 3 ≤ m → m ≤ bound → m ≠ 5 →
      ∃ a : Array LongCycleFinite.Dyadic, ∃ rows : Array (List ℤ),
        a.size = m-2 ∧ RepresentativeChecks m a rows)
    (range : n ≤ bound ∨ 128 ≤ n) : CommonIsolatingIntervals n :=
  isolating_of_shared (shared_intervals_of_evidence hn (range.imp_left fun hi ↦ finite hn hi five))

/-- For all sizes with common isolating intervals outside five, every allowed mixture splits. -/
theorem mixtures_from_isolation {n : ℕ} (mesh : n ≠ 5 → CommonIsolatingIntervals n)
    (w : ℕ → ℝ) (hw : ∀ k ∈ Icc 3 n, 0 ≤ w k) (pos : ∃ k ∈ Icc 3 n, 0 < w k) :
    (∑ k ∈ Icc 3 n, C (w k) * (row n k).map (Int.castRingHom ℝ)).Splits := by
  by_cases five : n = 5
  · subst n
    exact (five_mixture_roots w hw pos).2.1
  · obtain ⟨_, _, _, _, allWeights⟩ := mesh five
    exact (allWeights w hw pos).2.1

#print axioms original_from_isolation
#print axioms isolating_from_prefix
#print axioms mixtures_from_isolation
end LongCycleBounds.DescentNecklace

