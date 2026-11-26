import LongCycleBounds.DescentManuscript
import LongCycleBounds.DescentFiniteThrough127

/-! All sizes for the ordinary descent polynomial of permutations with long cycles. -/
noncomputable section
namespace LongCycleBounds.DescentNecklace
open Finset Polynomial DescentTwoLetters

theorem common_isolating_all_sizes {n : ℕ} (hn : 3 ≤ n) (five : n ≠ 5) :
    CommonIsolatingIntervals n :=
  isolating_from_prefix hn five (bound := 127) finite_certificate_through127 (by omega)

theorem original_roots_all_sizes {n k : ℕ} (hk : 3 ≤ k) (kn : k ≤ n)
    (five : n ≠ 5) :
    let p := (row n k).map (Int.castRingHom ℝ)
    p.Splits ∧ p.roots.Nodup ∧ 0 ∈ p.roots ∧ p.natDegree = n-2 ∧
      (p.roots.filter (· < 0)).card = n-3 :=
  original_from_isolation hk kn (common_isolating_all_sizes (hk.trans kn) five)

theorem mixture_splits_all_sizes {n : ℕ} (hn : 3 ≤ n)
    (w : ℕ → ℝ) (hw : ∀ k ∈ Icc 3 n, 0 ≤ w k) (pos : ∃ k ∈ Icc 3 n, 0 < w k) :
    (∑ k ∈ Icc 3 n, C (w k) * (row n k).map (Int.castRingHom ℝ)).Splits :=
  mixtures_from_isolation (fun five ↦ common_isolating_all_sizes hn five) w hw pos

theorem original_splits_all_sizes {n k : ℕ} (hk : 3 ≤ k) (kn : k ≤ n) :
    ((row n k).map (Int.castRingHom ℝ)).Splits := by
  by_cases five : n = 5
  · subst n
    exact row_five_splits hk kn
  · exact (original_roots_all_sizes hk kn five).1

#print axioms common_isolating_all_sizes
#print axioms original_roots_all_sizes
#print axioms mixture_splits_all_sizes
#print axioms original_splits_all_sizes
#print axioms LongCycleBounds.DescentTwoLetters.row_five
#print axioms LongCycleBounds.DescentTwoLetters.five_mixture_roots
end LongCycleBounds.DescentNecklace

