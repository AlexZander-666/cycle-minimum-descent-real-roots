import LongCycleBounds.DescentBoundaryOrderedSigns
import LongCycleBounds.DescentAllLarge

noncomputable section
namespace LongCycleBounds.DescentBoundary
open Finset Polynomial DescentMesh
/-- The two remaining boundary rows are tested on the very same analytic mesh. -/
theorem large_mixtures_of_two_signs {n : ℕ} (hn : 128 ≤ n)
    (extra : ∀ k, (k = 1 ∨ k = 2) → ∀ j, 2 ≤ j → j < n →
      (-1:ℝ)^j * (realRow n k).eval (rootNode n j) < 0)
    (w : ℕ → ℝ) (hw : ∀ k ∈ Icc 1 n, 0 ≤ w k) (pos : ∃ k ∈ Icc 1 n, 0 < w k) :
    (mixture n w).Splits ∧ (mixture n w).roots.Nodup ∧ ∀ x ∈ (mixture n w).roots, x ≤ 0 := by
  let a (i : Fin (n-2)) := rootNode n (n-1-i.val)
  apply all_mixtures_of_ordered_signs (by omega) a ?_ (fun _ ↦ nodeAt_negative _) ?_ w hw pos
  · intro i j hij
    have lt : i.val < j.val := hij
    have jlt := j.isLt
    apply rootNode_order <;> omega
  · intro k hk i
    have bounds := mem_Icc.mp hk
    have ilt := i.isLt
    let j := n-1-i.val
    have hj : 2 ≤ j := by dsimp [j]; omega
    have hlast : j < n := by dsimp [j]; omega
    have sign : (-1:ℝ)^j * (realRow n k).eval (a i) < 0 := by
      by_cases big : 3 ≤ k
      · exact actual_grid_sign big bounds.2 hn hj hlast
      · exact extra k (by omega) j hj hlast
    rw [neg_one_pow_eq_pow_mod_two] at sign
    change if (n-2-1-i.val)%2=0 then _ else _
    split <;> rename_i parity
    · have even : j%2=0 := by dsimp [j]; omega
      simpa [even] using sign
    · have odd : j%2=1 := by dsimp [j]; omega
      simpa [odd] using sign

#print axioms large_mixtures_of_two_signs
end LongCycleBounds.DescentBoundary
