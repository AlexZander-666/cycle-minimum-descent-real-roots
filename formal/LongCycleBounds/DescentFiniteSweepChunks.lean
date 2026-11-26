import LongCycleBounds.DescentFiniteSweep

/-! Check the alphabet sweep and signed inversions in independently evaluable pieces. -/

namespace LongCycleBounds.DescentNecklace

/-- Assemble checked alphabet slices into the original permutation-root decoder. -/
theorem representativeChecks_of_sweepChunks {n : ℕ} (hn : 3 ≤ n)
    (nodes : Array LongCycleFinite.Dyadic) (coeffs : Array (List ℤ))
    (alphabet : Fin n → Array ℕ)
    (sweep : ∀ q, alphabet q = alphabetCutoffSweep n (q.val + 1))
    (counts : ∀ i : Fin (lastRepresentative n - 2),
      readNumerator n (i.val + 3) (Array.ofFn alphabet) =
        (0 :: coeffs.getD i.val []) ++ [0])
    (signs : ∀ i : Fin (lastRepresentative n - 2),
      negativeMeshOK (coeffs.getD i.val []) nodes = true) :
    RepresentativeChecks n nodes coeffs := by
  have hAlphabet : Array.ofFn alphabet = alphabetSweeps n := by
    unfold alphabetSweeps
    rw [funext sweep]
  intro i
  have h := counts i
  rw [hAlphabet] at h
  have fit : lastRepresentative n ≤ n + 1 := by
    unfold lastRepresentative
    omega
  have hi := i.isLt
  rw [readNumerator_eq (by omega : i.val + 3 ≤ n + 1)] at h
  exact ⟨h, signs i⟩

#print axioms representativeChecks_of_sweepChunks
end LongCycleBounds.DescentNecklace
