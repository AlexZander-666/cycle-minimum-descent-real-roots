import LongCycleBounds.DescentLowerCutoffChecks
import LongCycleBounds.DescentPackedInversion

/-! Reuse cached length-one and length-two codes across all finite degrees. -/

namespace LongCycleBounds.DescentNecklace

def cachedLowerCode (one two : ℕ) (original : ℕ → ℕ) (k : ℕ) : ℕ :=
  if k = 1 then one else if k = 2 then two else original k

theorem packedChecks_of_cachedLower {bound alphabet : ℕ} (hb : 3 ≤ bound)
    {original : ℕ → ℕ} (known : PackedCutoffChecks bound alphabet 3 original)
    {one two : ℕ}
    (hTwo : two = codedCutoffStep (cutoffRadix bound alphabet) bound 2
      (primitiveCount 2 alphabet) (original 3))
    (hOne : one = codedCutoffStep (cutoffRadix bound alphabet) bound 1
      (primitiveCount 1 alphabet) two) :
    PackedCutoffChecks bound alphabet 1 (cachedLowerCode one two original) := by
  have equal : cachedLowerCode one two original = extendCutoffCode bound alphabet original := by
    funext k
    simp [cachedLowerCode, extendCutoffCode, hOne, hTwo]
  rw [equal]
  exact known.extend_one hb

/-- Read the usual numerator efficiently once the cached low-cutoff codes have been checked. -/
def cachedLowerNumerator (bound n k : ℕ) (codes : Fin n → ℕ → ℕ) : List ℤ :=
  packedInversion n (readPackedAlphabet bound n k codes)

theorem cachedLowerNumerator_eq {bound n k : ℕ} (fit : n ≤ bound)
    (hk : 1 ≤ k) (hi : k ≤ bound + 1) (codes : Fin n → ℕ → ℕ)
    (checked : ∀ i, PackedCutoffChecks bound (i.val + 1) 1 (codes i)) :
    cachedLowerNumerator bound n k codes = descentRowDP n k := by
  have alphabet : readPackedAlphabet bound n k codes = descentAlphabetTable n k := by
    unfold readPackedAlphabet descentAlphabetTable
    congr
    funext i
    exact (checked i).count_eq (Nat.succ_pos _) (by decide) fit hk hi
  simp only [cachedLowerNumerator, packedInversion_eq, alphabet, descentRowDP]

#print axioms packedChecks_of_cachedLower
#print axioms cachedLowerNumerator_eq

end LongCycleBounds.DescentNecklace
