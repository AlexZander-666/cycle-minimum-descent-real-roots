import LongCycleBounds.DescentFiniteCap
import LongCycleBounds.DescentFiniteSweepChunks
import LongCycleBounds.DescentFrozenConstants

/-! One checked descending-cutoff count table gives the alphabet counts at every smaller size. -/

namespace LongCycleBounds.DescentNecklace

private def allLengths (bound q : ℕ) : List (ℕ × ℕ) :=
  List.ofFn fun j : Fin bound ↦ (j.val + 1, primitiveCount (j.val + 1) q)

/-- The reference state is the truncated product over all lengths at least the cutoff. -/
def cappedCutoffState (bound q k : ℕ) : Array ℕ :=
  countTable bound ((allLengths bound q).drop (k - 1))

theorem cappedCutoffState_count {n bound : ℕ} (fit : n ≤ bound) (q k : ℕ) :
    (cappedCutoffState bound q k).getD n 0 = positiveCountDP n q k := by
  have drop :
      countTable bound (positiveFactors bound q k) = cappedCutoffState bound q k := by
    let removeUnavailable :=
      descentFrozenConst LongCycleBounds.DescentFiniteSweep
        LongCycleBounds.DescentNecklace.countTable_drop_cutoff
    simpa only [cappedCutoffState, allLengths, positiveFactors, Nat.add_comm 1] using
      removeUnavailable bound q k 1 bound
  rw [← drop]
  exact positiveCountDP_at_cap fit q k

@[simp] theorem cappedCutoffState_top (bound q : ℕ) :
    cappedCutoffState bound q (bound + 1) = initialTable bound := by
  rw [cappedCutoffState, Nat.add_sub_cancel, List.drop_of_length_le (by simp [allLengths])]
  rfl

theorem cappedCutoffState_step {bound k : ℕ} (positive : 0 < k) (fits : k ≤ bound) (q : ℕ) :
    cappedCutoffState bound q k =
      convolveTable bound k (primitiveCount k q) (cappedCutoffState bound q (k + 1)) := by
  have h : k - 1 < (allLengths bound q).length := by
    simp [allLengths]
    omega
  have cons := List.drop_eq_getElem_cons h
  have head : (allLengths bound q)[k - 1] = (k, primitiveCount k q) := by
    simp [allLengths, Nat.sub_add_cancel (by omega : 1 ≤ k)]
  rw [head, Nat.sub_add_cancel (by omega : 1 ≤ k)] at cons
  unfold cappedCutoffState
  rw [cons]
  rfl

/-- A supplied state sequence is certified by local convolutions in decreasing cutoff order. -/
structure CappedCutoffChecks (bound q lower : ℕ) (states : ℕ → Array ℕ) : Prop where
  base : states (bound + 1) = initialTable bound
  step : ∀ k, lower ≤ k → k ≤ bound →
    states k = convolveTable bound k (primitiveCount k q) (states (k + 1))

theorem CappedCutoffChecks.state_eq {bound q lower : ℕ} {states : ℕ → Array ℕ}
    (h : CappedCutoffChecks bound q lower states) (positive : 0 < lower)
    {k : ℕ} (lo : lower ≤ k) (hi : k ≤ bound + 1) :
    states k = cappedCutoffState bound q k := by
  have step (j : ℕ) (hj : j < bound + 1) (jlo : k ≤ j)
      (next : states (j + 1) = cappedCutoffState bound q (j + 1)) :
      states j = cappedCutoffState bound q j := by
    have jl : lower ≤ j := lo.trans jlo
    rw [h.step j jl (by omega), next]
    exact (cappedCutoffState_step (bound := bound) (k := j) (by omega) (by omega) q).symm
  exact Nat.decreasingInduction' step hi (by simpa using h.base)

/-- Retrieve the actual positive count from a verified state at the larger truncation bound. -/
theorem CappedCutoffChecks.count_eq {n bound q lower : ℕ} {states : ℕ → Array ℕ}
    (h : CappedCutoffChecks bound q lower states) (positive : 0 < lower)
    (fit : n ≤ bound) {k : ℕ} (lo : lower ≤ k) (hi : k ≤ bound + 1) :
    (states k).getD n 0 = positiveCountDP n q k := by
  rw [h.state_eq positive lo hi, cappedCutoffState_count fit]

/-- Read the alphabet vector needed for one actual numerator from shared state sequences. -/
def readCappedAlphabet (n k : ℕ) (states : Fin n → ℕ → Array ℕ) : Array ℕ :=
  Array.ofFn fun q ↦ (states q k).getD n 0

theorem readCappedAlphabet_eq {n bound k : ℕ} (fit : n ≤ bound)
    (hk : 3 ≤ k) (hkn : k ≤ bound + 1) (states : Fin n → ℕ → Array ℕ)
    (checked : ∀ q, CappedCutoffChecks bound (q.val + 1) 3 (states q)) :
    readCappedAlphabet n k states = descentAlphabetTable n k := by
  unfold readCappedAlphabet descentAlphabetTable
  congr
  funext q
  exact (checked q).count_eq (by decide) fit hk hkn

/-- Use the original inverse binomial transform after reading the shared alphabet vector. -/
def readCappedNumerator (n k : ℕ) (states : Fin n → ℕ → Array ℕ) : List ℤ :=
  let letters := readCappedAlphabet n k states
  List.ofFn fun r : Fin n ↦ descentNumeratorCell n r.val letters

theorem representativeChecks_of_cappedCutoffs {n bound : ℕ} (hn : 3 ≤ n) (fit : n ≤ bound)
    (nodes : Array LongCycleFinite.Dyadic) (coeffs : Array (List ℤ))
    (states : Fin n → ℕ → Array ℕ)
    (checked : ∀ q, CappedCutoffChecks bound (q.val + 1) 3 (states q))
    (counts : ∀ i : Fin (lastRepresentative n - 2),
      readCappedNumerator n (i.val + 3) states = (0 :: coeffs.getD i.val []) ++ [0])
    (signs : ∀ i : Fin (lastRepresentative n - 2),
      negativeMeshOK (coeffs.getD i.val []) nodes = true) :
    RepresentativeChecks n nodes coeffs := by
  intro i
  have h := counts i
  have boundRep : lastRepresentative n ≤ n + 1 := by
    unfold lastRepresentative
    omega
  have hi := i.isLt
  rw [readCappedNumerator, readCappedAlphabet_eq fit (by omega) (by omega) states checked] at h
  exact ⟨h, signs i⟩

#print axioms cappedCutoffState_count
#print axioms CappedCutoffChecks.count_eq
#print axioms representativeChecks_of_cappedCutoffs

end LongCycleBounds.DescentNecklace
