import LongCycleBounds.DescentFiniteBlocks

/-! Shared descending-cutoff tables for ordinary descent certificates. -/

namespace LongCycleBounds.DescentNecklace

private theorem countTable_drop_cutoff (bound q cutoff start len : ℕ) :
    countTable bound (List.ofFn fun i : Fin len ↦
      (start + i.val, if start + i.val < cutoff then 0 else primitiveCount (start + i.val) q)) =
    countTable bound ((List.ofFn fun i : Fin len ↦
      (start + i.val, primitiveCount (start + i.val) q)).drop (cutoff - start)) := by
  induction len generalizing start with
  | zero => simp
  | succ len ih =>
    by_cases h : start < cutoff
    · have drop : cutoff - start = (cutoff - (start + 1)) + 1 := by omega
      rw [drop, List.ofFn_succ, List.ofFn_succ, List.drop_succ_cons]
      simp only [Fin.val_zero, Nat.add_zero, countTable, List.foldr_cons]
      change convolveTable bound start (if start < cutoff then 0 else primitiveCount start q)
        _ = _
      rw [if_pos h]
      change countTable bound _ = countTable bound _
      have shift (i : Fin len) : start + i.succ.val = (start + 1) + i.val := by
        simp only [Fin.val_succ]
        omega
      simp only [shift]
      exact ih (start + 1)
    · have drop : cutoff - start = 0 := by omega
      have above (i : Fin (len + 1)) : ¬start + i.val < cutoff := by omega
      simp only [drop, List.drop_zero, if_neg (above _)]

/-- The coefficient of total weight `n` at each positive cutoff, from one downward scan. -/
def alphabetCutoffSweep (n q : ℕ) : Array ℕ :=
  let factors := List.ofFn fun i : Fin n ↦ (i.val + 1, primitiveCount (i.val + 1) q)
  ((factors.scanr (fun pair old ↦ convolveTable n pair.1 pair.2 old) (initialTable n)).map
    (fun table ↦ table.getD n 0)).toArray

theorem alphabetCutoffSweep_at {n k : ℕ} (kn : k ≤ n + 1) (q : ℕ) :
    (alphabetCutoffSweep n q).getD (k - 1) 0 = positiveCountDP n q k := by
  unfold alphabetCutoffSweep positiveCountDP
  let factors := List.ofFn fun i : Fin n ↦ (i.val + 1, primitiveCount (i.val + 1) q)
  let update (pair : ℕ × ℕ) := convolveTable n pair.1 pair.2
  have hi : k - 1 < factors.length + 1 := by simp [factors]; omega
  change (((factors.scanr update (initialTable n)).map
    (fun table ↦ table.getD n 0)).toArray).getD (k - 1) 0 = _
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map,
    List.getElem?_scanr_of_lt hi]
  simp only [Option.map_some, Option.getD_some]
  simpa only [positiveFactors, Nat.add_comm 1, countTable, factors, update] using
    congrArg (fun table : Array ℕ ↦ table.getD n 0)
      (countTable_drop_cutoff n q k 1 n).symm

/-- One scan suffices per alphabet size, regardless of the number of cutoff representatives. -/
def alphabetSweeps (n : ℕ) : Array (Array ℕ) :=
  Array.ofFn fun i : Fin n ↦ alphabetCutoffSweep n (i.val + 1)

/-- Read one cutoff's alphabet counts across the shared table. -/
def readAlphabet (n k : ℕ) (sweeps : Array (Array ℕ)) : Array ℕ :=
  Array.ofFn fun i : Fin n ↦ (sweeps.getD i.val #[]).getD (k - 1) 0

theorem readAlphabet_eq {n k : ℕ} (kn : k ≤ n + 1) :
    readAlphabet n k (alphabetSweeps n) = descentAlphabetTable n k := by
  unfold readAlphabet alphabetSweeps descentAlphabetTable
  congr 1
  ext i
  simpa using alphabetCutoffSweep_at kn (i.val + 1)

/-- Invert a complete alphabet row with the existing signed binomial transform. -/
def readNumerator (n k : ℕ) (sweeps : Array (Array ℕ)) : List ℤ :=
  let letters := readAlphabet n k sweeps
  List.ofFn fun r : Fin n ↦ descentNumeratorCell n r.val letters

theorem readNumerator_eq {n k : ℕ} (kn : k ≤ n + 1) :
    readNumerator n k (alphabetSweeps n) = descentRowDP n k := by
  simp [readNumerator, readAlphabet_eq kn, descentRowDP]

/-- Match the shared computation to every supplied representative numerator before root checks. -/
def sharedNumerators (n : ℕ) : Array (List ℤ) :=
  let sweeps := alphabetSweeps n
  Array.ofFn fun i : Fin (lastRepresentative n - 2) ↦
    readNumerator n (i.val + 3) sweeps

theorem sharedNumerators_at {n : ℕ} (hn : 3 ≤ n) (i : Fin (lastRepresentative n - 2)) :
    (sharedNumerators n).getD i.val [] = descentRowDP n (i.val + 3) := by
  have bound : lastRepresentative n ≤ n + 1 := by
    unfold lastRepresentative
    omega
  have i_lt := i.isLt
  simpa [sharedNumerators] using readNumerator_eq (k := i.val + 3) (by omega)

/-- Use the checked coefficient table and independent endpoint checks to recover the original rows. -/
theorem representativeChecks_of_shared {n : ℕ} (hn : 3 ≤ n) (nodes : Array LongCycleFinite.Dyadic)
    (coeffs : Array (List ℤ))
    (counts : sharedNumerators n = coeffs.map (fun cs ↦ (0 :: cs) ++ [0]))
    (signs : ∀ i : Fin (lastRepresentative n - 2),
      negativeMeshOK (coeffs.getD i.val []) nodes = true) :
    RepresentativeChecks n nodes coeffs := by
  intro i
  refine ⟨?_, signs i⟩
  rw [← sharedNumerators_at hn i, counts]
  have length : coeffs.size = lastRepresentative n - 2 := by
    simpa [sharedNumerators] using congrArg Array.size counts.symm
  have hi : i.val < coeffs.size := by simp [length]
  simp [Array.getD, hi]

#print axioms alphabetCutoffSweep_at
#print axioms readNumerator_eq
#print axioms representativeChecks_of_shared

end LongCycleBounds.DescentNecklace
