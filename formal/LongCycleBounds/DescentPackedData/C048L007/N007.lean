import LongCycleBounds.DescentPackedData.C048L007
import LongCycleBounds.DescentPackedInversion

/-! Size 7, reading its coefficients from the degree-48 alphabet tables. -/

namespace LongCycleBounds.DescentNecklace.Packed.C048L007.N007

private def nodes : Array LongCycleFinite.Dyadic :=
#[
  ⟨-12132387, 19⟩,
  ⟨-15410016, 22⟩,
  ⟨-16777216, 24⟩,
  ⟨-9132858, 25⟩,
  ⟨-11600148, 28⟩
]

private def rows : Array (List ℤ) :=
#[
  [24, 264, 564, 264, 24],
  [18, 168, 348, 168, 18]
]

private def alphabets : Array (Array ℕ) :=
#[
  #[0, 24, 456, 3540, 17160, 62040, 183504],
  #[0, 18, 312, 2340, 11160, 39990, 117648]
]

private def codes (q : Fin 7) : ℕ → ℕ := C048L007.codes ⟨q.val, by omega⟩

set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 50000000

private theorem alphabet000 :
    readPackedAlphabet 48 7 3 codes = alphabets.getD 0 #[] := by
  decide +kernel

private theorem alphabet001 :
    readPackedAlphabet 48 7 4 codes = alphabets.getD 1 #[] := by
  decide +kernel

private theorem alphabetChecked (i : Fin (lastRepresentative 7 - 2)) :
    readPackedAlphabet 48 7 (i.val + 3) codes = alphabets.getD i.val #[] := by
  obtain ⟨i, fits⟩ := i
  change i < 2 at fits
  interval_cases i
  · exact alphabet000
  · exact alphabet001

private theorem count000 :
    packedInversion 7 (alphabets.getD 0 #[]) =
      (0 :: rows.getD 0 []) ++ [0] := by
  decide +kernel

private theorem count001 :
    packedInversion 7 (alphabets.getD 1 #[]) =
      (0 :: rows.getD 1 []) ++ [0] := by
  decide +kernel

private theorem counts (i : Fin (lastRepresentative 7 - 2)) :
    readPackedNumerator 48 7 (i.val + 3) codes =
      (0 :: rows.getD i.val []) ++ [0] := by
  rw [readPackedNumerator, alphabetChecked i, ← packedInversion_eq]
  obtain ⟨i, fits⟩ := i
  change i < 2 at fits
  interval_cases i
  · exact count000
  · exact count001

private theorem sign000 :
    negativeMeshOK (rows.getD 0 []) nodes = true := by
  decide +kernel

private theorem sign001 :
    negativeMeshOK (rows.getD 1 []) nodes = true := by
  decide +kernel

private theorem signs (i : Fin (lastRepresentative 7 - 2)) :
    negativeMeshOK (rows.getD i.val []) nodes = true := by
  obtain ⟨i, fits⟩ := i
  change i < 2 at fits
  interval_cases i
  · exact sign000
  · exact sign001

private theorem dataChecks : RepresentativeChecks 7 nodes rows :=
  representativeChecks_of_packedCutoffs (by decide) (by decide) nodes rows codes
    (fun q ↦ C048L007.checked ⟨q.val, by omega⟩) counts signs

theorem finite_certificate :
    ∃ nodes : Array LongCycleFinite.Dyadic, ∃ rows : Array (List ℤ),
      nodes.size = 7 - 2 ∧ RepresentativeChecks 7 nodes rows :=
  ⟨nodes, rows, by decide, dataChecks⟩

theorem original_roots {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 7) :
    SimpleDescentRootPattern 7 k :=
  simpleDescentRoots_of_representativeChecks (by decide) (by decide) dataChecks hk kn

#print axioms finite_certificate
#print axioms original_roots

end LongCycleBounds.DescentNecklace.Packed.C048L007.N007
