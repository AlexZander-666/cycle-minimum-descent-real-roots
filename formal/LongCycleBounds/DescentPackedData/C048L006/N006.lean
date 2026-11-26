import LongCycleBounds.DescentPackedData.C048L006

/-! Size 6, reading its coefficients from the degree-48 alphabet tables. -/

namespace LongCycleBounds.DescentNecklace.Packed.C048L006.N006

private def nodes : Array LongCycleFinite.Dyadic :=
#[
  ⟨-12842623, 20⟩,
  ⟨-8591518, 22⟩,
  ⟨-16380980, 25⟩,
  ⟨-10958625, 27⟩
]

private def rows : Array (List ℤ) :=
#[
  [12, 68, 68, 12],
  [9, 53, 47, 11]
]

private def alphabets : Array (Array ℕ) :=
#[
  #[0, 12, 152, 880, 3400, 10220],
  #[0, 9, 116, 670, 2580, 7735]
]

private def codes (q : Fin 6) : ℕ → ℕ := C048L006.codes ⟨q.val, by omega⟩

set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 50000000

private theorem alphabet000 :
    readPackedAlphabet 48 6 3 codes = alphabets.getD 0 #[] := by
  decide +kernel

private theorem alphabet001 :
    readPackedAlphabet 48 6 4 codes = alphabets.getD 1 #[] := by
  decide +kernel

private theorem alphabetChecked (i : Fin (lastRepresentative 6 - 2)) :
    readPackedAlphabet 48 6 (i.val + 3) codes = alphabets.getD i.val #[] := by
  obtain ⟨i, fits⟩ := i
  change i < 2 at fits
  interval_cases i
  · exact alphabet000
  · exact alphabet001

private theorem count000 :
    (List.ofFn fun r : Fin 6 ↦ descentNumeratorCell 6 r.val (alphabets.getD 0 #[])) =
      (0 :: rows.getD 0 []) ++ [0] := by
  decide +kernel

private theorem count001 :
    (List.ofFn fun r : Fin 6 ↦ descentNumeratorCell 6 r.val (alphabets.getD 1 #[])) =
      (0 :: rows.getD 1 []) ++ [0] := by
  decide +kernel

private theorem counts (i : Fin (lastRepresentative 6 - 2)) :
    readPackedNumerator 48 6 (i.val + 3) codes =
      (0 :: rows.getD i.val []) ++ [0] := by
  rw [readPackedNumerator, alphabetChecked i]
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

private theorem signs (i : Fin (lastRepresentative 6 - 2)) :
    negativeMeshOK (rows.getD i.val []) nodes = true := by
  obtain ⟨i, fits⟩ := i
  change i < 2 at fits
  interval_cases i
  · exact sign000
  · exact sign001

private theorem dataChecks : RepresentativeChecks 6 nodes rows :=
  representativeChecks_of_packedCutoffs (by decide) (by decide) nodes rows codes
    (fun q ↦ C048L006.checked ⟨q.val, by omega⟩) counts signs

theorem finite_certificate :
    ∃ nodes : Array LongCycleFinite.Dyadic, ∃ rows : Array (List ℤ),
      nodes.size = 6 - 2 ∧ RepresentativeChecks 6 nodes rows :=
  ⟨nodes, rows, by decide, dataChecks⟩

theorem original_roots {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 6) :
    SimpleDescentRootPattern 6 k :=
  simpleDescentRoots_of_representativeChecks (by decide) (by decide) dataChecks hk kn

#print axioms finite_certificate
#print axioms original_roots

end LongCycleBounds.DescentNecklace.Packed.C048L006.N006
