import LongCycleBounds.DescentPackedCutoffs

/-! Extend the checked ordinary-descent mesh to cutoffs one and two. -/

namespace LongCycleBounds.DescentNecklace
open Polynomial LongCycleFinite

/-- Nodes are in increasing order. The original row is negative at the rightmost node. -/
def rawMeshNegative (nodes : Array LongCycleFinite.Dyadic) (i : ℕ) : Bool :=
  decide ((nodes.size - 1 - i) % 2 = 0)

/-- Strict signs of the original row at the existing shared dyadic nodes. -/
def RawSharedSigns (p : ℝ[X]) (nodes : Array LongCycleFinite.Dyadic) : Prop :=
  ∀ i : Fin nodes.size, if rawMeshNegative nodes i.val then
    p.eval (nodes[i.val]'i.isLt).value < 0
  else 0 < p.eval (nodes[i.val]'i.isLt).value

/-- The old representative data and both additional rows use the same nodes. -/
def LowerCutoffMeshCertificate (n : ℕ) : Prop :=
  ∃ nodes : Array LongCycleFinite.Dyadic, ∃ rows : Array (List ℤ),
    nodes.size = n - 2 ∧ RepresentativeChecks n nodes rows ∧
      ∀ k : ℕ, (k = 1 ∨ k = 2) →
        RawSharedSigns ((DescentTwoLetters.row n k).map (Int.castRingHom ℝ)) nodes

private def frozenNode : Array LongCycleFinite.Dyadic → ℕ → LongCycleFinite.Dyadic :=
  descentFrozenConst LongCycleBounds.DescentFiniteRoots LongCycleBounds.DescentNecklace.meshNode

private def quotientSign : ℕ → ℕ → Bool :=
  descentFrozenConst LongCycleBounds.DescentFiniteRoots LongCycleBounds.DescentNecklace.meshNegative

private theorem frozenNode_at (nodes : Array LongCycleFinite.Dyadic) (i : Fin nodes.size) :
    frozenNode nodes i.val = nodes[i.val]'i.isLt := by
  change nodes.getD i.val LongCycleFinite.Dyadic.zero = _
  simp [Array.getD, i.isLt]

private theorem rawMeshNegative_eq (nodes : Array LongCycleFinite.Dyadic) (i : ℕ) :
    rawMeshNegative nodes i = !quotientSign (nodes.size - 1) i := by
  change decide ((nodes.size - 1 - i) % 2 = 0) =
    !decide ((nodes.size - 1 - i) % 2 = 1)
  by_cases even : (nodes.size - 1 - i) % 2 = 0
  · simp [even]
  · have odd : (nodes.size - 1 - i) % 2 = 1 := by omega
    simp [odd]

theorem rawMeshNegative_succ {nodes : Array LongCycleFinite.Dyadic} {i : ℕ}
    (fit : i + 1 < nodes.size) :
    rawMeshNegative nodes (i + 1) = !rawMeshNegative nodes i := by
  unfold rawMeshNegative
  by_cases even : (nodes.size - 1 - i) % 2 = 0
  · have odd : (nodes.size - 1 - (i + 1)) % 2 ≠ 0 := by omega
    simp [even, odd]
  · have next : (nodes.size - 1 - (i + 1)) % 2 = 0 := by omega
    simp [even, next]

theorem rawMeshNegative_last (nodes : Array LongCycleFinite.Dyadic) :
    rawMeshNegative nodes (nodes.size - 1) = true := by
  simp [rawMeshNegative]

/-- The factored quotient check entails the original strict signs at each shared node. -/
theorem rawSharedSigns_X_mul {cs : List ℤ} {nodes : Array LongCycleFinite.Dyadic}
    (h : negativeMeshOK cs nodes = true) : RawSharedSigns (X * ofCoeffs cs) nodes := by
  have all :
      (List.range nodes.size).all (fun i ↦
        (frozenNode nodes i).less LongCycleFinite.Dyadic.zero &&
          K3.naturalSign (quotientSign (nodes.size - 1) i) cs (frozenNode nodes i)) = true :=
    (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).2
  intro i
  obtain ⟨neg, checked⟩ := Bool.and_eq_true_iff.mp
    (List.all_eq_true.mp all i.val (List.mem_range.mpr i.isLt))
  have xneg : (nodes[i.val]'i.isLt).value < 0 := by
    simpa only [frozenNode_at nodes i, LongCycleFinite.Dyadic.value_zero] using
      (LongCycleFinite.Dyadic.less_iff _ _).mp neg
  have signed := K3.naturalSign_sound checked
  rw [frozenNode_at nodes i] at signed
  rw [rawMeshNegative_eq, eval_mul, eval_X]
  cases bit : quotientSign (nodes.size - 1) i.val
  · simp only [bit, Bool.false_eq_true, if_false] at signed
    simpa using mul_neg_of_neg_of_pos xneg signed
  · simp only [bit, if_true] at signed
    simpa using mul_pos_of_neg_of_neg xneg signed

theorem rawSharedSigns_of_representativeChecks {n k : ℕ} (hn : 3 ≤ n)
    (hk : 3 ≤ k) (kn : k ≤ n) {nodes : Array LongCycleFinite.Dyadic}
    {rows : Array (List ℤ)} (checked : RepresentativeChecks n nodes rows) :
    RawSharedSigns ((DescentTwoLetters.row n k).map (Int.castRingHom ℝ)) nodes := by
  let cutoff := min k (lastRepresentative n)
  have cutLower : 3 ≤ cutoff := le_min hk (le_max_left ..)
  let i : Fin (lastRepresentative n - 2) := ⟨cutoff - 3, by
    have fit : cutoff ≤ lastRepresentative n := min_le_right ..
    omega⟩
  have hi : i.val + 3 = cutoff := Nat.sub_add_cancel cutLower
  obtain ⟨counts, signs⟩ := checked i
  rw [hi] at counts
  rw [row_eq_representative hk kn, row_eq_of_checkedCoeffs (by omega) counts]
  exact rawSharedSigns_X_mul signs

theorem representativeMesh_geometry {n : ℕ} {nodes : Array LongCycleFinite.Dyadic}
    {rows : Array (List ℤ)} (checked : RepresentativeChecks n nodes rows) :
    (∀ i : Fin nodes.size, (nodes[i.val]'i.isLt).value < 0) ∧
      StrictMono (fun i : Fin nodes.size ↦ (nodes[i.val]'i.isLt).value) := by
  have rep : 3 ≤ lastRepresentative n := le_max_left ..
  let i : Fin (lastRepresentative n - 2) := ⟨0, by omega⟩
  have mesh := (checked i).2
  let a (j : ℕ) := (frozenNode nodes j).value
  have adj (j : ℕ) (fit : j < nodes.size - 1) : a j < a (j + 1) :=
    (LongCycleFinite.Dyadic.less_iff _ _).mp
      (List.all_eq_true.mp (Bool.and_eq_true_iff.mp mesh).2 j (List.mem_range.mpr fit))
  constructor
  · intro j
    have check := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp mesh).1).2
    have sign := (Bool.and_eq_true_iff.mp
      (List.all_eq_true.mp check j.val (List.mem_range.mpr j.isLt))).1
    have value : (frozenNode nodes j.val).value < 0 := by
      simpa only [frozenNode, LongCycleFinite.Dyadic.value_zero] using
        (LongCycleFinite.Dyadic.less_iff _ _).mp sign
    rwa [frozenNode_at nodes j] at value
  · intro j l order
    have lfit : l.val ≤ nodes.size - 1 := by have h := l.isLt; omega
    have jl : j.val + 1 ≤ l.val := order
    have jfit : j.val < nodes.size - 1 := by omega
    let mono := descentFrozenConst LongCycleBounds.DescentFiniteRoots
      LongCycleBounds.DescentNecklace.adjacentMono
    have compare : a (j.val + 1) ≤ a l.val := mono a adj jl lfit
    simpa only [a, frozenNode_at nodes j, frozenNode_at nodes l] using
      (adj j.val jfit).trans_le compare

/-- Check an unfactored integer row at the old nodes. -/
def rawMeshOK (coefficients : List ℤ) (nodes : Array LongCycleFinite.Dyadic) : Bool :=
  (List.range nodes.size).all fun i ↦
    K3.naturalSign (rawMeshNegative nodes i) coefficients (frozenNode nodes i)

theorem rawSharedSigns_of_numerator {n k : ℕ} (hn : 0 < n)
    {coefficients : List ℤ} {nodes : Array LongCycleFinite.Dyadic}
    (value : descentRowDP n k = coefficients)
    (signs : rawMeshOK coefficients nodes = true) :
    RawSharedSigns ((DescentTwoLetters.row n k).map (Int.castRingHom ℝ)) nodes := by
  rw [← ofCoeffs_descentRowDP hn k, value]
  intro i
  have all := List.all_eq_true.mp signs i.val (List.mem_range.mpr i.isLt)
  have h := K3.naturalSign_sound all
  simpa only [frozenNode_at nodes i] using h

/-- Continue the verified descending sweep by its two missing factors. -/
def extendCutoffCode (bound alphabet : ℕ) (code : ℕ → ℕ) (k : ℕ) : ℕ :=
  let base := cutoffRadix bound alphabet
  let two := codedCutoffStep base bound 2 (primitiveCount 2 alphabet) (code 3)
  if k = 1 then codedCutoffStep base bound 1 (primitiveCount 1 alphabet) two
  else if k = 2 then two
  else code k

theorem PackedCutoffChecks.extend_one {bound alphabet : ℕ} {code : ℕ → ℕ}
    (hb : 3 ≤ bound) (h : PackedCutoffChecks bound alphabet 3 code) :
    PackedCutoffChecks bound alphabet 1 (extendCutoffCode bound alphabet code) := by
  constructor
  · simpa only [extendCutoffCode, if_neg (show bound + 1 ≠ 1 by omega),
      if_neg (show bound + 1 ≠ 2 by omega)] using h.base
  · intro k lo hi
    by_cases one : k = 1
    · subst k
      rfl
    by_cases two : k = 2
    · subst k
      rfl
    have three : 3 ≤ k := by omega
    simpa only [extendCutoffCode, if_neg one, if_neg two,
      if_neg (show k + 1 ≠ 1 by omega), if_neg (show k + 1 ≠ 2 by omega)] using
      h.step k three hi

/-- Compute a low-cutoff row with the two extra packed steps and the usual inversion. -/
def lowerCutoffNumerator (bound n k : ℕ) (codes : Fin n → ℕ → ℕ) : List ℤ :=
  readPackedNumerator bound n k fun i ↦ extendCutoffCode bound (i.val + 1) (codes i)

theorem lowerCutoffNumerator_eq {bound n k : ℕ} (hb : 3 ≤ bound) (fit : n ≤ bound)
    (hk : 1 ≤ k) (hi : k ≤ bound + 1) (codes : Fin n → ℕ → ℕ)
    (checks : ∀ i, PackedCutoffChecks bound (i.val + 1) 3 (codes i)) :
    lowerCutoffNumerator bound n k codes = descentRowDP n k := by
  have alphabet :
      readPackedAlphabet bound n k (fun i ↦ extendCutoffCode bound (i.val + 1) (codes i)) =
        descentAlphabetTable n k := by
    unfold readPackedAlphabet descentAlphabetTable
    congr
    funext i
    exact ((checks i).extend_one hb).count_eq (Nat.succ_pos _) (by decide) fit hk hi
  simp [lowerCutoffNumerator, readPackedNumerator, alphabet, descentRowDP]

#print axioms rawSharedSigns_of_representativeChecks
#print axioms representativeMesh_geometry
#print axioms rawSharedSigns_of_numerator
#print axioms lowerCutoffNumerator_eq

end LongCycleBounds.DescentNecklace
