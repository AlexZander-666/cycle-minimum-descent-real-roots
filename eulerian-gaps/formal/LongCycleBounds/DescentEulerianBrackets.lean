import LongCycleBounds.DescentFiniteBlocks

/-! Exact signed windows for the descent quotient and the next-degree Eulerian row. -/

namespace LongCycleBounds.DescentNecklace.EulerianBrackets

open Polynomial LongCycles LongCycleFinite

private def left (ws : List Window) (i : ℕ) : LongCycleFinite.Dyadic := (ws[i]?.getD default).left

private def right (ws : List Window) (i : ℕ) : LongCycleFinite.Dyadic := (ws[i]?.getD default).right

private def gapLeft (outer : LongCycleFinite.Dyadic) (ws : List Window) : ℕ → LongCycleFinite.Dyadic
  | 0 => outer
  | i + 1 => right ws i

private def gapRight (ws : List Window) (i : ℕ) : LongCycleFinite.Dyadic :=
  if i = ws.length then LongCycleFinite.Dyadic.zero else left ws i

/-- The Eulerian row is checked once for a whole family of lower rows. -/
def upperOK (q : List ℤ) (outer : LongCycleFinite.Dyadic) (ws : List Window) : Bool :=
  decide (q.length = ws.length + 2) && orderOK outer ws &&
    (List.range (ws.length + 1)).all fun i ↦
      K3.naturalSign (negativeSign (ws.length + 1 - i)) q (gapLeft outer ws i) &&
      K3.naturalSign (!negativeSign (ws.length + 1 - i)) q (gapRight ws i)

/-- Each representative descent row is checked at the ends of the lower windows. -/
def lowerOK (p : List ℤ) (ws : List Window) : Bool :=
  decide (p.length = ws.length + 1) &&
    (List.range ws.length).all fun i ↦
      K3.naturalSign (negativeSign (ws.length - i)) p (left ws i) &&
      K3.naturalSign (!negativeSign (ws.length - i)) p (right ws i)

private theorem left_at (ws : List Window) (i : Fin ws.length) :
    left ws i.val = (ws.get i).left := by simp [left, i.isLt]

private theorem right_at (ws : List Window) (i : Fin ws.length) :
    right ws i.val = (ws.get i).right := by simp [right, i.isLt]

private theorem gap_left_at (outer : LongCycleFinite.Dyadic) (ws : List Window) (i : Fin (ws.length + 1)) :
    (gapLeft outer ws i.val).value =
      Fin.cases outer.value (fun j ↦ (ws.get j).right.value) i := by
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · rfl
  · simpa only [Fin.val_succ, Fin.cases_succ, gapLeft] using
      congrArg LongCycleFinite.Dyadic.value (right_at ws j)

private theorem gap_right_at (ws : List Window) (i : Fin (ws.length + 1)) :
    (gapRight ws i.val).value =
      Fin.lastCases 0 (fun j ↦ (ws.get j).left.value) i := by
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simp [gapRight]
  · simpa only [Fin.lastCases_castSucc, Fin.val_castSucc, gapRight, if_neg j.isLt.ne] using
      congrArg LongCycleFinite.Dyadic.value (left_at ws j)

private theorem opposite_signs {b : Bool} {u v : ℝ} (hu : HasSign b u)
    (hv : HasSign (!b) v) : u * v < 0 := by
  cases b
  · exact mul_neg_of_pos_of_neg hu hv
  · exact mul_neg_of_neg_of_pos hu hv

/-- Checked windows and gaps give strict interlacing with all roots accounted for. -/
theorem checked_interlacing {p q : List ℤ} {outer : LongCycleFinite.Dyadic} {ws : List Window}
    (nonempty : 0 < ws.length) (upper : upperOK q outer ws = true)
    (lower : lowerOK p ws = true) :
    StrictNegativeInterlacing (ofCoeffs p) (ofCoeffs q) ws.length := by
  obtain ⟨⟨lq, ord⟩, uq⟩ :
      (q.length = ws.length + 2 ∧ orderOK outer ws = true) ∧ _ := by
    simpa only [upperOK, Bool.and_eq_true_iff, decide_eq_true_eq] using upper
  obtain ⟨lp, cp⟩ : p.length = ws.length + 1 ∧ _ := by
    simpa only [lowerOK, Bool.and_eq_true_iff, decide_eq_true_eq] using lower
  have crossing (i : Fin ws.length) :
      (ofCoeffs p).eval (ws.get i).left.value *
        (ofCoeffs p).eval (ws.get i).right.value < 0 := by
    obtain ⟨lo, hi⟩ := Bool.and_eq_true_iff.mp (List.all_eq_true.mp cp i.val
      (List.mem_range.mpr i.isLt))
    simpa only [left_at ws i, right_at ws i] using
      opposite_signs (K3.naturalSign_sound lo) (K3.naturalSign_sound hi)
  have gap (i : Fin (ws.length + 1)) :
      (ofCoeffs q).eval (Fin.cases outer.value (fun j ↦ (ws.get j).right.value) i) *
        (ofCoeffs q).eval (Fin.lastCases 0 (fun j ↦ (ws.get j).left.value) i) < 0 := by
    obtain ⟨lo, hi⟩ := Bool.and_eq_true_iff.mp (List.all_eq_true.mp uq i.val
      (List.mem_range.mpr i.isLt))
    simpa only [gap_left_at outer ws i, gap_right_at ws i] using
      opposite_signs (K3.naturalSign_sound lo) (K3.naturalSign_sound hi)
  have hp : ofCoeffs p ≠ 0 := by
    intro eq
    simpa [eq] using crossing ⟨0, nonempty⟩
  have hq : ofCoeffs q ≠ 0 := by
    intro eq
    simpa [eq] using gap 0
  have boundP : (ofCoeffs p).natDegree ≤ ws.length :=
    (ofCoeffs_degree_le p).trans (by rw [lp]; omega)
  have boundQ : (ofCoeffs q).natDegree ≤ ws.length + 1 :=
    (ofCoeffs_degree_le q).trans (by rw [lq]; omega)
  obtain ⟨out, windows, order⟩ := orderOK_between ord
  exact interlacing_of_brackets hp hq boundP boundQ outer.value
    (fun i ↦ (ws.get i).left.value) (fun i ↦ (ws.get i).right.value)
    out windows order crossing gap

/-- The mapped integer descent row is divided by its original zero factor. -/
noncomputable def originalQuotient (n k : ℕ) : Polynomial ℝ :=
  ((DescentTwoLetters.row n k).map (Int.castRingHom ℝ)).divX

private theorem quotient_readout {n k : ℕ} (hn : 0 < n) {cs : List ℤ}
    (checked : descentRowDP n k = (0 :: cs) ++ [0]) :
    originalQuotient n k = ofCoeffs cs := by
  unfold originalQuotient
  rw [row_eq_of_checkedCoeffs hn checked]
  ext i
  rw [coeff_divX, coeff_X_mul]

/-- Use previously certified true quotient coefficients and newly checked signs in shared gaps. -/
theorem original_of_representatives {n : ℕ} (hn : 6 ≤ n)
    {nodes : Array LongCycleFinite.Dyadic} {rows : Array (List ℤ)}
    (original : RepresentativeChecks n nodes rows)
    {outer : LongCycleFinite.Dyadic} {ws : List Window} (size : ws.length = n - 3)
    (upper : upperOK (descentCoeffs (n - 1)) outer ws = true)
    (lower : ∀ i : Fin (lastRepresentative n - 2), lowerOK (rows.getD i.val []) ws = true)
    {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ n) :
    StrictNegativeInterlacing (originalQuotient n k) (eulerian (n - 1)) (n - 3) := by
  let cutoff := min k (lastRepresentative n)
  have low : 3 ≤ cutoff := le_min hk (le_max_left ..)
  let i : Fin (lastRepresentative n - 2) := ⟨cutoff - 3, by
    have le : cutoff ≤ lastRepresentative n := min_le_right ..
    omega⟩
  have eq : i.val + 3 = cutoff := Nat.sub_add_cancel low
  have counts := (original i).1
  rw [eq] at counts
  have rowEq : originalQuotient n k = originalQuotient n cutoff := by
    unfold originalQuotient
    rw [row_eq_representative hk kn]
  rw [rowEq, quotient_readout (by omega : 0 < n) counts]
  have h := checked_interlacing (by omega : 0 < ws.length) upper (lower i)
  rwa [ofCoeffs_descentCoeffs, size] at h

#print axioms checked_interlacing
#print axioms original_of_representatives

end LongCycleBounds.DescentNecklace.EulerianBrackets
