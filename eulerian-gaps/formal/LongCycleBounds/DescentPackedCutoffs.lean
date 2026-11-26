import LongCycleBounds.DescentCappedCutoffs
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Data.ZMod.Basic

/-! Radix arithmetic for the positive necklace product at a fixed degree cap. -/

namespace LongCycleBounds.DescentNecklace

open Finset Polynomial

private theorem positiveCountDP_le_words {n q k : ℕ} (hn : 0 < n) :
    positiveCountDP n q k ≤ q ^ n := by
  have card : Nat.card (AllowedCompatible n q k) = positiveCountDP n q k := by
    have h := card_allowedCompatible_eq_letters hn q k
    rw [letters_eq_positiveCountDP hn q k] at h
    exact_mod_cast h
  rw [← card]
  let forget (x : AllowedCompatible n q k) := (wordEquiv n q).symm x.val
  have inj : Function.Injective forget := fun _ _ e ↦
    Subtype.ext ((wordEquiv n q).symm.injective e)
  simpa [Nat.card_fun] using Nat.card_le_card_of_injective forget inj

/-- The base is strictly larger than every retained coefficient for this alphabet. -/
def cutoffRadix (bound q : ℕ) : ℕ := q ^ bound + 1

private theorem eval_divX_split (base : ℕ) (p : ℕ[X]) :
    p.eval base = p.coeff 0 + (divX p).eval base * base := by
  conv_lhs => rw [← divX_mul_X_add p]
  simp [add_comm]

private theorem eval_radix_digit (base : ℕ) (positive : 0 < base) (p : ℕ[X]) (d : ℕ)
    (bounded : ∀ i ≤ d, p.coeff i < base) :
    p.eval base / base ^ d % base = p.coeff d := by
  induction d generalizing p with
  | zero =>
    rw [pow_zero, Nat.div_one, eval_divX_split, Nat.add_mul_mod_self_right,
      Nat.mod_eq_of_lt (bounded 0 le_rfl)]
  | succ d ih =>
    have div : p.eval base / base = (divX p).eval base := by
      rw [eval_divX_split, Nat.add_comm, Nat.mul_comm ((divX p).eval base), Nat.mul_add_div positive,
        Nat.div_eq_of_lt (bounded 0 (Nat.zero_le _)), Nat.add_zero]
    rw [pow_succ, Nat.mul_comm (base ^ d), ← Nat.div_div_eq_div_mul, div,
      ih (divX p) (fun i hi ↦ by
        rw [coeff_divX]
        exact bounded _ (Nat.succ_le_succ hi)), coeff_divX]

/-- Taking the remainder modulo the cap power leaves every retained radix digit unchanged. -/
private theorem mod_radix_digit (base : ℕ) {n bound : ℕ}
    (fit : n ≤ bound) (z : ℕ) :
    (z % base ^ (bound + 1)) / base ^ n % base = z / base ^ n % base := by
  obtain ⟨m, eq⟩ := Nat.exists_eq_add_of_le fit
  have hbound : bound + 1 = n + 1 + m := by omega
  have dp : base ^ (n + 1) ∣ base ^ (bound + 1) := by
    rw [hbound, pow_add base (n + 1) m]
    exact Nat.dvd_mul_right _ _
  have same : z % base ^ (bound + 1) % base ^ (n + 1) = z % base ^ (n + 1) :=
    Nat.mod_mod_of_dvd _ dp
  rw [pow_succ base n] at same
  have left := congrArg (fun x : ℕ ↦ x / base ^ n) same
  simpa only [Nat.mod_mul_right_div_self] using left

private noncomputable def productAt (bound q cutoff : ℕ) : ℕ[X] :=
  let factors := List.ofFn fun j : Fin bound ↦ (j.val + 1, primitiveCount (j.val + 1) q)
  (((factors.drop (cutoff - 1)).map fun w ↦ lengthFactor bound w.1 w.2)).prod

private theorem productAt_coeff {bound n : ℕ} (fit : n ≤ bound) (q k : ℕ) :
    (productAt bound q k).coeff n = positiveCountDP n q k := by
  rw [← cappedCutoffState_count fit q k]
  unfold productAt cappedCutoffState
  apply (countTable_correct bound _ ?_ fit).symm
  intro w hw
  have mem := List.mem_of_mem_drop hw
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp mem
  exact Nat.succ_pos i.val

private theorem productAt_coeff_lt {bound q k n : ℕ} (hq : 0 < q) (fit : n ≤ bound) :
    (productAt bound q k).coeff n < cutoffRadix bound q := by
  rw [productAt_coeff fit, cutoffRadix, Nat.lt_succ_iff]
  by_cases zero : n = 0
  · subst n
    simpa [positiveCountDP, positiveFactors, countTable, initialTable] using
      Nat.one_le_pow bound q hq
  exact (positiveCountDP_le_words (Nat.pos_of_ne_zero zero)).trans
    (Nat.pow_le_pow_right hq fit)

/-- Radix representation of the true truncated suffix product. -/
private noncomputable def trueCutoffCode (bound q k : ℕ) : ℕ :=
  let base := cutoffRadix bound q
  (productAt bound q k).eval base % base ^ (bound + 1)

private theorem trueCutoffCode_digit {bound q n : ℕ} (hq : 0 < q) (fit : n ≤ bound) (k : ℕ) :
    trueCutoffCode bound q k / cutoffRadix bound q ^ n % cutoffRadix bound q =
      positiveCountDP n q k := by
  have pos : 0 < cutoffRadix bound q := by simp [cutoffRadix]
  unfold trueCutoffCode
  rw [mod_radix_digit _ fit, eval_radix_digit _ pos _ _
    (fun i hi ↦ productAt_coeff_lt hq (hi.trans fit)), productAt_coeff fit]

/-- Only monomials that affect the retained degree range are needed in the coded factor. -/
def codedLengthFactor (base bound weight M : ℕ) : ℕ :=
  ((List.range (bound / weight + 1)).map fun j ↦
    multiplicityWeight M j * base ^ (weight * j)).sum

private theorem codedLengthFactor_cast (base bound : ℕ) {weight : ℕ} (hw : 0 < weight) (M : ℕ) :
    ((codedLengthFactor base bound weight M : ℕ) : ZMod (base ^ (bound + 1))) =
      (((lengthFactor bound weight M).eval base : ℕ) : ZMod (base ^ (bound + 1))) := by
  classical
  unfold codedLengthFactor lengthFactor
  rw [← List.sum_toFinset _ List.nodup_range, List.toFinset_range, Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_monomial]
  rw [Fin.sum_univ_eq_sum_range (fun i ↦ multiplicityWeight M i * base ^ (weight * i))]
  simp only [Nat.cast_sum]
  apply sum_subset (range_mono (Nat.succ_le_succ (Nat.div_le_self _ _)))
  intro a _ notIn
  have greater : bound + 1 ≤ weight * a := by
    by_contra! small
    have fits : weight * a ≤ bound := Nat.lt_succ_iff.mp small
    exact notIn <| mem_range.mpr <| Nat.lt_succ_of_le <|
      (Nat.le_div_iff_mul_le hw).mpr (by simpa [Nat.mul_comm] using fits)
  have disappears : (((base ^ (weight * a) : ℕ) : ZMod (base ^ (bound + 1)))) = 0 := by
    rw [ZMod.natCast_eq_zero_iff]
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le greater
    rw [hm, pow_add base (bound + 1) m]
    exact Nat.dvd_mul_right _ _
  rw [Nat.cast_mul, disappears, mul_zero]

/-- A single arithmetic update in the truncated positive product's radix representation. -/
def codedCutoffStep (base bound weight M code : ℕ) : ℕ :=
  code * codedLengthFactor base bound weight M % base ^ (bound + 1)

private theorem productAt_step {bound k : ℕ} (positive : 0 < k) (fit : k ≤ bound) (q : ℕ) :
    productAt bound q k = lengthFactor bound k (primitiveCount k q) * productAt bound q (k + 1) := by
  let lengths := List.ofFn fun j : Fin bound ↦ (j.val + 1, primitiveCount (j.val + 1) q)
  have h : k - 1 < lengths.length := by simp [lengths]; omega
  have head : lengths[k - 1] = (k, primitiveCount k q) := by
    simp [lengths, Nat.sub_add_cancel (by omega : 1 ≤ k)]
  have cons := List.drop_eq_getElem_cons h
  rw [head, Nat.sub_add_cancel (by omega : 1 ≤ k)] at cons
  change ((lengths.drop (k - 1)).map _).prod = _ * ((lengths.drop ((k + 1) - 1)).map _).prod
  rw [cons]
  rfl

private theorem trueCutoffCode_step {bound k : ℕ} (positive : 0 < k) (fit : k ≤ bound) (q : ℕ) :
    trueCutoffCode bound q k = codedCutoffStep (cutoffRadix bound q) bound k
      (primitiveCount k q) (trueCutoffCode bound q (k + 1)) := by
  unfold trueCutoffCode codedCutoffStep
  simp only [productAt_step positive fit q, eval_mul]
  let base := cutoffRadix bound q
  let m := base ^ (bound + 1)
  have equal :
      (((lengthFactor bound k (primitiveCount k q)).eval base * (productAt bound q (k + 1)).eval base : ℕ) :
        ZMod m) =
      (((productAt bound q (k + 1)).eval base % m *
        codedLengthFactor base bound k (primitiveCount k q) : ℕ) : ZMod m) := by
    have red (a : ℕ) : ((a % m : ℕ) : ZMod m) = a :=
      (ZMod.natCast_eq_natCast_iff' _ _ _).mpr (Nat.mod_mod _ _)
    rw [Nat.cast_mul, Nat.cast_mul, red, codedLengthFactor_cast base bound positive]
    exact mul_comm _ _
  exact (ZMod.natCast_eq_natCast_iff' _ _ _).mp equal

/-- A provided code sequence is checked by one exact integer multiplication per cutoff. -/
structure PackedCutoffChecks (bound q lower : ℕ) (code : ℕ → ℕ) : Prop where
  base : code (bound + 1) = 1 % cutoffRadix bound q ^ (bound + 1)
  step : ∀ k, lower ≤ k → k ≤ bound →
    code k = codedCutoffStep (cutoffRadix bound q) bound k (primitiveCount k q) (code (k + 1))

theorem PackedCutoffChecks.count_eq {bound q lower n : ℕ} {code : ℕ → ℕ}
    (checked : PackedCutoffChecks bound q lower code) (hq : 0 < q)
    (positive : 0 < lower) (fit : n ≤ bound) {k : ℕ} (lo : lower ≤ k) (hi : k ≤ bound + 1) :
    code k / cutoffRadix bound q ^ n % cutoffRadix bound q = positiveCountDP n q k := by
  have step (j : ℕ) (hj : j < bound + 1) (jlo : k ≤ j)
      (next : code (j + 1) = trueCutoffCode bound q (j + 1)) :
      code j = trueCutoffCode bound q j := by
    rw [checked.step j (lo.trans jlo) (by omega), next]
    exact (trueCutoffCode_step (bound := bound) (k := j) (by omega) (by omega) q).symm
  have base : code (bound + 1) = trueCutoffCode bound q (bound + 1) := by
    rw [checked.base, trueCutoffCode, productAt]
    rw [Nat.add_sub_cancel, List.drop_of_length_le (by simp)]
    simp
  have equal : code k = trueCutoffCode bound q k := Nat.decreasingInduction' step hi base
  rw [equal, trueCutoffCode_digit hq fit]

/-- Read the alphabet vector with one digit extraction from each shared integer table. -/
def readPackedAlphabet (bound n k : ℕ) (codes : Fin n → ℕ → ℕ) : Array ℕ :=
  Array.ofFn fun i ↦
    let base := cutoffRadix bound (i.val + 1)
    codes i k / base ^ n % base

theorem readPackedAlphabet_eq {n bound k : ℕ} (fit : n ≤ bound)
    (hk : 3 ≤ k) (hkn : k ≤ bound + 1) (codes : Fin n → ℕ → ℕ)
    (checked : ∀ i, PackedCutoffChecks bound (i.val + 1) 3 (codes i)) :
    readPackedAlphabet bound n k codes = descentAlphabetTable n k := by
  unfold readPackedAlphabet descentAlphabetTable
  congr
  funext i
  exact (checked i).count_eq (Nat.succ_pos _) (by decide) fit hk hkn

/-- The usual signed binomial transform, with its inputs read from the packed counts. -/
def readPackedNumerator (bound n k : ℕ) (codes : Fin n → ℕ → ℕ) : List ℤ :=
  let letters := readPackedAlphabet bound n k codes
  List.ofFn fun r : Fin n ↦ descentNumeratorCell n r.val letters

theorem representativeChecks_of_packedCutoffs {n bound : ℕ} (hn : 3 ≤ n) (fit : n ≤ bound)
    (nodes : Array LongCycleFinite.Dyadic) (coeffs : Array (List ℤ))
    (codes : Fin n → ℕ → ℕ)
    (checked : ∀ i, PackedCutoffChecks bound (i.val + 1) 3 (codes i))
    (counts : ∀ i : Fin (lastRepresentative n - 2),
      readPackedNumerator bound n (i.val + 3) codes = (0 :: coeffs.getD i.val []) ++ [0])
    (signs : ∀ i : Fin (lastRepresentative n - 2),
      negativeMeshOK (coeffs.getD i.val []) nodes = true) :
    RepresentativeChecks n nodes coeffs := by
  intro i
  have h := counts i
  have boundRep : lastRepresentative n ≤ n + 1 := by
    unfold lastRepresentative
    omega
  have hi := i.isLt
  rw [readPackedNumerator, readPackedAlphabet_eq fit (by omega) (by omega) codes checked] at h
  exact ⟨h, signs i⟩

#print axioms PackedCutoffChecks.count_eq
#print axioms representativeChecks_of_packedCutoffs

end LongCycleBounds.DescentNecklace
