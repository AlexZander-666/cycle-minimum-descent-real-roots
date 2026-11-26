import LongCycleBounds.DescentBoundaryDerangementColors
import LongCycleBounds.DescentBoundaryDerangementRadii
import LongCycleBounds.DescentDerangementTail
import LongCycleBounds.DescentMeshEndSign

/-! End-node label ratios for the ordinary descent enumerator on derangements. -/
noncomputable section
namespace LongCycleBounds.DescentDerangement
open Polynomial DescentMesh

theorem labelRatio_signedInput {n : ℕ} (hn : 0<n) (s : ℚ) {p : ℝ} (hp : p ≠ 0) (j : ℕ) :
    labelRatio n (colorEval n (signedInput n s)) p j =
      (((gn n).eval (s/((j+1:ℕ):ℚ)) : ℚ) : ℝ)/p := by
  rw [labelRatio, actual_color_value hn (by omega)]
  push_cast
  field_simp

private theorem abs_argument {s : ℚ} (hs : s=1 ∨ s= -1) {j a : ℕ} (ha : 0<a)
    (haj : a ≤ j+1) : |s/((j+1:ℕ):ℚ)| ≤ 1/(a:ℚ) := by
  have h : |s|=1 := by rcases hs with rfl | rfl <;> norm_num
  rw [abs_div,h,abs_of_nonneg (by positivity)]
  exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast haj)

private theorem zero_label {n : ℕ} (hn : 0<n) {s : ℚ} (hs : s=1 ∨ s= -1) :
    0 ≤ (gn n).eval s ∧ (gn n).eval s ≤ 1 := by
  rcases hs with rfl | rfl
  · rw [gn_at_one hn]; norm_num
  · rw [gn_at_minus_one]; split <;> norm_num

private theorem rational_end_ratios {n : ℕ} (hn : 10 ≤ n) {s : ℚ} (hs : s=1 ∨ s= -1)
    (htwo : (gn n).eval (s/2) ≤ (4/3)*(gn n).eval 0) :
    let G := gn n
    let p := G.eval 0
    (∀ j : ℕ, 0 ≤ G.eval (s/((j+1:ℕ):ℚ)) ∧ G.eval (s/((j+1:ℕ):ℚ)) ≤ 1) ∧
    1/(2*(n:ℚ)) ≤ G.eval (s/2) ∧ G.eval s ≤ 3*p ∧
    (∀ j : ℕ, 1 ≤ j → G.eval (s/((j+1:ℕ):ℚ)) ≤ (4/3)*p) ∧
    (2/3)*p ≤ G.eval (s/3) ∧
    ∀ j : ℕ, 3 ≤ j →
      (6/7)*p ≤ G.eval (s/((j+1:ℕ):ℚ)) ∧ G.eval (s/((j+1:ℕ):ℚ)) ≤ (8/7)*p := by
  dsimp only
  have p := leading_interval (show 7≤n by omega)
  rw [coeff_zero_eq_eval_zero] at p
  have half (j : ℕ) (hj : 1 ≤ j) :=
    (derangement_three_radii hn (s/((j+1:ℕ):ℚ))).2.2 (abs_argument hs (a:=2) (by decide) (by omega))
  have thirds (j : ℕ) (hj : 2 ≤ j) :=
    (derangement_three_radii hn (s/((j+1:ℕ):ℚ))).2.1 (abs_argument hs (a:=3) (by decide) (by omega))
  have fourths (j : ℕ) (hj : 3 ≤ j) :=
    (derangement_three_radii hn (s/((j+1:ℕ):ℚ))).1 (abs_argument hs (a:=4) (by decide) (by omega))
  have zero := zero_label (by omega : 0<n) hs
  constructor
  · intro j
    cases j with
    | zero => simpa using zero
    | succ j =>
      have t := abs_le.mp (half (j+1) (by omega))
      constructor <;> linarith
  have n10 : (10:ℚ) ≤ n := by exact_mod_cast hn
  have dl : 1/(2*(n:ℚ)) ≤ 1/20 := one_div_le_one_div_of_le (by norm_num) (by linarith)
  have h2 := abs_le.mp (half 1 (by decide))
  have h3 := abs_le.mp (thirds 2 (by decide))
  norm_num at h2 h3
  refine ⟨by linarith, by linarith [zero.2], ?_, by linarith, ?_⟩
  · intro j hj
    by_cases one : j=1
    · subst j; simpa using htwo
    have h := abs_le.mp (thirds j (by omega))
    linarith
  · intro j hj
    have h := abs_le.mp (fourths j hj)
    constructor <;> linarith

/-- Transfer the rational estimates to the two actual orientations, retaining
the distinct, unnormalized denominator at the two-letter lower bound. -/
private theorem end_ratios_of_two {n : ℕ} (hn : 10 ≤ n) (s : ℚ) (hs : s=1 ∨ s= -1)
    (htwo : (gn n).eval (s/2) ≤ (4/3)*(gn n).eval 0) :
    let g := colorEval n (signedInput n s)
    let p := gnCoeff n n
    0<p ∧
    (∀ j : ℕ, 0 ≤ g (j+1) ∧ g (j+1) ≤ ((j:ℝ)+1)^n) ∧
    1/(2*(n:ℝ)) ≤ labelRatio n g 1 1 ∧ labelRatio n g p 0 ≤ 3 ∧
    (∀ j : ℕ, 1 ≤ j → labelRatio n g p j ≤ 4/3) ∧
    2/3 ≤ labelRatio n g p 2 ∧
    ∀ j : ℕ, 3 ≤ j → 6/7 ≤ labelRatio n g p j ∧ labelRatio n g p j ≤ 8/7 := by
  dsimp only
  obtain ⟨raw,twoL,zeroU,allU,threeL,regular⟩ := rational_end_ratios hn hs htwo
  have npos : 0<n := by omega
  have pdef : gnCoeff n n = (((gn n).eval 0 : ℚ):ℝ) := by
    simp [gnCoeff,coeff_zero_eq_eval_zero]
  have ppos : 0 < gnCoeff n n := by
    rw [pdef]
    apply Rat.cast_pos.mpr
    have p := (leading_interval (show 7≤n by omega)).1
    rw [coeff_zero_eq_eval_zero] at p
    linarith
  have rt := labelRatio_signedInput npos s ppos.ne'
  refine ⟨ppos, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    have zero : (0:ℝ) ≤ (((gn n).eval (s/((j+1:ℕ):ℚ)):ℚ):ℝ) := by exact_mod_cast (raw j).1
    have one : (((gn n).eval (s/((j+1:ℕ):ℚ)):ℚ):ℝ) ≤ 1 := by exact_mod_cast (raw j).2
    rw [actual_color_value npos (by omega)]
    have nn : (0:ℝ) ≤ ((j+1:ℕ):ℝ)^n := by positivity
    refine ⟨mul_nonneg nn zero, ?_⟩
    simpa using mul_le_mul_of_nonneg_left one nn
  · rw [labelRatio_signedInput npos s one_ne_zero, div_one]
    have h := Rat.cast_le (K:=ℝ) |>.mpr twoL
    push_cast at h
    simpa using h
  · rw [rt, div_le_iff₀ ppos,pdef]
    norm_num
    exact_mod_cast zeroU
  · intro j hj
    rw [rt,div_le_iff₀ ppos,pdef]
    have h := Rat.cast_le (K:=ℝ) |>.mpr (allU j hj)
    push_cast at h
    simpa only [Nat.cast_add, Nat.cast_one] using h
  · rw [rt,le_div_iff₀ ppos,pdef]
    have h := Rat.cast_le (K:=ℝ) |>.mpr threeL
    push_cast at h
    simpa using h
  · intro j hj
    rw [rt, le_div_iff₀ ppos, div_le_iff₀ ppos,pdef]
    constructor
    · have h := Rat.cast_le (K:=ℝ) |>.mpr (regular j hj).1
      push_cast at h
      simpa only [Nat.cast_add, Nat.cast_one] using h
    · have h := Rat.cast_le (K:=ℝ) |>.mpr (regular j hj).2
      push_cast at h
      simpa only [Nat.cast_add, Nat.cast_one] using h

/-- Complete end-node ratio data at both signs, proved for every n ≥ 10. -/
theorem derangement_end_ratios {n : ℕ} (hn : 10 ≤ n) (s : ℚ) (hs : s=1 ∨ s= -1) :
    let g := colorEval n (signedInput n s)
    let p := gnCoeff n n
    0<p ∧
    (∀ j : ℕ, 0 ≤ g (j+1) ∧ g (j+1) ≤ ((j:ℝ)+1)^n) ∧
    1/(2*(n:ℝ)) ≤ labelRatio n g 1 1 ∧ labelRatio n g p 0 ≤ 3 ∧
    (∀ j : ℕ, 1 ≤ j → labelRatio n g p j ≤ 4/3) ∧
    2/3 ≤ labelRatio n g p 2 ∧
    ∀ j : ℕ, 3 ≤ j → 6/7 ≤ labelRatio n g p j ∧ labelRatio n g p j ≤ 8/7 := by
  apply end_ratios_of_two hn s hs
  have hh := half_alphabet_upper hn (x:=s/2) (by rcases hs with rfl | rfl <;> norm_num)
  have h0 := (leading_interval (show 7≤n by omega)).1
  rw [coeff_zero_eq_eval_zero] at h0
  linarith

#print axioms derangement_end_ratios
#print axioms labelRatio_signedInput
end LongCycleBounds.DescentDerangement
