import LongCycleBounds.DescentBoundaryEulerianGrid
import LongCycleBounds.DescentBoundaryEndLabels
import LongCycleBounds.DescentBoundaryDerangementColors
import LongCycleBounds.DescentDerangementBudget
import LongCycleBounds.DescentDerangementEndRatios

noncomputable section
namespace LongCycleBounds.DescentDerangement
open Finset Polynomial Real DescentTwoLetters DescentMesh DescentBoundary

def EndColorBounds (n : ℕ) (s : ℚ) : Prop :=
  let g := colorEval n (signedInput n s)
  let p := gnCoeff n n
  0 < p ∧ (∀ j : ℕ, 0 ≤ g (j+1) ∧ g (j+1) ≤ ((j:ℝ)+1)^n) ∧
    1/(2*(n:ℝ)) ≤ labelRatio n g 1 1 ∧ labelRatio n g p 0 ≤ 3 ∧
    (∀ j, 1 ≤ j → labelRatio n g p j ≤ 4/3) ∧ 2/3 ≤ labelRatio n g p 2 ∧
    ∀ j, 3 ≤ j → 6/7 ≤ labelRatio n g p j ∧ labelRatio n g p j ≤ 8/7

theorem signed_end {n i : ℕ} (hn : 128 ≤ n) (hi : 2 ≤ i) (s : ℚ) (bounds : EndColorBounds n s)
    {θ : ℝ} (ht : 0 < θ) (top : θ < π/2) (phase : ((n:ℝ)+1)*θ=(i:ℝ)*π)
    (small : 4*(i:ℝ)^2 ≤ (n:ℝ)+1) :
    (-1:ℝ)^i*(descentTransform n (signedInput n s)).eval (-exp (-(π*cos θ/sin θ))) < 0 := by
  obtain ⟨hp,raw,two,zeroU,cap,three,reg⟩ := bounds
  have sig := end_sign_allowing_one_label hn hi ht top phase small hp _ raw two zeroU cap three reg
  let x := π*cos θ/sin θ
  have xp : 0 < x := div_pos (mul_pos pi_pos (cos_pos_of_mem_Ioo ⟨by linarith [pi_pos],top⟩))
    (sin_pos_of_pos_of_lt_pi ht (by linarith [pi_pos]))
  rw [labelSeries_transform n _ xp,mul_left_comm] at sig
  have fac : 0 < exp (-x)/(1+exp (-x))^(n+1) := by positivity
  have z := (mul_pos_iff_of_pos_left fac).mp sig
  have flip : (-1:ℝ)^i = -((-1:ℝ)^(i-1)) := by
    conv_lhs => rw [← Nat.sub_add_cancel (show 1 ≤ i by omega),pow_succ]
    ring
  rw [flip,neg_mul]
  exact neg_lt_zero.mpr z

theorem derangement_grid_of_colors {n i : ℕ} (hn : 128 ≤ n)
    (pos : EndColorBounds n 1) (neg : EndColorBounds n (-1)) (hi : 2 ≤ i) (last : i < n) :
    (-1:ℝ)^i * (realRow n 2).eval (rootNode n i) < 0 := by
  have halfGrid {j : ℕ} (hj : 2 ≤ j) (half : 2*j ≤ n+1) :
      let t := rootNode n j
      (-1:ℝ)^j*(realRow n 2).eval t < 0 ∧ (-1:ℝ)^j*(t^(n-1)*(realRow n 2).eval t⁻¹) < 0 := by
    dsimp only
    have ht := (gridAngle_bounds (by omega : 0 < j) (by omega : j < n+1)).1
    have phase := gridAngle_phase n j
    rcases boundary_grid_regimes hn half with ⟨lo,top⟩ | ⟨small,top⟩
    · exact ⟨central_derangement hn lo top phase,central_derangement_true_reciprocal hn lo top phase⟩
    · constructor
      · rw [realRow,actual_two_readout (by omega)]
        have f : signedInput n 1 = gnCoeff n := by funext h; simp [signedInput]
        simpa only [f,rootNode,nodeAt] using signed_end hn hj 1 pos ht top phase small
      · rw [realRow,actual_two_reciprocal (n:=n) (t:=rootNode n j) (by omega) (ne_of_lt (nodeAt_negative _))]
        have f : signedInput n (-1) = reflectedCoefficients n (gnCoeff n) := by
          funext h; simp [signedInput,reflectedCoefficients]
        simpa only [f,rootNode,nodeAt] using signed_end hn hj (-1) neg ht top phase small
  by_cases half : 2*i ≤ n+1
  · exact (halfGrid hi half).1
  have ref := (halfGrid (j:=n+1-i) (by omega) (by omega)).2
  simpa only [show n+1-(n+1-i)=i by omega] using
    grid_sign_reflect (by omega : 2 ≤ n+1-i) (by omega : n+1-i < n) _ ref

theorem derangement_grid_sign {n i : ℕ} (hn : 128 ≤ n) (hi : 2 ≤ i) (last : i < n) :
    (-1:ℝ)^i * (realRow n 2).eval (rootNode n i) < 0 :=
  derangement_grid_of_colors hn (derangement_end_ratios (by omega) 1 (Or.inl rfl))
    (derangement_end_ratios (by omega) (-1) (Or.inr rfl)) hi last

theorem all_cutoffs_large {n : ℕ} (hn : 128 ≤ n) (w : ℕ → ℝ)
    (hw : ∀ k ∈ Icc 1 n, 0 ≤ w k) (pos : ∃ k ∈ Icc 1 n, 0 < w k) :
    (mixture n w).Splits ∧ (mixture n w).roots.Nodup ∧ ∀ x ∈ (mixture n w).roots, x ≤ 0 :=
  large_mixtures_of_derangement_sign hn (fun _ ↦ derangement_grid_sign hn) w hw pos

#print axioms derangement_grid_sign
#print axioms all_cutoffs_large
end LongCycleBounds.DescentDerangement
