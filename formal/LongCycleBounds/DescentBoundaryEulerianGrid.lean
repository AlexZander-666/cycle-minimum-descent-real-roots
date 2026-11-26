import LongCycleBounds.DescentBoundaryEulerianEnd
import LongCycleBounds.DescentBoundaryLargeBridge

noncomputable section
namespace LongCycleBounds.DescentBoundary
open Finset Polynomial Real LongCycles DescentNecklace DescentMesh DescentTwoLetters

theorem boundary_grid_regimes {n i : ℕ} (hn : 128 ≤ n) (half : 2*i≤n+1) :
    (π/(2*sqrt ((n:ℝ)+1)) ≤ gridAngle n i ∧ gridAngle n i ≤ π/2) ∨
    (4*(i:ℝ)^2 ≤ (n:ℝ)+1 ∧ gridAngle n i < π/2) := by
  let N := (n:ℝ)+1
  have np : 0<N := by dsimp [N]; positivity
  have sp : 0<sqrt N := sqrt_pos.mpr np
  have sq := sq_sqrt np.le
  have h2 : 2*(i:ℝ) ≤ N := by dsimp [N]; exact_mod_cast half
  have n128 : 128≤(n:ℝ) := by exact_mod_cast hn
  have fr : sqrt N<N := by dsimp [N] at *; nlinarith
  by_cases h : sqrt N ≤ 2*(i:ℝ)
  · left
    constructor
    · change π/(2*sqrt N) ≤ π*(i:ℝ)/N
      rw [div_le_div_iff₀ (by positivity) np]
      have z := mul_le_mul_of_nonneg_right h sp.le
      nlinarith only [mul_nonneg pi_pos.le (sub_nonneg.mpr z),congrArg (fun x : ℝ ↦ π*x) sq]
    · change π*(i:ℝ)/N ≤ π/2
      rw [div_le_div_iff₀ np (by norm_num)]
      nlinarith only [mul_nonneg pi_pos.le (sub_nonneg.mpr h2)]
  · right
    have h' := lt_of_not_ge h
    constructor
    · change 4*(i:ℝ)^2 ≤ N
      have nn : 0≤(i:ℝ) := by positivity
      nlinarith only [sq,sq_nonneg (sqrt N-2*(i:ℝ)),mul_nonneg (sub_nonneg.mpr h'.le)
        (add_nonneg sp.le (mul_nonneg (by norm_num : (0:ℝ)≤2) nn))]
    · change π*(i:ℝ)/N < π/2
      rw [div_lt_div_iff₀ np (by norm_num)]
      nlinarith only [mul_pos pi_pos (sub_pos.mpr (h'.trans fr))]

private theorem unrestricted_half {n i : ℕ} (hn : 128 ≤ n) (hi : 2 ≤ i) (half : 2*i≤n+1) :
    (-1:ℝ)^i * (realRow n 1).eval (rootNode n i) < 0 := by
  have angle := (gridAngle_bounds (by omega : 0 < i) (by omega : i < n+1)).1
  have phase := gridAngle_phase n i
  rcases boundary_grid_regimes hn half with ⟨lo,top⟩ | ⟨small,top⟩
  · exact unrestricted_central_sign hn lo top phase
  · exact unrestricted_end_sign hn hi angle top phase small

theorem unrestricted_grid_sign {n i : ℕ} (hn : 128 ≤ n) (hi : 2 ≤ i) (last : i < n) :
    (-1:ℝ)^i * (realRow n 1).eval (rootNode n i) < 0 := by
  by_cases half : 2*i≤n+1
  · exact unrestricted_half hn hi half
  let j := n+1-i
  have hj : 2 ≤ j := by dsimp [j]; omega
  have lastj : j < n := by dsimp [j]; omega
  have reflected := unrestricted_half hn hj (by dsimp [j]; omega)
  have nz : rootNode n j ≠ 0 := ne_of_lt (nodeAt_negative _)
  have reciprocal : (rootNode n j)^(n-1) * (realRow n 1).eval (rootNode n j)⁻¹ =
      (realRow n 1).eval (rootNode n j) := by
    rw [realRow, unrestricted_row (by omega)]
    have h := eulerian_reciprocity (n-1) nz
    rwa [show n-1+1=n by omega] at h
  rw [← reciprocal] at reflected
  have h := grid_sign_reflect hj lastj (realRow n 1) reflected
  simpa only [show n+1-j=i by dsimp [j]; omega] using h

theorem large_mixtures_of_derangement_sign {n : ℕ} (hn : 128 ≤ n)
    (derangement : ∀ j, 2 ≤ j → j < n →
      (-1:ℝ)^j * (realRow n 2).eval (rootNode n j) < 0)
    (w : ℕ → ℝ) (hw : ∀ k ∈ Icc 1 n, 0 ≤ w k) (pos : ∃ k ∈ Icc 1 n, 0 < w k) :
    (mixture n w).Splits ∧ (mixture n w).roots.Nodup ∧ ∀ x ∈ (mixture n w).roots, x ≤ 0 := by
  apply large_mixtures_of_two_signs hn _ w hw pos
  intro k hk j hj last
  rcases hk with rfl | rfl
  · exact unrestricted_grid_sign hn hj last
  · exact derangement j hj last

#print axioms unrestricted_grid_sign
#print axioms large_mixtures_of_derangement_sign
end LongCycleBounds.DescentBoundary
