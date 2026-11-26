import LongCycleBounds.DescentMeshEndSign
import LongCycleBounds.DescentFrozenConstants

noncomputable section
namespace LongCycleBounds.DescentMesh
open Finset Real Outer
/-- Allow one exceptional envelope at any specified index up to the dominant term. -/
theorem single_exception_dominance {n m : ℕ} (hm : 1 ≤ m) (eIdx : ℕ) (heIdx : eIdx ≤ m) (x : ℝ) (a : ℕ→ℝ)
    {l r A E : ℝ} (hl : 0 ≤ l) (hl1 : l<1) (hr : 0 ≤ r) (hr1 : r<1)
    (ha : 0 ≤ A) (he : 0 ≤ E)
    (left : weight n x (m-1) ≤ l*weight n x m) (right : weight n x (m+1) ≤ r*weight n x m)
    (limits : ∀ j, |a j| ≤ A+(if j=eIdx then E else 0))
    (dominant : A*(l/(1-l)+r/(1-r)) + E*l^(m-eIdx) < a m) :
    0 < (-1:ℝ)^m * ∑' j, (-1:ℝ)^j * a j * weight n x j := by
  let w := weight n x
  let f (j : ℕ) := (-1:ℝ)^m*((-1:ℝ)^j*a j*w j)
  have absf (j : ℕ) : |f j| = |a j| *w j := by
    simp [f,abs_mul,abs_of_nonneg (weight_pos n x j).le,w]
  have atM : f m = a m*w m := by
    have sq : (-1:ℝ)^m*(-1:ℝ)^m=1 := by rw [← mul_pow]; norm_num
    dsimp [f]; linear_combination (a m*w m)*sq
  obtain ⟨rwSum,rwBound⟩ := (descentFrozenConst LongCycleBounds.DescentMeshEndTails LongCycleBounds.DescentMesh.right_raw_sum) x hr hr1 right
  have tailS := rwSum.mul_left A
  have upper (d : ℕ) : ‖f (d+(m+1))‖ ≤ A*w (d+(m+1)) := by
    rw [Real.norm_eq_abs,absf]
    apply mul_le_mul_of_nonneg_right _ (weight_pos ..).le
    simpa [show d+(m+1)≠eIdx by omega] using limits (d+(m+1))
  have fRS : Summable (fun d : ℕ ↦ f (d+(m+1))) := Summable.of_norm_bounded
    (g:=fun d ↦ A*w (d+(m+1))) tailS upper
  have fS := (summable_nat_add_iff (m+1)).mp fRS
  have absRS : Summable (fun d : ℕ ↦ ‖f (d+(m+1))‖) := fRS.norm
  have rightB : |∑' d, f (d+(m+1))| ≤ A*(r/(1-r)*w m) := by
    rw [← Real.norm_eq_abs]
    apply (norm_tsum_le_tsum_norm absRS).trans
    have h := absRS.tsum_le_tsum upper tailS
    rw [tsum_mul_left] at h
    exact h.trans (mul_le_mul_of_nonneg_left rwBound ha)
  have leftB : |∑ j ∈ range m, f j| ≤ A*(l/(1-l)*w m) + E*l^(m-eIdx)*w m := by
    apply (abs_sum_le_sum_abs _ _).trans
    have h (j : ℕ) (_ : j ∈ range m) : |f j| ≤ A*w j + (if j=eIdx then E*w eIdx else 0) := by
      rw [absf]
      have h := mul_le_mul_of_nonneg_right (limits j) (weight_pos n x j).le
      by_cases hj : j=eIdx
      · subst j; simpa [add_mul] using h
      · simpa [hj] using h
    have sm := sum_le_sum h
    rw [sum_add_distrib,← mul_sum,sum_ite_eq'] at sm
    have g := mul_le_mul_of_nonneg_left ((descentFrozenConst LongCycleBounds.DescentMeshEndTails LongCycleBounds.DescentMesh.left_raw_sum) hm x hl hl1 left) ha
    have e := raw_left_radii hm x hl left (m-eIdx) (by omega)
    rw [show m-(m-eIdx)=eIdx by omega] at e
    have ee := mul_le_mul_of_nonneg_left e he
    split_ifs at sm
    · linarith only [sm,g,ee]
    · have := mul_nonneg he (weight_pos n x eIdx).le
      linarith only [sm,g,ee,this]
  have de := fS.sum_add_tsum_nat_add (m+1)
  rw [sum_range_succ,atM] at de
  have b := mul_lt_mul_of_pos_right dominant (weight_pos n x m)
  have total : 0 < ∑' j, f j := by
    linarith only [de,neg_le_abs (∑ j ∈ range m, f j),neg_le_abs (∑' d, f (d+(m+1))),
      leftB,rightB,b]
  simpa only [f,tsum_mul_left,w] using total


#print axioms single_exception_dominance
end LongCycleBounds.DescentMesh
