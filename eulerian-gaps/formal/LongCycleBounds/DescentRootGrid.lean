import LongCycleBounds.DescentActualReciprocal

/-! Ordering and reflection of the analytic sign nodes. -/
noncomputable section
namespace LongCycleBounds.DescentMesh
open Real

def gridAngle (n i : ℕ) : ℝ := π*(i:ℝ)/((n:ℝ)+1)
def nodeAt (θ : ℝ) : ℝ := -exp (-(π*cos θ/sin θ))
def rootNode (n i : ℕ) : ℝ := nodeAt (gridAngle n i)

theorem nodeAt_negative (θ : ℝ) : nodeAt θ < 0 := neg_neg_of_pos (exp_pos _)

theorem gridAngle_phase (n i : ℕ) : ((n:ℝ)+1)*gridAngle n i=(i:ℝ)*π := by
  unfold gridAngle
  field_simp

theorem gridAngle_bounds {n i : ℕ} (hi : 0 < i) (hin : i < n+1) :
    0 < gridAngle n i ∧ gridAngle n i < π := by
  unfold gridAngle
  constructor
  · positivity
  · apply (div_lt_iff₀ (by positivity)).mpr
    exact mul_lt_mul_of_pos_left (by exact_mod_cast hin) pi_pos

theorem nodeAt_antitone : StrictAntiOn nodeAt (Set.Ioo 0 π) := by
  intro x hx y hy hxy
  have sx := sin_pos_of_pos_of_lt_pi hx.1 hx.2
  have sy := sin_pos_of_pos_of_lt_pi hy.1 hy.2
  have diff := sin_pos_of_pos_of_lt_pi (sub_pos.mpr hxy) (by linarith only [hy.2,hx.1] : y-x<π)
  rw [sin_sub] at diff
  have cot : π*cos y/sin y < π*cos x/sin x := by
    rw [div_lt_div_iff₀ sy sx]
    nlinarith only [mul_pos pi_pos diff]
  unfold nodeAt
  exact neg_lt_neg (exp_lt_exp.mpr (neg_lt_neg cot))

theorem rootNode_order {n i j : ℕ} (hi : 0 < i) (hij : i < j) (hj : j < n+1) :
    rootNode n j < rootNode n i := by
  apply nodeAt_antitone (gridAngle_bounds hi (by omega)) (gridAngle_bounds (by omega) hj)
  unfold gridAngle
  apply div_lt_div_of_pos_right _ (by positivity)
  exact mul_lt_mul_of_pos_left (by exact_mod_cast hij) pi_pos

theorem rootNode_reflect {n i : ℕ} (hi : i≤n+1) :
    rootNode n (n+1-i) = (rootNode n i)⁻¹ := by
  have phase : gridAngle n (n+1-i)=π-gridAngle n i := by
    unfold gridAngle
    rw [Nat.cast_sub hi,Nat.cast_add,Nat.cast_one]
    field_simp
  unfold rootNode nodeAt
  rw [phase,cos_pi_sub,sin_pi_sub,← neg_inv,← exp_neg]
  congr 2
  ring

#print axioms rootNode_order
#print axioms rootNode_reflect
end LongCycleBounds.DescentMesh
