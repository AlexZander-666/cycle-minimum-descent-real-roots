import LongCycleBounds.DescentMeshPole
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds

/-! Uniform geometry for the central angular mesh. -/
namespace LongCycleBounds.DescentMesh
open Real

/-- The central cut gives both the Bernoulli tail budget and the sharper radius needed
for the separation of high and low Eulerian moments. -/
theorem central_mesh_geometry {N θ : ℝ} (hN : 129 ≤ N)
    (hlo : π/(2 * sqrt N) ≤ θ) (hhi : θ ≤ π/2) :
    2 ≤ N*(sin θ)^2 ∧ π/sin θ ≤ 41/20*sqrt (N-1) := by
  let u := sqrt N
  let w := sqrt (N-1)
  let y := π/(2*u)
  have up : 0 < u := sqrt_pos.mpr (by linarith)
  have wp : 0 < w := sqrt_pos.mpr (by linarith)
  have up2 : u^2=N := sq_sqrt (by linarith)
  have wp2 : w^2=N-1 := sq_sqrt (by linarith)
  have yp : 0 < y := by dsimp [y]; positivity
  have yu : y*(2*u)=π := div_mul_cancel₀ _ (by positivity)
  have yl : y ≤ θ := hlo
  have pi2 : π^2 ≤ 10 := by nlinarith [pi_lt_d2, pi_pos]
  have y2 : y^2 ≤ 3/100 := by
    have eq : y^2 * (4*N) = π^2 := by rw [← up2, ← yu]; ring
    by_contra! hbad
    nlinarith [mul_pos (sub_pos.mpr hbad) (show 0 < N by linarith)]
  have siny : 199/200*y ≤ sin y := by
    have h₁ := sin_ge_sub_cube yp.le
    nlinarith [mul_nonneg (sub_nonneg.mpr y2) yp.le]
  have sint : sin y ≤ sin θ := monotoneOn_sin
    ⟨by linarith [pi_pos], yl.trans hhi⟩ ⟨by linarith [pi_pos], hhi⟩ yl
  have strong : 199/400*π ≤ u*sin θ := by
    nlinarith only [yu, mul_le_mul_of_nonneg_left (siny.trans sint) up.le]
  have spos : 0 < sin θ := by nlinarith only [siny, sint, yp]
  constructor
  · have lo : 199/400*(3:ℝ) ≤ u*sin θ := by linarith only [strong, pi_gt_three]
    have sq := (sq_le_sq₀ (by norm_num : 0 ≤ 199/400*(3:ℝ)) (mul_pos up spos).le).mpr lo
    simp only [mul_pow, up2] at sq
    norm_num at sq
    linarith
  · apply (div_le_iff₀ spos).mpr
    have rel : u ≤ 101/100*w := by
      apply (sq_le_sq₀ up.le (by positivity)).mp
      rw [up2, mul_pow, wp2]
      nlinarith
    nlinarith only [strong, mul_le_mul_of_nonneg_right rel spos.le, mul_nonneg wp.le spos.le]

#print axioms central_mesh_geometry
end LongCycleBounds.DescentMesh
