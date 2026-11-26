import LongCycleBounds.OccupancyAnchoredSeries

/-! Differentiate the ball-count variable without moving the slot-count variable. -/
noncomputable section
namespace LongCycleBounds.Occupancy
open PowerSeries Finset
abbrev SlotBallSeries := PowerSeries (PowerSeries ℝ)

/-- The formal derivative in the ball variable at each fixed slot size. -/
def markBall (F : SlotBallSeries) : SlotBallSeries :=
  mk fun m ↦ derivative ℝ (coeff m F)

@[simp] theorem coeff_markBall (F : SlotBallSeries) (m : ℕ) :
    coeff m (markBall F) = derivative ℝ (coeff m F) := coeff_mk .. 

theorem markBall_mul (F G : SlotBallSeries) :
    markBall (F*G) = markBall F*G+F*markBall G := by
  ext1 m
  simp only [coeff_markBall,map_add,coeff_mul,map_sum,Derivation.leibniz,smul_eq_mul,←sum_add_distrib]
  apply sum_congr rfl
  intro v _
  ring

theorem markBall_pow_succ (F : SlotBallSeries) (h : ℕ) :
    markBall (F^(h+1)) = (h+1:ℕ)*markBall F*F^h := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [pow_succ F (h+1),markBall_mul,ih,pow_succ F h]
    push_cast
    ring

#print axioms markBall_pow_succ
end LongCycleBounds.Occupancy
