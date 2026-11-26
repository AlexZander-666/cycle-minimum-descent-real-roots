import LongCycleBounds.OrdinaryEulerianLabelIncrements
import LongCycleBounds.Outer
import LongCycleBounds.WeightedOuter

noncomputable section
namespace LongCycleBounds.OrdinaryEulerianGap
open Outer DescentMesh Real LongCycles

/-- Exact positive-label normalization. The alternating series begins with
the positive sign at label one, for both the perturbed and the Eulerian row. -/
theorem labelG_weighted_eval (n : ℕ) (a : ℕ→ℝ) (ap : 0<a n) (x : ℝ) (hx : 0<x) :
    a n * weightedMoment (n-1) x (labelG n a) =
      exp (-x)/(1+exp (-x))^(n+1)*(descentTransform n a).eval (-exp (-x)) := by
  rw [←labelSeries_transform n a hx,weightedMoment,←tsum_mul_left]
  apply tsum_congr
  intro i
  change a n*((-1:ℝ)^i*weight (n-1) x i*labelG n a (i+1)) =
    (-1:ℝ)^i*colorEval n a (i+1)*exp (-x)^(i+1)
  unfold labelG weight
  rw [Nat.cast_add,Nat.cast_one]
  field_simp

theorem linear_label_moment {n : ℕ} (hn : 1≤n) (x : ℝ) :
    weightedMoment (n-1) x (fun q ↦ (q:ℝ)) = moment n x := by
  unfold weightedMoment moment
  apply tsum_congr
  intro i
  simp only [weight,Nat.cast_succ]
  rw [show ((i:ℝ)+1)^n=((i:ℝ)+1)^(n-1)*((i:ℝ)+1) by rw [←pow_succ]; congr 1; omega]
  ring

theorem original_zero_to_cancellation {n : ℕ} {x : ℝ} (hx : 0<x)
    (zero : (eulerian (n-1)).eval (-exp (-x))=0) : moment (n-1) x=0 := by
  rw [outerMoment_eq_evaluation _ _ hx,zero,mul_zero,zero_div]

theorem sign_of_weighted_moments {n : ℕ} (hn : 1≤n) (a : ℕ→ℝ) (ap : 0<a n)
    {x : ℝ} (hx : 0<x) (aligned :
      0 < weightedMoment (n-1) x (labelG n a) * weightedMoment (n-1) x (fun q ↦ (q:ℝ))) :
    0<(descentTransform n a).eval (-exp (-x))*(eulerian n).eval (-exp (-x)) := by
  let f := exp (-x)/(1+exp (-x))^(n+1)
  have z : 0<f := by dsimp [f]; positivity
  have arow := labelG_weighted_eval n a ap x hx
  change _=f*_ at arow
  have eu : weightedMoment (n-1) x (fun q ↦ (q:ℝ)) = f*(eulerian n).eval (-exp (-x)) := by
    rw [linear_label_moment hn,outerMoment_eq_evaluation n x hx]; dsimp only [f]; ring
  have aligned' := mul_pos ap aligned
  rw [←mul_assoc,arow,eu] at aligned'
  apply pos_of_mul_pos_right (a:=f^2) _ (sq_nonneg _)
  calc (0:ℝ) < _ := aligned'
       _ = _ := by ring

#print axioms labelG_weighted_eval
#print axioms original_zero_to_cancellation
#print axioms sign_of_weighted_moments
end LongCycleBounds.OrdinaryEulerianGap
