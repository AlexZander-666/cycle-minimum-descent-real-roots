import LongCycleBounds.OrdinaryEulerianGapWeights
import LongCycleBounds.OrdinaryEulerianGapReadout

noncomputable section
namespace LongCycleBounds.OrdinaryEulerianGap
open Finset Polynomial DescentMesh DescentNecklace DescentTwoLetters Band PoleBridge Real LongCycles

/-- A weighted coefficient test at all roots of the preceding Eulerian row
in the central range. The loss-one summand vanishes exactly at such a root. -/
theorem central_transform_sign {n : ℕ} (hn : 128≤n) (a : ℕ→ℝ)
    (dominates : lossNorm n a (4/5) < a n) {x : ℝ} (hx : 0≤x)
    (upper : x≤5/2*sqrt ((n:ℝ)-1))
    (zero : (eulerian (n-1)).eval (-exp (-x))=0) :
    0 < (descentTransform n a).eval (-exp (-x))*(eulerian n).eval (-exp (-x)) := by
  let t := -exp (-x)
  let r := radius x
  let w (h : ℕ) := ((h.factorial:ℝ)/n.factorial)*r^(n-h)
  let U (h : ℕ) := scaledMoment r t (h+1)
  let C := t*r^(n+1)/(2*n.factorial*(1-t)^(n+1))
  have ht : t≠1 := by dsimp only [t]; linarith only [exp_pos (-x)]
  have sp : 0<sqrt (n:ℝ) := sqrt_pos.mpr (by exact_mod_cast (by omega : 0<n))
  have normeq : C*(descentTransform n a).eval t =
      (∑ h ∈ Ico 1 n, a h*w h*U h) + a n*U n := by
    have exactsum := normalized_transform n a (r:=r) ht
    change t*r^(n+1)/(2*n.factorial*(1-t)^(n+1))*(descentTransform n a).eval t = _
    rw [exactsum,←Ico_insert_right (by omega : 1≤n),sum_insert (by simp)]
    have regroup : (∑ h ∈ Ico 1 n, a h*((h.factorial:ℝ)/n.factorial)*r^(n-h)*
      scaledMoment r t (h+1)) = ∑ h ∈ Ico 1 n, a h*w h*U h := by
      apply sum_congr rfl
      intro h _
      dsimp only [w,U]; ring
    rw [regroup]
    change a n*((n.factorial:ℝ)/n.factorial)*r^(n-n)*U n+_ = _
    simp [Nat.factorial_ne_zero,add_comm]
  have scaleEU : C*(eulerian n).eval t=U n := by
    simp only [C,U,scaledMoment,moment,Nat.add_sub_cancel]
    field_simp
  have pt (h : ℕ) (mem : h∈Ico 1 n) : sqrt n*|a h*w h*U h| ≤ |a h| *(4/5:ℝ)^(n-h) := by
    obtain ⟨lo,high⟩ := mem_Ico.mp mem
    have wp : 0≤w h := mul_nonneg (by positivity) (pow_nonneg (radius_pos x).le _)
    rw [abs_mul,abs_mul,abs_of_nonneg wp]
    by_cases last : h+1=n
    · have u0 : U h=0 := by
        unfold U
        rw [last]
        simp [scaledMoment,moment,t,zero]
      rw [u0,abs_zero,mul_zero,mul_zero]; positivity
    · have small := central_weight hn lo (show h+2≤n by omega) hx upper
      calc
        _ = |a h| *(sqrt n*w h*|U h|) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left small (abs_nonneg _)
  have absbound : sqrt n*|C*(descentTransform n a).eval t-a n*U n| ≤ lossNorm n a (4/5) := by
    rw [normeq,add_sub_cancel_right]
    calc
      _ ≤ sqrt n*(∑ h ∈ Ico 1 n, |a h*w h*U h|) :=
          mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) sp.le
      _ ≤ _ := by rw [mul_sum]; exact sum_le_sum pt
  have pole : 1<sqrt n*|U n| := actual_eulerian_root_gap hn hx upper zero
  have apos : 0<a n := (show 0≤lossNorm n a (4/5) from sum_nonneg fun _ _ ↦ by positivity).trans_lt dominates
  have error : |C*(descentTransform n a).eval t-a n*U n| < a n*|U n| := by
    have ordered := (absbound.trans_lt dominates).trans (lt_of_le_of_lt (le_of_eq (mul_one (a n)).symm)
      (mul_lt_mul_of_pos_left pole apos))
    apply lt_of_mul_lt_mul_left (a:=sqrt n)
    · calc _ < a n*(sqrt n*|U n|) := ordered
           _ = _ := by ring
    · exact sp.le
  have same : 0 < (C*(descentTransform n a).eval t)*U n := by
    rcases le_or_gt 0 (U n) with pos|neg
    · rw [abs_of_nonneg pos,abs_lt] at error
      have : 0<U n := lt_of_le_of_ne pos (by intro e; rw [←e,abs_zero,mul_zero] at pole; linarith)
      exact mul_pos (by linarith only [error.1]) this
    · rw [abs_of_neg neg,abs_lt] at error
      exact mul_pos_of_neg_of_neg (by linarith only [error.2]) neg
  rw [←scaleEU] at same
  have res : 0 < C^2*((descentTransform n a).eval t*(eulerian n).eval t) := by
    calc (0:ℝ) < _ := same
         _ = _ := by ring
  exact pos_of_mul_pos_right res (sq_nonneg _)

/-- The original ordinary-descent row at a genuine central Eulerian zero. -/
theorem central_original_sign {n k : ℕ} (hn : 128≤n) (hk : 3≤k) (kn : k≤n)
    {x : ℝ} (hx : 0≤x) (upper : x≤5/2*sqrt ((n:ℝ)-1))
    (zero : (eulerian (n-1)).eval (-exp (-x))=0) :
    0<((row n k).map (Int.castRingHom ℝ)).eval (-exp (-x))*(eulerian n).eval (-exp (-x)) := by
  rw [original_eq_descentTransform (by omega : 1≤n)]
  exact central_transform_sign hn _ (actual_four_fifths_all hk kn hn) hx upper zero

#print axioms central_transform_sign
#print axioms central_original_sign
end LongCycleBounds.OrdinaryEulerianGap
