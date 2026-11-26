import LongCycleBounds.OccupancyJumpDiscount

/-! Finite quantitative transfer between original positive labels in the sparse-cutoff transition range. -/
noncomputable section
namespace LongCycleBounds.Occupancy
open Finset CycleProfile

/-- The actual coefficient after division by the unrestricted m^n. -/
def labelFraction (n k m : ℕ) (u : ℝ) : ℝ := anchoredLabel (profile k u) n m/(m:ℝ)^n

private theorem third_exp (x : ℝ) (hx : 0 ≤ x) : x^3 ≤ 6*Real.exp x := by
  have e := Real.sum_le_exp_of_nonneg hx 4
  have t := single_le_sum (s:=range 4) (a:=3) (f:=fun i : ℕ ↦ x^i/(i.factorial:ℝ))
    (fun i _ ↦ by positivity) (by decide)
  have sum := t.trans e
  norm_num [Nat.factorial] at sum
  linarith

/-- At square-root slot scale the actual marked coefficient is within O(1/n) of one,
uniformly in the mark and the cutoff for n at least 4mk. -/
theorem labelFraction_near_full_sqrt {n k m : ℕ} {C u : ℝ} (hm : 0 < m) (hk : 2 ≤ k)
    (hu : u ∈ Set.Icc (0:ℝ) 1) (size : 4*m*k ≤ n) (scale : (m:ℝ)^2 ≤ C^2*n) :
    |labelFraction n k m u-1| ≤ 384*C^4/n := by
  apply (original_coefficient_near_full hm hk size hu).trans
  have mp : 0 < (m:ℝ) := by exact_mod_cast hm
  have np : 0 < (n:ℝ) := by exact_mod_cast (lt_of_lt_of_le (by positivity : 0<4*m*k) size)
  let x := (n:ℝ)/(4*m)
  have xp : 0<x := by dsimp [x]; positivity
  have h := third_exp x xp.le
  have expbound : Real.exp (-x) ≤ 6/x^3 := by
    rw [Real.exp_neg,inv_eq_one_div,div_le_div_iff₀ (Real.exp_pos _) (pow_pos xp 3)]
    simpa using h
  have eq : -(n:ℝ)/(4*m) = -x := by dsimp [x]; ring
  rw [eq]
  apply (mul_le_mul_of_nonneg_left expbound mp.le).trans
  dsimp only [x]
  have sq := pow_le_pow_left₀ (sq_nonneg _) scale 2
  field_simp
  nlinarith only [sq]

/-- Transfer at arbitrary two positive labels satisfying the same finite square-root cap. -/
theorem labelFraction_transfer_sqrt {n k m l : ℕ} {C u : ℝ} (hm : 0 < m) (hl : 0 < l)
    (hk : 2 ≤ k) (hu : u ∈ Set.Icc (0:ℝ) 1)
    (bm : 4*m*k ≤ n) (bl : 4*l*k ≤ n) (sm : (m:ℝ)^2 ≤ C^2*n) (sl : (l:ℝ)^2 ≤ C^2*n)
    (large : 768*C^4 ≤ (n:ℝ)) :
    |labelFraction n k l u/labelFraction n k m u-1| ≤ 768*C^4/n := by
  let a := labelFraction n k m u
  let b := labelFraction n k l u
  let E := 384*C^4/(n:ℝ)
  have errorA : |a-1| ≤ E := labelFraction_near_full_sqrt hm hk hu bm sm
  have errorB : |b-1| ≤ E := labelFraction_near_full_sqrt hl hk hu bl sl
  have np : 0 < (n:ℝ) := by exact_mod_cast (lt_of_lt_of_le (by positivity : 0<4*m*k) bm)
  have ep : 0 ≤ E := by dsimp [E]; positivity
  have small : E ≤ 1/2 := by
    dsimp only [E]
    rw [div_le_iff₀ np]
    linarith
  have half : 1/2 ≤ a := by linarith [(abs_le.mp errorA).1]
  have ap : 0<a := by linarith
  have upper (j : ℕ) (hj : 0<j) : labelFraction n k j u ≤ 1 := by
    unfold labelFraction
    have jp : (j:ℝ)≠0 := by exact_mod_cast hj.ne'
    rw [original_profile_eq_slot_probability hj,mul_div_cancel_left₀ _ (pow_ne_zero _ jp)]
    exact slot_probability_le_one hj hu
  have ua : a ≤ 1 := upper m hm
  have ub : b ≤ 1 := upper l hl
  have dist : |b-a| ≤ E := abs_le.mpr ⟨by linarith [(abs_le.mp errorB).1],
    by linarith [(abs_le.mp errorA).1]⟩
  change |b/a-1| ≤ _
  rw [show b/a-1=(b-a)/a by field_simp,abs_div,abs_of_pos ap]
  calc
    _ ≤ E/(1/2) := div_le_div₀ ep dist (by norm_num) half
    _ = _ := by dsimp [E]; ring

#print axioms labelFraction_near_full_sqrt
#print axioms labelFraction_transfer_sqrt
end LongCycleBounds.Occupancy
