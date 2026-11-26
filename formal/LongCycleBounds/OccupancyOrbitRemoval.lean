import LongCycleBounds.OccupancySlotSeries
import LongCycleBounds.OccupancyBallDerivative

/-! Removing the orbit containing the distinguished ball in the true slot cycle index. -/
noncomputable section
namespace LongCycleBounds.Occupancy
open PowerSeries Finset CycleProfile
open scoped Classical

private theorem orbit_power_high {m h : ℕ} (too : m < h) (k : ℕ) (u : ℝ) :
    coeff m ((orbitSeries k u)^h)=0 := by
  rw [coeff_orbitSeries_pow]
  apply sum_eq_zero
  intro l hl
  obtain ⟨ha,pos⟩ := mem_filter.mp hl
  have total : (∑ i, l i)=m := (mem_piAntidiag.mp ha).1
  have small : h ≤ m := by simpa using (calc
    (∑ _ : Fin h, (1:ℕ)) ≤ ∑ i, l i := sum_le_sum fun i _ ↦ pos i
    _ = m := total)
  exact (Nat.not_le.mpr too small).elim

private theorem padded_slotIndex {m N : ℕ} (bound : m ≤ N) (k : ℕ) (u : ℝ) :
    (∑ h ∈ range (N+1), C (1/(h.factorial:ℝ))*coeff m ((orbitSeries k u)^h)) =
      slotIndexSeries k u m := by
  unfold slotIndexSeries
  symm
  apply sum_subset (range_subset_range.mpr (by omega))
  intro h _ hh
  rw [orbit_power_high (by have := not_lt.mp (fun low ↦ hh (mem_range.mpr low));omega),mul_zero]

private theorem derivative_level (k m h : ℕ) (u : ℝ) :
    derivative ℝ (C (1/((h+1).factorial:ℝ))*coeff m ((orbitSeries k u)^(h+1))) =
      ∑ l ∈ range (m+1), coeff l (markBall (orbitSeries k u))*
        (C (1/(h.factorial:ℝ))*coeff (m-l) ((orbitSeries k u)^h)) := by
  let Z := orbitSeries k u
  rw [Derivation.leibniz,derivative_C,smul_zero,add_zero,smul_eq_mul,←coeff_markBall,markBall_pow_succ]
  rw [mul_assoc,←nsmul_eq_mul,map_nsmul,nsmul_eq_mul,coeff_mul,Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have scalar : C (1/((h+1).factorial:ℝ))*((h+1:ℕ):PowerSeries ℝ) = C (1/(h.factorial:ℝ)) := by
    rw [←map_natCast (C (R:=ℝ)),←map_mul]
    congr 1
    rw [Nat.factorial_succ,Nat.cast_mul]
    have : ((h+1:ℕ):ℝ)≠0 := by positivity
    field_simp
  rw [←mul_assoc,scalar,mul_sum]
  apply sum_congr rfl
  intro l _
  ring

/-- Formal differentiation marks one ball. The orbit which receives it is selected
exactly once, whereas the residual arrangement retains its original symmetry divisor. -/
theorem remove_marked_orbit (k m : ℕ) (u : ℝ) :
    derivative ℝ (slotIndexSeries k u m) =
      ∑ l ∈ range (m+1), coeff l (markBall (orbitSeries k u))*slotIndexSeries k u (m-l) := by
  have ext := padded_slotIndex (m:=m) (N:=m+1) (by omega) k u
  rw [←ext,map_sum,sum_range_succ']
  have z : derivative ℝ (C (1/((0:ℕ).factorial:ℝ))*coeff m (orbitSeries k u^0))=0 := by
    by_cases hm : m=0 <;> simp [coeff_one,hm]
  rw [z,add_zero]
  simp_rw [derivative_level]
  rw [sum_comm]
  apply sum_congr rfl
  intro l _
  rw [←mul_sum,padded_slotIndex (Nat.sub_le m l)]

/-- The removal kernel on a nonzero orbit has the exact l to the d factor.
The forbidden singleton in the ball permutation produces zero at d=0. -/
theorem coeff_removed_orbit (k d l : ℕ) (u : ℝ) :
    coeff d (coeff l (markBall (orbitSeries k u))) =
      if d=0 then 0 else profile k u (d+1)*(l:ℝ)^d/d.factorial := by
  rw [coeff_markBall,coeff_derivative]
  simp only [orbitSeries,coeff_mk,coeff_C_mul,orbitBallSeries]
  by_cases hd : d=0
  · simp [hd,loadMark]
  rw [if_neg hd,loadMark,if_neg (by omega : ¬d+1<2)]
  change _ = (if d+1<k then u else 1)*_ / _
  by_cases hl : l=0
  · simp [hl,zero_pow hd]
  · have ln : (l:ℝ)≠0 := by exact_mod_cast hl
    have dn : ((d+1:ℕ):ℝ)≠0 := by positivity
    rw [pow_succ,Nat.factorial_succ,Nat.cast_mul]
    push_cast
    field_simp

#print axioms remove_marked_orbit
#print axioms coeff_removed_orbit
end LongCycleBounds.Occupancy
