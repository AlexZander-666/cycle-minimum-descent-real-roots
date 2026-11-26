import LongCycleBounds.DescentDerangementSeed

noncomputable section
namespace LongCycleBounds.DescentDerangement
open Finset Polynomial

/-- Remove the constant of the seventh partial sum, so that lower-degree losses
are unaltered and the rational seed can be measured once. -/
def centered (n : ℕ) : ℚ[X] := gn n - C (headTable 7 0)

private theorem centered_bound {v c : ℚ} (hv : 0 ≤ v) (hc : 0 ≤ c)
    (ratio : ∀ j ≥ 7, (1+c)*((1+j*v)/((j+1:ℕ):ℚ)) ≤ c)
    {n : ℕ} (hn : 7 ≤ n) (N : ℕ) :
    mass v N (centered n) ≤
    (∑ d ∈ range 8, |headTable 7 d - (if d=0 then headTable 7 0 else 0)| *v^d)
      + c * ∑ d ∈ range 8, |atomTable 7 d| *v^d := by
  have eq : centered n = seed + (gn n - gn 7) := by unfold centered seed; abel
  have tail := finite_tail hv hc N 7 ratio n hn
  have rest := mul_nonneg hc (mass_nonneg hv N (gnAtom n))
  have major := mul_le_mul_of_nonneg_left (atom_seven_mass hv N) hc
  rw [eq]
  exact (mass_add_le hv N ..).trans (add_le_add (seed_mass hv N) (by linarith))

private theorem half_ratio {v : ℚ} (hv : v ≤ 3/8) (j : ℕ) (hj : 7 ≤ j) :
    (1+1)*((1+(j:ℚ)*v)/((j+1:ℕ):ℚ)) ≤ 1 := by
  rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
  push_cast
  have h : (7:ℚ) ≤ j := by exact_mod_cast hj
  nlinarith [mul_le_mul_of_nonneg_left hv (Nat.cast_nonneg j : (0:ℚ) ≤ j)]

private theorem three_ratio (j : ℕ) (hj : 7 ≤ j) :
    (1+3)*((1+(j:ℚ)*(2/3))/((j+1:ℕ):ℚ)) ≤ 3 := by
  rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
  push_cast
  have h : (7:ℚ) ≤ j := by exact_mod_cast hj
  linarith

set_option maxRecDepth 16000 in
set_option maxHeartbeats 1800000 in
theorem centered_three_eighths {n : ℕ} (hn : 7 ≤ n) (N : ℕ) :
    mass (3/8) N (centered n) ≤ 4489049/41287680 := by
  apply (centered_bound (v:=3/8) (c:=1) (by norm_num) (by norm_num) (half_ratio le_rfl) hn N).trans
  norm_num [headTable, Finset.sum_range_succ, atomTable]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 1800000 in
theorem centered_two_thirds {n : ℕ} (hn : 7 ≤ n) (N : ℕ) :
    mass (2/3) N (centered n) ≤ 105547/136080 := by
  apply (centered_bound (v:=2/3) (c:=3) (by norm_num) (by norm_num) three_ratio hn N).trans
  norm_num [headTable, Finset.sum_range_succ, atomTable]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 1800000 in
theorem leading_interval {n : ℕ} (hn : 7 ≤ n) :
    103/280-1/5040 ≤ (gn n).coeff 0 ∧ (gn n).coeff 0 ≤ 103/280+1/5040 := by
  have h := centered_bound (v:=0) (c:=1) (by norm_num) (by norm_num)
    (half_ratio (by norm_num)) hn 1
  have bound : mass 0 1 (centered n) ≤ 1/5040 := h.trans (by norm_num [headTable, Finset.sum_range_succ, atomTable])
  have seed0 : headTable 7 0 = 103/280 := by norm_num [headTable, Finset.sum_range_succ, atomTable]
  simpa [mass,centered,seed0,abs_le,sub_le_iff_le_add,le_sub_iff_add_le,add_comm] using bound

#print axioms centered_three_eighths
#print axioms centered_two_thirds
#print axioms leading_interval
end LongCycleBounds.DescentDerangement
