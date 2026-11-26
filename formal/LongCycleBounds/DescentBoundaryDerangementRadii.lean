import LongCycleBounds.DescentDerangementSeed
import LongCycleBounds.DescentBoundaryDerangementReadout

noncomputable section
namespace LongCycleBounds.DescentDerangement
open Finset Polynomial

theorem abs_eval_le_mass (p : ℚ[X]) {x v : ℚ} (hv : |x| ≤ v) :
    |p.eval x| ≤ mass v (p.natDegree+1) p := by
  rw [eval_eq_sum_range]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro i _
  rw [abs_mul,abs_pow]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hv i) (abs_nonneg _)

private def atomMass10 (v : ℚ) : ℚ := ∑ d ∈ range 11, |atomTable 10 d| * v^d
private def headMass10 (v : ℚ) : ℚ := ∑ d ∈ range 11,
  |headTable 10 d - (if d=0 then headTable 10 0 else 0)| * v^d

private theorem tail_eval10 {n : ℕ} (hn : 10 ≤ n) {x v c : ℚ}
    (vx : |x| ≤ v) (hc : 0 ≤ c)
    (ratio : ∀ j ≥ 10, (1+c)*((1+j*v)/((j+1:ℕ):ℚ)) ≤ c) :
    |(gn n).eval x - (gn 10).eval x| ≤ c*atomMass10 v := by
  let p := gn n - gn 10
  let N := p.natDegree+1
  have hv := (abs_nonneg x).trans vx
  have t := finite_tail hv hc N 10 ratio n hn
  have cap := mass_le_cut hv N 11 (gnAtom 10) (fun d hd ↦
    (atomTable_eq ..).trans (atomTable_zero_above (by omega)))
  have upper : mass v N (gnAtom 10) ≤ atomMass10 v := by
    simpa only [mass,atomTable_eq,atomMass10] using cap
  have r := mul_le_mul_of_nonneg_left upper hc
  have rem := mul_nonneg hc (mass_nonneg hv N (gnAtom n))
  have e := abs_eval_le_mass p vx
  change |(gn n - gn 10).eval x| ≤ mass v N (gn n-gn 10) at e
  rw [eval_sub] at e
  exact e.trans ((le_add_of_nonneg_right rem).trans (t.trans r))

theorem derangement_head_error {n : ℕ} (hn : 10 ≤ n) {x v c : ℚ}
    (vx : |x| ≤ v) (hc : 0 ≤ c)
    (ratio : ∀ j ≥ 10, (1+c)*((1+j*v)/((j+1:ℕ):ℚ)) ≤ c) :
    |(gn n).eval x - (gn n).eval 0| ≤ headMass10 v + 2*c*atomMass10 v := by
  let p := gn 10 - C ((gn 10).coeff 0)
  have hv := (abs_nonneg x).trans vx
  have e := abs_eval_le_mass p vx
  have cap := mass_le_cut hv (p.natDegree+1) 11 p (fun d hd ↦ by
    simp [p,coeff_sub,headTable_eq,headTable_zero_above (by omega : 10<d),coeff_C,
      show d≠0 by omega])
  have middle : |(gn 10).eval x-(gn 10).eval 0| ≤ headMass10 v := by
    have h := e.trans cap
    simpa only [p,eval_sub,eval_C,← coeff_zero_eq_eval_zero,mass,coeff_sub,coeff_C,headTable_eq,headMass10] using h
  have tx := tail_eval10 hn vx hc ratio
  have t0 := tail_eval10 hn (show |(0:ℚ)| ≤ v by simpa using hv) hc ratio
  rw [abs_le] at middle tx t0 ⊢
  constructor <;> linarith

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem derangement_three_radii {n : ℕ} (hn : 10 ≤ n) (x : ℚ) :
    (|x|≤1/4 → |(gn n).eval x-(gn n).eval 0|≤13/250) ∧
    (|x|≤1/3 → |(gn n).eval x-(gn n).eval 0|≤2/25) ∧
    (|x|≤1/2 → |(gn n).eval x-(gn n).eval 0|≤4/25) := by
  refine ⟨fun hx ↦ (derangement_head_error hn (c:=1/2) hx (by norm_num) ?_).trans ?_,
    fun hx ↦ (derangement_head_error hn (c:=1) hx (by norm_num) ?_).trans ?_,
    fun hx ↦ (derangement_head_error hn (c:=3/2) hx (by norm_num) ?_).trans ?_⟩
  all_goals first
    | (intro j hj; have t : (10:ℚ) ≤ j := by exact_mod_cast hj
       push_cast
       field_simp
       linarith)
    | norm_num [headMass10,atomMass10,headTable,Finset.sum_range_succ,atomTable]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 16384 in
theorem half_alphabet_upper {n : ℕ} (hn : 10 ≤ n) {x : ℚ} (hx : x=1/2 ∨ x= -(1/2)) :
    (gn n).eval x ≤ 12/25 := by
  have xv : |x| ≤ 1/2 := by rcases hx with rfl | rfl <;> norm_num
  have t := tail_eval10 hn (c:=3/2) xv (by norm_num) (by
    intro j hj; have z : (10:ℚ) ≤ j := by exact_mod_cast hj
    push_cast
    field_simp
    linarith)
  have b : (3/2)*atomMass10 (1/2) ≤ 17/1000 := by
    norm_num [atomMass10,Finset.sum_range_succ,atomTable]
  have head : (gn 10).eval x ≤ 46/100 := by
    rcases hx with rfl | rfl <;>
      norm_num [gn,sum_range_succ,gnAtom,eval_add,eval_mul,eval_C,eval_X,eval_one,eval_sub]
  have u := (abs_le.mp (t.trans b)).2
  linarith
#print axioms half_alphabet_upper
#print axioms derangement_three_radii
end LongCycleBounds.DescentDerangement
