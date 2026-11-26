import LongCycleBounds.DescentMeshNeighbors
import LongCycleBounds.OuterMoments

/-! Two-sided geometric control of raw end-node terms, with one exceptional label. -/
noncomputable section
namespace LongCycleBounds.DescentMesh
open Finset Real Outer

theorem raw_right_radii {n m : ℕ} (x : ℝ) {r : ℝ} (hr : 0 ≤ r)
    (adj : weight n x (m+1) ≤ r*weight n x m) (d : ℕ) :
    weight n x (m+d) ≤ r^d*weight n x m := by
  have ratioM : ratio n x m ≤ r := (mul_le_mul_iff_left₀ (weight_pos n x m)).mp
    (by simpa only [← weight_succ] using adj)
  induction d with
  | zero => simp
  | succ d ih =>
    rw [← Nat.add_assoc,weight_succ,pow_succ']
    calc
      _ ≤ r*weight n x (m+d) := mul_le_mul_of_nonneg_right
        (((ratio_antitone n x) (by omega : m ≤ m+d)).trans ratioM) (weight_pos ..).le
      _ ≤ _ := by simpa [mul_assoc] using mul_le_mul_of_nonneg_left ih hr

theorem raw_left_radii {n m : ℕ} (hm : 1 ≤ m) (x : ℝ) {l : ℝ} (hl : 0 ≤ l)
    (adj : weight n x (m-1) ≤ l*weight n x m) (d : ℕ) (hd : d ≤ m) :
    weight n x (m-d) ≤ l^d*weight n x m := by
  have eq : weight n x m=ratio n x (m-1)*weight n x (m-1) := by
    simpa [show m-1+1=m by omega] using weight_succ n x (m-1)
  have one : 1 ≤ l*ratio n x (m-1) := by
    apply (mul_le_mul_iff_left₀ (weight_pos n x (m-1))).mp
    simpa only [one_mul,mul_assoc,← eq] using adj
  induction d with
  | zero => simp
  | succ d ih =>
    let j := m-(d+1)
    have r := (ratio_antitone n x) (show j ≤ m-1 by dsimp [j]; omega)
    have a := mul_le_mul_of_nonneg_right (one.trans (mul_le_mul_of_nonneg_left r hl))
      (weight_pos n x j).le
    rw [one_mul,mul_assoc,← weight_succ,show j+1=m-d by dsimp [j]; omega] at a
    exact a.trans (by simpa [pow_succ',mul_assoc] using mul_le_mul_of_nonneg_left (ih (by omega)) hl)

private theorem left_raw_sum {n m : ℕ} (hm : 1 ≤ m) (x : ℝ) {l : ℝ} (hl : 0 ≤ l) (h1 : l<1)
    (adj : weight n x (m-1) ≤ l*weight n x m) :
    ∑ j ∈ range m, weight n x j ≤ l/(1-l)*weight n x m := by
  rw [← sum_range_reflect (weight n x) m]
  have each (j : ℕ) (hj : j∈range m) :
      weight n x (m-1-j) ≤ l^j*(l*weight n x m) := by
    have hd := mem_range.mp hj
    have h := raw_left_radii hm x hl adj (j+1) (by omega)
    simpa [show m-(j+1)=m-1-j by omega, pow_succ,mul_assoc] using h
  have h := sum_le_sum each
  rw [← sum_mul] at h
  have H := geom_sum_mul_neg l m
  have g : (∑ j ∈ range m, l^j) ≤ 1/(1-l) := by
    apply (le_div_iff₀ (by linarith)).mpr
    linarith only [H,pow_nonneg hl m]
  have ga := mul_le_mul_of_nonneg_right g (mul_nonneg hl (weight_pos n x m).le)
  exact h.trans (by convert ga using 1; ring)

private theorem right_raw_sum {n m : ℕ} (x : ℝ) {r : ℝ} (hr : 0 ≤ r) (h1 : r<1)
    (adj : weight n x (m+1) ≤ r*weight n x m) :
    Summable (fun d : ℕ ↦ weight n x (d+(m+1))) ∧
      (∑' d : ℕ, weight n x (d+(m+1))) ≤ r/(1-r)*weight n x m := by
  have G := ((hasSum_geometric_of_lt_one hr h1).mul_right (r*weight n x m))
  have b (d : ℕ) : weight n x (d+(m+1)) ≤ r^d*(r*weight n x m) := by
    simpa [show d+(m+1)=m+(d+1) by omega,pow_succ,mul_assoc] using
      raw_right_radii x hr adj (d+1)
  have h := G.summable.of_nonneg_of_le (fun _ ↦ (weight_pos ..).le) b
  refine ⟨h,?_⟩
  have sm := h.tsum_le_tsum b G.summable
  rw [G.tsum_eq] at sm
  exact sm.trans (by apply le_of_eq; ring)

/-- A sign criterion at a dominant positive label (indexed by m). The only
exceptional upper allowance E is at label two (array index one). -/
theorem signed_end_of_dominance {n m : ℕ} (hm : 1 ≤ m) (x : ℝ) (a : ℕ→ℝ)
    {l r A E : ℝ} (hl : 0 ≤ l) (hl1 : l<1) (hr : 0 ≤ r) (hr1 : r<1)
    (ha : 0 ≤ A) (he : 0 ≤ E)
    (left : weight n x (m-1) ≤ l*weight n x m) (right : weight n x (m+1) ≤ r*weight n x m)
    (limits : ∀ j, |a j| ≤ A+(if j=1 then E else 0))
    (dominant : A*(l/(1-l)+r/(1-r)) + E*l^(m-1) < a m) :
    0 < (-1:ℝ)^m * ∑' j, (-1:ℝ)^j * a j * weight n x j := by
  let w := weight n x
  let f (j : ℕ) := (-1:ℝ)^m*((-1:ℝ)^j*a j*w j)
  have absf (j : ℕ) : |f j| = |a j| *w j := by
    simp [f,abs_mul,abs_of_nonneg (weight_pos n x j).le,w]
  have atM : f m = a m*w m := by
    have sq : (-1:ℝ)^m*(-1:ℝ)^m=1 := by rw [← mul_pow]; norm_num
    dsimp [f]; linear_combination (a m*w m)*sq
  obtain ⟨rwSum,rwBound⟩ := right_raw_sum x hr hr1 right
  have tailS := rwSum.mul_left A
  have upper (d : ℕ) : ‖f (d+(m+1))‖ ≤ A*w (d+(m+1)) := by
    rw [Real.norm_eq_abs,absf]
    apply mul_le_mul_of_nonneg_right _ (weight_pos ..).le
    simpa [show d+(m+1)≠1 by omega] using limits (d+(m+1))
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
  have leftB : |∑ j ∈ range m, f j| ≤ A*(l/(1-l)*w m) + E*l^(m-1)*w m := by
    apply (abs_sum_le_sum_abs _ _).trans
    have h (j : ℕ) (_ : j ∈ range m) : |f j| ≤ A*w j + (if j=1 then E*w 1 else 0) := by
      rw [absf]
      have h := mul_le_mul_of_nonneg_right (limits j) (weight_pos n x j).le
      by_cases hj : j=1
      · subst j; simpa [add_mul] using h
      · simpa [hj] using h
    have sm := sum_le_sum h
    rw [sum_add_distrib,← mul_sum,sum_ite_eq'] at sm
    have g := mul_le_mul_of_nonneg_left (left_raw_sum hm x hl hl1 left) ha
    have e := raw_left_radii hm x hl left (m-1) (by omega)
    rw [show m-(m-1)=1 by omega] at e
    have ee := mul_le_mul_of_nonneg_left e he
    split_ifs at sm
    · linarith only [sm,g,ee]
    · have := mul_nonneg he (weight_pos n x 1).le
      linarith only [sm,g,ee,this]
  have de := fS.sum_add_tsum_nat_add (m+1)
  rw [sum_range_succ,atM] at de
  have b := mul_lt_mul_of_pos_right dominant (weight_pos n x m)
  have total : 0 < ∑' j, f j := by
    linarith only [de,neg_le_abs (∑ j ∈ range m, f j),neg_le_abs (∑' d, f (d+(m+1))),
      leftB,rightB,b]
  simpa only [f,tsum_mul_left,w] using total

#print axioms raw_right_radii
#print axioms raw_left_radii
#print axioms signed_end_of_dominance
end LongCycleBounds.DescentMesh
