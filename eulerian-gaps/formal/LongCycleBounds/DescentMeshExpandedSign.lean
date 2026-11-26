import LongCycleBounds.DescentMeshResidualBudget

/-! The exact finite signed-log expansion has the central angular sign. -/
noncomputable section
namespace LongCycleBounds.DescentMesh
open Finset Real FixedCycleCount

theorem expanded_top {n k : ℕ} (hk : 3≤k) (hn : 0<n) (N B T : ℕ) :
    expandedCoefficient n k N B T n = allowedFraction n k := by
  classical
  simp only [expandedCoefficient,if_true]
  have nonzero (w : LogWord k N B T) : 2 ≤ wordLoss w := by
    let i : Fin (w.1.val+1) := 0
    have h := single_le_sum (s:=univ) (f:=fun a ↦ atomLoss (w.2 a)) (fun _ _ ↦ Nat.zero_le _) (mem_univ i)
    exact (atom_loss hk _).1.trans h
  have term (w : LogWord k N B T) : ¬(wordLength w ≤ n ∧ n=n-wordLoss w) := by
    have := nonzero w; omega
  simp [term]

theorem expanded_global {n k : ℕ} (hk : 3≤k) (hn : k≤n) (N B T : ℕ) :
    lossNorm n (expandedCoefficient n k N B T) (2/3) ≤ 16*n*allowedFraction n k := by
  let p := allowedFraction n k
  have p0 : 0≤p := allowedFraction_nonneg .. 
  have bound (m : ℕ) : allowedFraction m k ≤ (2*(n:ℝ))*p := by
    have kpos : (1:ℝ) ≤ n := by exact_mod_cast (by omega : 1≤n)
    by_cases h : m=0
    · subst m
      rw [allowedFraction_zero]
      have h := empty_residual (by omega : 2≤k) hn
      apply h.trans
      apply mul_le_mul_of_nonneg_right _ p0
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hn) (by norm_num)
    · have s := nonempty_residual (by omega : 2≤k) hn (Nat.pos_of_ne_zero h)
      apply s.trans
      exact mul_le_mul_of_nonneg_right (by linarith) p0
  apply (expanded_loss_le n k N B T (by norm_num : 0≤(2/3:ℝ))).trans
  let u (w : LogWord k N B T) := |wordCoefficient w| * (2/3:ℝ)^(wordLoss w)
  have m (w : LogWord k N B T) (_ : w ∈ univ) :
      (if wordLength w ≤ n then allowedFraction (n-wordLength w) k * u w else 0) ≤
      (2*(n:ℝ)*p)*u w := by
    have u0 : 0≤u w := by dsimp [u]; positivity
    split_ifs
    · exact mul_le_mul_of_nonneg_right (bound _) u0
    · positivity
  have sm := sum_le_sum m
  rw [← mul_sum] at sm
  apply sm.trans
  have h := word_mass_budget hk N B T (v:=2/3) (by norm_num) (by norm_num)
  have small : ∑ w, u w ≤ 8 := h.trans (by linarith only [envelope_comparison])
  have mul := mul_le_mul_of_nonneg_left small (show 0≤2*(n:ℝ)*p by positivity)
  dsimp only [p] at *
  linarith only [mul]

theorem expanded_small {n k : ℕ} (hk : 3≤k) (hn : k≤n) (h128 : 128≤n) (N B T : ℕ)
    {v K : ℝ} (hv : 0≤v) (half : v≤1/2)
    (budget : 2*(exp (badEnvelope v)-1)+1/1000 < K) :
    lossNorm n (expandedCoefficient n k N B T) v < K*allowedFraction n k := by
  let p := allowedFraction n k
  have pp : 0<p := lt_of_lt_of_le (by positivity) (Occupancy.allowedFraction_ge_half (by omega : 2≤k) hn)
  have s := expanded_loss_envelope hk hn N B T hv (by norm_num : (0:ℝ)<2/3)
    (half.trans (by norm_num)) (by norm_num)
  have rat : 0≤v/(2/3) := by positivity
  have rr : v/(2/3) ≤ 3/4 := by linarith
  have pw : (v/(2/3))^((n+1)/2) ≤ (3/4:ℝ)^(n/2) :=
    (pow_le_pow_left₀ rat rr _).trans (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega))
  have kr : (k:ℝ) ≤ n := by exact_mod_cast hn
  have nz : (0:ℝ) ≤ (k:ℝ) := by positivity
  have zn := mul_le_mul (mul_le_mul_of_nonneg_left kr (by norm_num : (0:ℝ)≤2)) pw
    (by positivity) (by positivity)
  have eight : exp (badEnvelope (2/3))-1 ≤ 8 := by linarith only [envelope_comparison]
  have zz := calc
    2*(k:ℝ)*(v/(2/3))^((n+1)/2)*(exp (badEnvelope (2/3))-1)
        ≤ 2*(k:ℝ)*(v/(2/3))^((n+1)/2)*8 := mul_le_mul_of_nonneg_left eight (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_right zn (by norm_num : (0:ℝ)≤8)
  have em := empty_tail_small n h128
  have est : 2*(exp (badEnvelope v)-1) +
      2*(k:ℝ)*(v/(2/3))^((n+1)/2)*(exp (badEnvelope (2/3))-1) < K := by
    linarith only [zz,em,budget]
  exact s.trans_lt (by simpa [mul_comm] using mul_lt_mul_of_pos_left est pp)

theorem central_sign_expanded {n k i : ℕ} (hk : 3≤k) (hn : k≤n) (h128 : 128≤n)
    (N B T : ℕ) {θ : ℝ} (lo : π/(2*sqrt ((n:ℝ)+1)) ≤ θ) (top : θ ≤ π/2)
    (phase : ((n:ℝ)+1)*θ=(i:ℝ)*π) :
    (-1:ℝ)^i*(descentTransform n (expandedCoefficient n k N B T)).eval
      (-exp (-(π*cos θ/sin θ))) < 0 := by
  apply central_sign_of_global h128 lo top phase
  · rw [expanded_top hk (by omega)]
    exact lt_of_lt_of_le (by positivity) (Occupancy.allowedFraction_ge_half (by omega : 2≤k) hn)
  · rw [expanded_top hk (by omega)]
    exact (expanded_small hk hn h128 N B T (by norm_num) (by norm_num) envelope_table.2.2.1).le
  · rw [expanded_top hk (by omega)]
    exact expanded_global hk hn N B T

#print axioms expanded_global
#print axioms expanded_small
#print axioms central_sign_expanded
end LongCycleBounds.DescentMesh
