import LongCycleBounds.DescentDerangementTail
import LongCycleBounds.DescentBoundaryDerangementReadout

/-! Certified two-radius loss budgets for the actual derangement descent row and its reversal. -/
noncomputable section
namespace LongCycleBounds.DescentDerangement
open Finset Polynomial Real DescentMesh DescentTwoLetters

private theorem loss_rat {v : ℚ} (hv : 0 ≤ v) (n : ℕ) :
    (∑ h ∈ Ico 1 n, |(gn n).coeff (n-h)| *v^(n-h)) ≤ mass v n (centered n) := by
  have reindex := Finset.sum_Ico_reflect (fun d ↦ |(gn n).coeff d| *v^d) 1
    (m:=n) (n:=n) (by omega)
  have lo : n+1-n=1 := by omega
  have hi : n+1-1=n := by omega
  rw [reindex,lo,hi]
  calc
    _ = ∑ d ∈ Ico 1 n, |(centered n).coeff d| *v^d := by
      apply sum_congr rfl
      intro d hd
      have dne : d ≠ 0 := by have := (mem_Ico.mp hd).1; omega
      simp [centered, coeff_C, dne]
    _ ≤ _ := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro d hd
        exact mem_range.mpr (mem_Ico.mp hd).2
      · intro d _ _
        positivity

theorem gn_loss_le {v : ℚ} (hv : 0 ≤ v) (n : ℕ) :
    lossNorm n (gnCoeff n) (v:ℝ) ≤ (mass v n (centered n) : ℝ) := by
  unfold lossNorm gnCoeff
  exact_mod_cast loss_rat hv n

theorem gn_budgets {n : ℕ} (hn : 7 ≤ n) :
    0 < gnCoeff n n ∧ lossNorm n (gnCoeff n) (3/8) ≤ (3/7)*gnCoeff n n ∧
    lossNorm n (gnCoeff n) (2/3) ≤ 16*n*gnCoeff n n := by
  have h0 := (leading_interval hn).1
  have p : (1/3:ℝ) ≤ gnCoeff n n := by
    simp only [gnCoeff, Nat.sub_self]
    calc
      (1/3:ℝ) = ((1/3:ℚ):ℝ) := by norm_num
      _ ≤ _ := Rat.cast_le.mpr (by linarith)
  have h := gn_loss_le (v:=3/8) (by norm_num) n
  have l := gn_loss_le (v:=2/3) (by norm_num) n
  push_cast at h l
  have h1 : (mass (3/8) n (centered n) : ℝ) ≤ 4489049/41287680 := (Rat.cast_le.mpr (centered_three_eighths hn n)).trans_eq (by norm_num)
  have l1 : (mass (2/3) n (centered n) : ℝ) ≤ 105547/136080 := (Rat.cast_le.mpr (centered_two_thirds hn n)).trans_eq (by norm_num)
  have six : (7:ℝ) ≤ n := by exact_mod_cast hn
  exact ⟨by linarith, by linarith, by nlinarith [mul_le_mul_of_nonneg_right six (by linarith : 0 ≤ gnCoeff n n)]⟩

theorem central_derangement {n i : ℕ} (hn : 128 ≤ n) {θ : ℝ}
    (lo : π/(2*sqrt ((n:ℝ)+1)) ≤ θ) (top : θ ≤ π/2) (phase : ((n:ℝ)+1)*θ=(i:ℝ)*π) :
    (-1:ℝ)^i*((row n 2).map (Int.castRingHom ℝ)).eval (-exp (-(π*cos θ/sin θ))) < 0 := by
  rw [actual_two_readout (by omega)]
  obtain ⟨positive, high, low⟩ := gn_budgets (n:=n) (by omega)
  exact central_sign_of_global hn lo top phase _ positive high low

theorem central_derangement_reflected {n i : ℕ} (hn : 128 ≤ n) {θ : ℝ}
    (lo : π/(2*sqrt ((n:ℝ)+1)) ≤ θ) (top : θ ≤ π/2) (phase : ((n:ℝ)+1)*θ=(i:ℝ)*π) :
    (-1:ℝ)^i*(descentTransform n (reflectedCoefficients n (gnCoeff n))).eval
      (-exp (-(π*cos θ/sin θ))) < 0 := by
  obtain ⟨positive, high, low⟩ := gn_budgets (n:=n) (by omega)
  apply central_sign_of_global hn lo top phase
  · simpa [reflectedCoefficients] using positive
  · simpa [reflected_lossNorm,reflectedCoefficients] using high
  · simpa [reflected_lossNorm,reflectedCoefficients] using low

/-- The second orientation at the original ordinary derangement row's ambient reversal. -/
theorem central_derangement_true_reciprocal {n i : ℕ} (hn : 128 ≤ n) {θ : ℝ}
    (lo : π/(2*sqrt ((n:ℝ)+1)) ≤ θ) (top : θ ≤ π/2) (phase : ((n:ℝ)+1)*θ=(i:ℝ)*π) :
    let t := -exp (-(π*cos θ/sin θ))
    (-1:ℝ)^i*(t^(n-1)*((row n 2).map (Int.castRingHom ℝ)).eval t⁻¹) < 0 := by
  dsimp only
  rw [actual_two_reciprocal (by omega) (neg_ne_zero.mpr (exp_ne_zero _))]
  exact central_derangement_reflected hn lo top phase

#print axioms central_derangement_true_reciprocal
#print axioms gn_budgets
#print axioms central_derangement
#print axioms central_derangement_reflected
end LongCycleBounds.DescentDerangement
