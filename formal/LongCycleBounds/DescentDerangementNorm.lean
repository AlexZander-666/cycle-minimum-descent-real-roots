import LongCycleBounds.DescentDerangementInput

noncomputable section
namespace LongCycleBounds.DescentDerangement
open Finset Polynomial

/-- Sum over the first N loss degrees. Uniformity in N allows applying the
bound directly to either orientation and to a row of any size. -/
def mass (v : ℚ) (N : ℕ) (P : ℚ[X]) : ℚ :=
  ∑ d ∈ range N, |P.coeff d| * v^d

theorem mass_nonneg {v : ℚ} (hv : 0 ≤ v) (N : ℕ) (P : ℚ[X]) : 0 ≤ mass v N P :=
  sum_nonneg fun _ _ ↦ by positivity

theorem mass_add_le {v : ℚ} (hv : 0 ≤ v) (N : ℕ) (P Q : ℚ[X]) :
    mass v N (P+Q) ≤ mass v N P + mass v N Q := by
  unfold mass
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro d _
  rw [coeff_add, ← add_mul]
  exact mul_le_mul_of_nonneg_right (abs_add_le ..) (pow_nonneg hv d)

theorem mass_sub_le {v : ℚ} (hv : 0 ≤ v) (N : ℕ) (P Q : ℚ[X]) :
    mass v N (P-Q) ≤ mass v N P + mass v N Q := by
  simpa [sub_eq_add_neg, mass] using mass_add_le hv N P (-Q)

theorem mass_C_mul (v : ℚ) (N : ℕ) (b : ℚ) (P : ℚ[X]) :
    mass v N (C b * P) = |b| * mass v N P := by
  simp [mass, mul_sum, abs_mul, mul_assoc]

theorem mass_X_mul {v : ℚ} (hv : 0 ≤ v) (N : ℕ) (P : ℚ[X]) :
    mass v N (X*P) ≤ v * mass v N P := by
  cases N with
  | zero => simp [mass]
  | succ N =>
    have shift : mass v (N+1) (X*P) = v * mass v N P := by
      simp [mass, sum_range_succ', pow_succ, mul_sum, mul_assoc, mul_comm]
    rw [shift]
    apply mul_le_mul_of_nonneg_left _ hv
    simp only [mass, sum_range_succ]
    exact le_add_of_nonneg_right (by positivity)

theorem atom_step (j : ℕ) : gnAtom (j+1) =
    C (1/((j+1:ℕ):ℚ)) * (C (j:ℚ)*(X*gnAtom j) - gnAtom j) := by
  rw [gnAtom]
  ring

set_option maxHeartbeats 1400000 in
theorem atom_mass_step {v : ℚ} (hv : 0 ≤ v) (N j : ℕ) :
    mass v N (gnAtom (j+1)) ≤ (1+j*v)/((j+1:ℕ):ℚ) * mass v N (gnAtom j) := by
  rw [atom_step, mass_C_mul, abs_of_nonneg (show (0:ℚ) ≤ 1/((j+1:ℕ):ℚ) by positivity)]
  have h := mass_sub_le hv N (C (j:ℚ)*(X*gnAtom j)) (gnAtom j)
  rw [mass_C_mul, abs_of_nonneg (Nat.cast_nonneg j)] at h
  have s := mul_le_mul_of_nonneg_left (mass_X_mul hv N (gnAtom j)) (Nat.cast_nonneg j : (0:ℚ) ≤ j)
  calc
    _ ≤ 1/((j+1:ℕ):ℚ) * ((j:ℚ)*(v*mass v N (gnAtom j)) + mass v N (gnAtom j)) :=
      mul_le_mul_of_nonneg_left (h.trans (add_le_add s (le_refl _))) (by positivity)
    _ = _ := by ring

/-- A finite tail invariant, uniform in its final degree cutoff and without a limiting series. -/
theorem finite_tail {v c : ℚ} (hv : 0 ≤ v) (hc : 0 ≤ c) (N b : ℕ)
    (ratio : ∀ j ≥ b, (1+c)*((1+j*v)/((j+1:ℕ):ℚ)) ≤ c) :
    ∀ n ≥ b, mass v N (gn n - gn b) + c * mass v N (gnAtom n) ≤ c * mass v N (gnAtom b) := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => simp [mass]
  | succ j hj ih =>
    have heq : gn (j+1) - gn b = gn j - gn b + gnAtom (j+1) := by rw [gn_succ]; abel
    rw [heq]
    have ht := mass_add_le hv N (gn j - gn b) (gnAtom (j+1))
    have hm := mul_le_mul_of_nonneg_left (atom_mass_step hv N j) (show 0 ≤ 1+c by linarith)
    have hq := mul_le_mul_of_nonneg_right (ratio j hj) (mass_nonneg hv N (gnAtom j))
    rw [← mul_assoc] at hm
    linarith only [ht, hm.trans hq, ih]

end LongCycleBounds.DescentDerangement
