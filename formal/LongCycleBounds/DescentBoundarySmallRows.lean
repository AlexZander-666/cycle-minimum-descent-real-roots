import LongCycleBounds.DescentFiniteRoots

/-! Actual four- and five-letter rows at every cutoff, including both boundary rows. -/
noncomputable section
namespace LongCycleBounds.DescentBoundary
open Finset Polynomial LongCycleFinite DescentNecklace DescentTwoLetters

def realRow (n k : ℕ) : ℝ[X] := (row n k).map (Int.castRingHom ℝ)
def mixture (n : ℕ) (w : ℕ → ℝ) : ℝ[X] := ∑ k ∈ Icc 1 n, C (w k) * realRow n k

private theorem checked {n k : ℕ} (hn : 0 < n) {c : List ℤ} (h : descentRowDP n k = c) :
    realRow n k = ofCoeffs c := (ofCoeffs_descentRowDP hn k).symm.trans (congrArg ofCoeffs h)

theorem four_one : realRow 4 1 = 1 + 11*X + 11*X^2 + X^3 := by
  rw [checked (by decide) (c := [1,11,11,1]) (by decide +kernel)]
  simp [ofCoeffs, C_ofNat]
  ring

theorem four_two : realRow 4 2 = X * (X-C (-2))^2 := by
  rw [checked (by decide) (c := [0,4,4,1]) (by decide +kernel)]
  simp [ofCoeffs, C_ofNat]
  ring

theorem four_long {k : ℕ} (lo : 3 ≤ k) (hi : k ≤ 4) :
    realRow 4 k = 3*X*(1+X) := by
  have h : descentRowDP 4 k = [0,3,3,0] := by interval_cases k <;> decide +kernel
  rw [checked (by decide) h]
  simp [ofCoeffs, C_ofNat]
  ring

theorem five_one : realRow 5 1 = 1 + 26*X + 66*X^2 + 26*X^3 + X^4 := by
  rw [checked (by decide) (c := [1,26,66,26,1]) (by decide +kernel)]
  simp [ofCoeffs, C_ofNat]
  ring

theorem five_two : realRow 5 2 = 8*X + 24*X^2 + 12*X^3 := by
  rw [checked (by decide) (c := [0,8,24,12,0]) (by decide +kernel)]
  simp [ofCoeffs, C_ofNat]
  ring

theorem five_long {k : ℕ} (lo : 3 ≤ k) (hi : k ≤ 5) :
    realRow 5 k = 6*X*(1+X)^2 := by
  have h : descentRowDP 5 k = [0,6,12,6,0] := by interval_cases k <;> decide +kernel
  rw [checked (by decide) h]
  simp [ofCoeffs, C_ofNat]
  ring

theorem four_mixture (w : ℕ → ℝ) :
    mixture 4 w = C (w 1) * (1 + 11*X + 11*X^2 + X^3) +
      C (w 2) * (X*(X-C (-2))^2) + C (w 3+w 4) * (3*X*(1+X)) := by
  unfold mixture
  rw [show Icc 1 4 = ({1,2,3,4} : Finset ℕ) by decide]
  norm_num [four_one, four_two, four_long, map_add]
  ring

theorem five_mixture (w : ℕ → ℝ) :
    mixture 5 w = C (w 1) * (1 + 26*X + 66*X^2 + 26*X^3 + X^4) +
      C (w 2) * (8*X + 24*X^2 + 12*X^3) + C (w 3+w 4+w 5) * (6*X*(1+X)^2) := by
  unfold mixture
  rw [show Icc 1 5 = ({1,2,3,4,5} : Finset ℕ) by decide]
  norm_num [five_one, five_two, five_long, map_add]
  ring

#print axioms four_mixture
#print axioms five_mixture
end LongCycleBounds.DescentBoundary

