import LongCycleBounds.DescentDerangementNorm

noncomputable section
namespace LongCycleBounds.DescentDerangement
open Finset Polynomial

/-- Rational coefficients of the signed product, computed without polynomial quotients. -/
def atomTable : ℕ → ℕ → ℚ
  | 0, d => if d=0 then 1 else 0
  | j+1, 0 => (1/((j+1:ℕ):ℚ)) * (0-atomTable j 0)
  | j+1, d+1 => (1/((j+1:ℕ):ℚ)) * (j*atomTable j d-atomTable j (d+1))

theorem atomTable_eq (j d : ℕ) : (gnAtom j).coeff d = atomTable j d := by
  induction j generalizing d with
  | zero => simp [gnAtom, atomTable, coeff_one]
  | succ j ih =>
    cases d with
    | zero => simp [atom_step, atomTable, ih]
    | succ d => simp [atom_step, atomTable, ih]

def headTable (j d : ℕ) : ℚ := ∑ i ∈ range (j+1), atomTable i d

theorem headTable_eq (j d : ℕ) : (gn j).coeff d = headTable j d := by
  simp [gn, headTable, finsetSum_coeff, atomTable_eq]

theorem atomTable_zero_above {j d : ℕ} (h : j < d) : atomTable j d = 0 := by
  induction j generalizing d with
  | zero => simp [atomTable, Nat.ne_of_gt h]
  | succ j ih =>
    cases d with
    | zero => omega
    | succ d => simp [atomTable, ih (show j < d by omega), ih (show j < d+1 by omega)]

theorem headTable_zero_above {j d : ℕ} (h : j < d) : headTable j d = 0 := by
  apply sum_eq_zero
  intro i hi
  exact atomTable_zero_above (by have := mem_range.mp hi; omega)

theorem mass_le_cut {v : ℚ} (hv : 0 ≤ v) (N b : ℕ) (P : ℚ[X])
    (cut : ∀ d ≥ b, P.coeff d = 0) : mass v N P ≤ mass v b P := by
  by_cases fit : N ≤ b
  · exact sum_le_sum_of_subset_of_nonneg (range_mono fit) (fun d _ _ ↦ by positivity)
  · apply le_of_eq
    symm
    apply sum_subset (range_mono (by omega : b ≤ N))
    intro d _ hd
    simp [cut d (by simpa using hd)]

def seed : ℚ[X] := gn 7 - C (headTable 7 0)

theorem seed_mass {v : ℚ} (hv : 0 ≤ v) (N : ℕ) :
    mass v N seed ≤ ∑ d ∈ range 8, |headTable 7 d - (if d=0 then headTable 7 0 else 0)| *v^d := by
  have cf (d : ℕ) : seed.coeff d = headTable 7 d - (if d=0 then headTable 7 0 else 0) := by
    simp [seed, headTable_eq, coeff_C]
  have cut (d : ℕ) (hd : 8 ≤ d) : seed.coeff d = 0 := by
    rw [cf, headTable_zero_above (by omega), if_neg (by omega)]
    norm_num
  simpa only [mass,cf] using mass_le_cut hv N 8 seed cut

theorem atom_seven_mass {v : ℚ} (hv : 0 ≤ v) (N : ℕ) :
    mass v N (gnAtom 7) ≤ ∑ d ∈ range 8, |atomTable 7 d| *v^d := by
  have cut (d : ℕ) (hd : 8 ≤ d) : (gnAtom 7).coeff d = 0 :=
    (atomTable_eq ..).trans (atomTable_zero_above (by omega))
  simpa only [mass,atomTable_eq] using mass_le_cut hv N 8 (gnAtom 7) cut

end LongCycleBounds.DescentDerangement
