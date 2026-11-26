import LongCycleBounds.DescentAlphabetProduct
import LongCycleBounds.DescentEulerianReadout
import LongCycleBounds.DescentMeshSignedRecurrence
import LongCycleBounds.DescentMeshExpandedSign

/-! Central grid sign theorem for the actual ordinary descent polynomial. -/
noncomputable section
namespace LongCycleBounds.DescentMesh
open Finset Polynomial DescentNecklace DescentTwoLetters Real

private theorem positive_range (H : ℕ) : Icc 1 H = (range H).image Nat.succ := by
  ext j
  cases j <;> simp

private theorem one_kernel (H j : ℕ) (M : ℝ[X]) :
    (j:BiPoly)*expand ℝ[X] j (inventoryKernel H M) =
    ∑ b ∈ Icc 1 H, monomial (j*b) ((j:ℝ[X])*M) := by
  unfold inventoryKernel coefficientBox
  rw [sum_range_succ',map_add,map_sum,positive_range,sum_image (fun a _ b _ h ↦ Nat.succ.inj h)]
  simp only [Nat.succ_ne_zero,if_false,if_true,map_zero,add_zero,mul_sum,expand_monomial]
  apply sum_congr rfl
  intro i _
  rw [← C_eq_natCast,C_mul_monomial,Nat.mul_comm]

theorem alphabet_kernel_eq_raw {k : ℕ} (hk : 1 ≤ k) (H : ℕ) :
    alphabetKernel H k = rawKernel k H := by
  unfold alphabetKernel rawKernel
  rw [Fin.sum_univ_eq_sum_range (fun i ↦ ((i+1:ℕ):BiPoly)*expand ℝ[X] (i+1)
    (inventoryKernel H (cutoffMass k (i+1))))]
  simp_rw [one_kernel]
  rw [← sum_image (g:=Nat.succ) (s:=range H) (f:=fun j ↦ ∑ b ∈ Icc 1 H,
    monomial (j*b) ((j:ℝ[X])*cutoffMass k j)) (fun a _ b _ h ↦ Nat.succ.inj h),← positive_range]
  have sub : Icc k H ⊆ Icc 1 H := fun j h ↦ mem_Icc.mpr ⟨hk.trans (mem_Icc.mp h).1,(mem_Icc.mp h).2⟩
  rw [← sum_subset sub (fun j h hn ↦ by
    have hj : j<k := by have := mem_Icc.mp h; by_contra! h'; exact hn (mem_Icc.mpr ⟨h',this.2⟩)
    simp [cutoffMass,hj])]
  apply sum_congr rfl
  intro j hj
  have hjk := (mem_Icc.mp hj).1
  have h := rawDivisors_eq_mobiusPolynomial (hk.trans hjk)
  change (∑ b ∈ Icc 1 H, monomial (j*b) ((j:ℝ[X])*cutoffMass k j)) =
    ∑ b ∈ Icc 1 H, monomial (j*b) (rawDivisors j)
  simp only [cutoffMass,if_neg (Nat.not_lt.mpr hjk),realMass,h]

theorem alphabet_product_zero (H k : ℕ) : (alphabetProduct H k).coeff 0 = 1 := by
  change constantCoeff (∏ i : Fin H, _) = _
  rw [map_prod]
  apply prod_eq_one
  intro i _
  change (expand ℝ[X] (i.val+1) (inventoryFactor H _)).coeff 0 = 1
  rw [coeff_expand (Nat.succ_pos i.val),if_pos (dvd_zero _),Nat.zero_div]
  exact (coeff_box (Nat.zero_le H) _).trans (Ring.multichoose_zero_right _)

theorem profile_eq_expansion {n k : ℕ} (hk : 3≤k) (hn : 1≤n) :
    (profilePolynomial n k).map (Rat.castHom ℝ) = expansionRow k n n := by
  rw [← alphabet_product_coeff]
  apply expansionRow_unique hk hn (alphabetProduct n k).coeff (alphabet_product_zero n k) _ (le_refl n)
  intro s _ hs
  have h := X_pow_dvd_iff.mp (alphabet_product_ode n k) s (by omega)
  rw [coeff_sub,euler_coeff,alphabet_kernel_eq_raw (by omega),kernel_step (by omega) hs] at h
  exact (sub_eq_zero.mp h).symm

theorem actual_expanded_readout {n k : ℕ} (hk : 3≤k) (hn : 1≤n) :
    (row n k).map (Int.castRingHom ℝ) = descentTransform n (expandedCoefficient n k n n n) := by
  rw [original_eq_descentTransform hn]
  apply congrArg (descentTransform n)
  funext d
  have h := congrArg (fun f : ℝ[X] ↦ f.coeff d) (profile_eq_expansion hk hn)
  rw [← good_mul_badTaylor_coeff n k n n n d]
  rw [coeff_map] at h
  have cast (x : ℚ) : (Rat.castHom ℝ) x = (x:ℝ) := by
    simp
  rw [cast] at h
  exact h

theorem central_sign_actual {n k i : ℕ} (hk : 3≤k) (hn : k≤n) (h128 : 128≤n)
    {θ : ℝ} (lo : π/(2*sqrt ((n:ℝ)+1)) ≤ θ) (top : θ ≤ π/2)
    (phase : ((n:ℝ)+1)*θ=(i:ℝ)*π) :
    (-1:ℝ)^i*((row n k).map (Int.castRingHom ℝ)).eval (-exp (-(π*cos θ/sin θ))) < 0 := by
  rw [actual_expanded_readout hk (by omega)]
  exact central_sign_expanded hk hn h128 n n n lo top phase

#print axioms profile_eq_expansion
#print axioms central_sign_actual
end LongCycleBounds.DescentMesh
