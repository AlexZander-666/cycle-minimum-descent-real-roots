import LongCycleBounds.DescentAlphabetFactorODE
import LongCycleBounds.DescentMeshFullKernel

/-! The finite inventory product for the alphabet polynomial of the actual descent row. -/
noncomputable section
namespace LongCycleBounds.DescentMesh
open Finset Polynomial DescentNecklace

def realMass (j : ℕ) : ℝ[X] := (mobiusPolynomial j).map (Rat.castHom ℝ)
def cutoffMass (k j : ℕ) : ℝ[X] := if j < k then 0 else realMass j

def alphabetProduct (H k : ℕ) : BiPoly :=
  ∏ i : Fin H, expand ℝ[X] (i.val+1) (inventoryFactor H (cutoffMass k (i.val+1)))

def alphabetKernel (H k : ℕ) : BiPoly :=
  ∑ i : Fin H, ((i.val+1:ℕ):BiPoly)*expand ℝ[X] (i.val+1) (inventoryKernel H (cutoffMass k (i.val+1)))

theorem alphabet_product_ode (H k : ℕ) :
    X^(H+1) ∣ alphabetKernel H k * alphabetProduct H k - eulerOp (alphabetProduct H k) :=
  product_inventory_ode univ _ _ H (fun i _ ↦ expanded_inventory_ode H (Nat.succ_pos i.val) _)

private theorem factor_formula (n j : ℕ) (M : ℝ[X]) :
    expand ℝ[X] j (inventoryFactor n M) =
    ∑ a : Fin (n+1), monomial (j*a.val) (Ring.multichoose M a.val) := by
  rw [Fin.sum_univ_eq_sum_range (fun a ↦ monomial (j*a) (Ring.multichoose M a))]
  simp only [inventoryFactor,coefficientBox,map_sum,expand_monomial]
  apply sum_congr rfl
  intro i _
  rw [Nat.mul_comm]

private theorem prod_mon {ι : Type*} (s : Finset ι) (e : ι → ℕ) (c : ι → ℝ[X]) :
    (∏ i ∈ s, monomial (e i) (c i)) = monomial (∑ i ∈ s, e i) (∏ i ∈ s, c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp only [prod_insert hi,sum_insert hi,ih,monomial_mul_monomial]

theorem alphabet_product_coeff (n k : ℕ) :
    (alphabetProduct n k).coeff n = (profilePolynomial n k).map (Rat.castHom ℝ) := by
  classical
  simp only [alphabetProduct,factor_formula,Fintype.prod_sum,prod_mon,finsetSum_coeff,coeff_monomial]
  let valid (f : Fin n → Fin (n+1)) : Prop :=
    (∑ i, (i.val+1)*(f i).val) = n ∧ ∀ i, i.val+1 < k → f i = 0
  let weight (f : Fin n → Fin (n+1)) := ∏ i, Ring.multichoose (realMass (i.val+1)) (f i).val
  have cv : (profilePolynomial n k).map (Rat.castHom ℝ) =
      ∑ f ∈ univ.filter valid, weight f := by
    unfold profilePolynomial
    simp only [Polynomial.map_sum, Polynomial.map_prod]
    change (∑ p : PositiveLengthProfile n k, ∏ i : Fin n,
      (Polynomial.mapRingHom (Rat.castHom ℝ)) (Ring.multichoose (mobiusPolynomial (i.val+1)) (p.val i).val)) = _
    simp_rw [Ring.map_multichoose]
    exact (Finset.sum_subtype (p := valid) (univ.filter valid)
      (fun _ ↦ by simp only [mem_filter,mem_univ,true_and]) weight).symm
  rw [cv,sum_filter]
  apply sum_congr rfl
  intro f _
  by_cases total : (∑ i, (i.val+1)*(f i).val)=n
  · by_cases cutoff : ∀ i : Fin n, i.val+1 < k → f i=0
    · rw [if_pos total, if_pos (show valid f from ⟨total,cutoff⟩)]
      apply prod_congr rfl
      intro i _
      by_cases c : i.val+1<k
      · simp [cutoffMass,c,cutoff i c]
      · simp [cutoffMass,c]
    · rw [if_pos total, if_neg (show ¬valid f from fun a ↦ cutoff a.2)]
      push Not at cutoff
      obtain ⟨i,hi,ha⟩ := cutoff
      apply Finset.prod_eq_zero (mem_univ i)
      have nz : (f i).val ≠ 0 := fun eq ↦ ha (Fin.ext eq)
      obtain ⟨v,hv⟩ := Nat.exists_eq_succ_of_ne_zero nz
      simp [cutoffMass,hi,hv,Ring.multichoose_zero_succ]
  · rw [if_neg total,if_neg (show ¬valid f from fun a ↦ total a.1)]

#print axioms alphabet_product_ode
#print axioms alphabet_product_coeff
end LongCycleBounds.DescentMesh
