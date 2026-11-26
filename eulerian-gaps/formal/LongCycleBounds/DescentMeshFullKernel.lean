import LongCycleBounds.DescentMeshGoodODE
import LongCycleBounds.DescentAlphabetPolynomial

/-! Recombine the good length-j generator with all nonleading joint Möbius
generators to recover the raw alphabet logarithmic derivative. -/
noncomputable section
namespace LongCycleBounds.DescentMesh
open Finset Polynomial ArithmeticFunction
open scoped Moebius

def rawKernel (k H : ℕ) : BiPoly := ∑ j ∈ Icc k H, ∑ b ∈ Icc 1 H,
  monomial (j*b) (∑ d ∈ j.divisors, monomial (j/d) ((μ d:ℤ):ℝ))

private theorem euler_sum {α : Type*} (I : Finset α) (f : α → BiPoly) :
    eulerOp (∑ a ∈ I, f a) = ∑ a ∈ I, eulerOp (f a) := by
  classical
  induction I using Finset.induction with
  | empty => simp [eulerOp]
  | insert a I ha ih =>
    rw [sum_insert ha,sum_insert ha,← ih]
    unfold eulerOp
    rw [derivative_add,mul_add]

private theorem euler_bi (l d : ℕ) (a : ℝ) :
    eulerOp (biTerm l d a) = biTerm l d ((l:ℝ)*a) := by
  ext1 s
  rw [euler_coeff]
  simp only [biTerm,coeff_monomial]
  split_ifs with h
  · subst s; rw [← C_eq_natCast,C_mul_monomial]
  · simp

private theorem atom_decode {k N B : ℕ} (hk : 3≤k) (z : LogAtom k N B) :
    eulerOp (biTerm (atomLength z) (atomLength z-atomLoss z) (atomCoefficient z)) =
    biTerm (atomLength z) (z.1.val/atomDivisor z) ((μ (atomDivisor z):ℤ):ℝ) := by
  have jp : 0<z.1.val := by have h := (mem_Icc.mp z.1.prop).1; omega
  have bp : 0<atomRepeat z := by
    obtain ⟨j,z⟩ := z
    cases z with
    | inl d => exact Nat.zero_lt_one
    | inr a => have h := (mem_Icc.mp a.1.prop).1; exact lt_of_lt_of_le (by decide : 0<2) h
  have order : z.1.val/atomDivisor z ≤ atomLength z :=
    (Nat.div_le_self ..).trans (Nat.le_mul_of_pos_right _ bp)
  rw [euler_bi,show atomLength z-atomLoss z=z.1.val/atomDivisor z from Nat.sub_sub_self order]
  congr 2
  unfold atomCoefficient atomLength
  push_cast
  field_simp

/-- The two independently controlled pieces equal the full raw divisor kernel,
including the d=1 principal term at b=1 exactly once. -/
theorem good_add_bad_kernel {k H : ℕ} (hk : 3≤k) (hH : 1≤H) :
    goodKernel H k + eulerOp (badLogPolynomial k H H) = rawKernel k H := by
  classical
  unfold goodKernel badLogPolynomial rawKernel
  rw [euler_sum]
  simp_rw [atom_decode hk]
  rw [Fintype.sum_sigma]
  conv_lhs => arg 1; rw [← Finset.sum_coe_sort]
  conv_rhs => rw [← Finset.sum_coe_sort]
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro j _
  rw [Fintype.sum_sum_type]
  have jpos : 0<j.val := by have h := (mem_Icc.mp j.prop).1; omega
  have bin : Icc 1 H = insert 1 (Icc 2 H) := by ext i; simp; omega
  rw [bin,sum_insert (by simp)]
  simp only [Nat.mul_one]
  have prim : biTerm j.val j.val 1 +
       (∑ d : ↥(j.val.divisors.erase 1), biTerm j.val (j.val/d.val) ((μ d.val:ℤ):ℝ)) =
       monomial j.val (∑ d ∈ j.val.divisors, monomial (j.val/d) ((μ d:ℤ):ℝ)) := by
    unfold biTerm
    rw [map_sum,← sum_erase_add _ _ (Nat.one_mem_divisors.mpr jpos.ne')]
    simp only [Nat.div_one,moebius_apply_one,Int.cast_one,add_comm]
    conv_rhs => arg 2; rw [← sum_coe_sort]
  have reps : (∑ p : ((_b : ↥(Icc 2 H)) × ↥j.val.divisors),
       biTerm (j.val*p.1.val) (j.val/p.2.val) ((μ p.2.val:ℤ):ℝ)) =
       ∑ b ∈ Icc 2 H, monomial (j.val*b) (∑ d ∈ j.val.divisors, monomial (j.val/d) ((μ d:ℤ):ℝ)) := by
    rw [Fintype.sum_sigma]
    conv_rhs => rw [← sum_coe_sort]
    apply sum_congr rfl
    intro b _
    rw [map_sum]
    conv_rhs => rw [← sum_coe_sort]
    rfl
  dsimp only [atomLength,atomRepeat,atomDivisor,Sum.elim_inl,Sum.elim_inr,Nat.mul_one] at *
  rw [← add_assoc, ← prim, ← reps]
  simp only [Nat.mul_one]

#print axioms good_add_bad_kernel
end LongCycleBounds.DescentMesh
