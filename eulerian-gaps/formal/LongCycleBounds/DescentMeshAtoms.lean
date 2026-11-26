import LongCycleBounds.DescentMeshLogMajorant

/-! A finite alphabet of all bad Möbius decorations; the scalar logarithmic envelope
controls exponential products with their exact factorials. -/
noncomputable section
namespace LongCycleBounds.DescentMesh
open Finset ArithmeticFunction Real
open scoped Moebius

/-- The zero-loss decoration (b,d)=(1,1) is removed only in the primitive summand. -/
abbrev LogAtom (k N B : ℕ) := (j : ↥(Icc k N)) ×
  (↥(j.val.divisors.erase 1) ⊕ ((_b : ↥(Icc 2 B)) × ↥(j.val.divisors)))

def atomRepeat {k N B : ℕ} (z : LogAtom k N B) : ℕ := z.2.elim (fun _ ↦ 1) (fun a ↦ a.1.val)
def atomDivisor {k N B : ℕ} (z : LogAtom k N B) : ℕ := z.2.elim Subtype.val (fun a ↦ a.2.val)
def atomLength {k N B : ℕ} (z : LogAtom k N B) : ℕ := z.1.val * atomRepeat z
def atomLoss {k N B : ℕ} (z : LogAtom k N B) : ℕ := atomLength z-z.1.val/atomDivisor z
def atomCoefficient {k N B : ℕ} (z : LogAtom k N B) : ℝ :=
  (μ (atomDivisor z) : ℝ)/((z.1.val:ℝ)*(atomRepeat z:ℝ))

theorem atom_loss {k N B : ℕ} (hk : 3≤k) (z : LogAtom k N B) :
    2 ≤ atomLoss z ∧ atomLength z ≤ 2*atomLoss z := by
  obtain ⟨j,z⟩ := z
  have h := (mem_Icc.mp j.prop).1
  cases z with
  | inl d =>
    exact decoration_loss (hk.trans h) (by decide : 1≤1) (Nat.pos_of_mem_divisors
      (mem_erase.mp d.prop).2) (Or.inr (mem_erase.mp d.prop).1)
  | inr p =>
    obtain ⟨b,d⟩ := p
    have two := (mem_Icc.mp b.prop).1
    exact decoration_loss (hk.trans h) (by omega : 1≤b.val) (Nat.pos_of_mem_divisors d.prop)
      (Or.inl (by omega : b.val≠1))

private theorem scalar_abs (a : ℝ) (j b : ℕ) (v : ℝ) (l : ℕ) :
    |a/((j:ℝ)*b)| *v^l = |a| *v^l/((j:ℝ)*b) := by
  rw [abs_div, abs_of_nonneg (by positivity : 0≤(j:ℝ)*b)]
  ring

/-- Equality, before inequalities, to the three-index Möbius log sum. -/
theorem atom_mass (k N B : ℕ) (v : ℝ) :
    (∑ z : LogAtom k N B, |atomCoefficient z| *v^(atomLoss z)) =
      ∑ j ∈ Icc k N, (primitiveCost j v + ∑ b ∈ Icc 2 B, repeatedCost j b v) := by
  classical
  rw [Fintype.sum_sigma]
  conv_rhs => rw [← Finset.sum_coe_sort]
  apply sum_congr rfl
  intro j _
  rw [Fintype.sum_sum_type]
  congr 1
  · simp only [atomCoefficient,atomDivisor,atomRepeat,atomLoss,atomLength,Sum.elim_inl,
      Nat.cast_one,mul_one,abs_div,Nat.abs_cast]
    unfold primitiveCost
    rw [sum_div]
    conv_rhs => rw [← Finset.sum_coe_sort]
    apply sum_congr rfl
    intro d _
    ring
  · rw [Fintype.sum_sigma]
    conv_rhs => rw [← Finset.sum_coe_sort]
    apply sum_congr rfl
    intro b _
    unfold repeatedCost
    rw [sum_div]
    conv_rhs => rw [← Finset.sum_coe_sort]
    simp only [atomCoefficient,atomDivisor,atomRepeat,atomLoss,atomLength,
      Sum.elim_inr,scalar_abs]

def tupleMass {α : Type*} [Fintype α] (w : α → ℝ) (h : ℕ) : ℝ :=
  ∑ word : Fin h → α, ∏ i, w (word i)

theorem tupleMass_eq {α : Type*} [Fintype α] (w : α → ℝ) (h : ℕ) :
    tupleMass w h = (∑ a, w a)^h := by
  classical
  unfold tupleMass
  rw [← Fintype.prod_sum]
  simp

/-- All nonempty Taylor terms of the positive majorant, even before any length rejection. -/
theorem exponential_atom_budget {k : ℕ} (hk : 3≤k) (N B T : ℕ) {v : ℝ}
    (hv : 0≤v) (h1 : v<1) :
    (∑ h ∈ range T, tupleMass (fun z : LogAtom k N B ↦ |atomCoefficient z| *v^(atomLoss z))
       (h+1)/((h+1).factorial:ℝ)) ≤ exp (badEnvelope v)-1 := by
  let s := ∑ z : LogAtom k N B, |atomCoefficient z| * v^(atomLoss z)
  have s0 : 0 ≤ s := sum_nonneg fun _ _ ↦ by positivity
  have cap : s ≤ badEnvelope v := (atom_mass k N B v).le.trans (bad_log_majorant hk N B hv h1)
  have h := (Real.sum_le_exp_of_nonneg s0 (T+1)).trans (exp_le_exp.mpr cap)
  rw [sum_range_succ',pow_zero,Nat.factorial_zero,Nat.cast_one,div_one] at h
  simp_rw [tupleMass_eq]
  linarith only [h]

#print axioms atom_loss
#print axioms atom_mass
#print axioms exponential_atom_budget
end LongCycleBounds.DescentMesh
