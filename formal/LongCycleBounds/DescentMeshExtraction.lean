import LongCycleBounds.DescentMeshExpandedSign

/-! Exact coefficient extraction in the polynomial ring ℝ[q][z] from the finite
product of the good residual polynomial and the signed bad logarithm's Taylor series. -/
noncomputable section
namespace LongCycleBounds.DescentMesh
open Finset Polynomial FixedCycleCount
abbrev BiPoly := Polynomial (Polynomial ℝ)

def biTerm (length degree : ℕ) (a : ℝ) : BiPoly := monomial length (monomial degree a)

@[simp] theorem biTerm_one : biTerm 0 0 1 = 1 := by simp [biTerm]
theorem biTerm_mul (l d m e : ℕ) (a b : ℝ) :
    biTerm l d a * biTerm m e b = biTerm (l+m) (d+e) (a*b) := by
  simp only [biTerm,monomial_mul_monomial]

theorem biTerm_product {α : Type*} (I : Finset α) (l d : α→ℕ) (a : α→ℝ) :
    (∏ i ∈ I, biTerm (l i) (d i) (a i)) = biTerm (∑ i ∈ I, l i) (∑ i ∈ I, d i) (∏ i ∈ I, a i) := by
  classical
  induction I using Finset.induction with
  | empty => simp
  | insert i I hi ih => simp [hi,ih,biTerm_mul]

/-- Raw alphabet degree j/d, written as length minus its marked loss. -/
def badLogPolynomial (k N B : ℕ) : BiPoly :=
  ∑ z : LogAtom k N B, biTerm (atomLength z) (atomLength z-atomLoss z) (atomCoefficient z)

/-- The ordinary, signed exponential Taylor polynomial, including order zero. -/
def badTaylor (k N B T : ℕ) : BiPoly :=
  1+∑ h ∈ range T, biTerm 0 0 (((h+1).factorial:ℝ)⁻¹) * (badLogPolynomial k N B)^(h+1)

def goodPolynomial (n k : ℕ) : BiPoly :=
  ∑ s ∈ range (n+1), biTerm s s (allowedFraction s k)

theorem word_degree {k N B T} (w : LogWord k N B T) :
    ∑ i, (atomLength (w.2 i)-atomLoss (w.2 i)) = wordLength w-wordLoss w := by
  have hh : ∑ i, ((atomLength (w.2 i)-atomLoss (w.2 i))+atomLoss (w.2 i)) = wordLength w := by
    apply sum_congr rfl
    intro i _
    exact Nat.sub_add_cancel (Nat.sub_le ..)
  rw [sum_add_distrib] at hh
  unfold wordLoss
  omega

theorem badTaylor_eq_words (k N B T : ℕ) : badTaylor k N B T =
    1+∑ w : LogWord k N B T, biTerm (wordLength w) (wordLength w-wordLoss w) (wordCoefficient w) := by
  classical
  unfold badTaylor
  congr 1
  rw [Fintype.sum_sigma, ← Fin.sum_univ_eq_sum_range]
  apply sum_congr rfl
  intro h _
  have pw : (badLogPolynomial k N B)^(h.val+1) = ∑ w : Fin (h.val+1)→LogAtom k N B,
      ∏ i, biTerm (atomLength (w i)) (atomLength (w i)-atomLoss (w i)) (atomCoefficient (w i)) := by
    rw [← Fintype.prod_sum (fun (_ : Fin (h.val+1)) (z : LogAtom k N B) ↦
      biTerm (atomLength z) (atomLength z-atomLoss z) (atomCoefficient z))]
    simp [badLogPolynomial]
  rw [pw,mul_sum]
  apply sum_congr rfl
  intro w _
  rw [biTerm_product,biTerm_mul,zero_add,zero_add]
  change biTerm (wordLength ⟨h,w⟩) _ _ = _
  rw [word_degree (k:=k) (N:=N) (B:=B) (T:=T) ⟨h,w⟩]
  unfold wordCoefficient
  simp only [div_eq_inv_mul]

private theorem coeff_good_term (n k l d : ℕ) (a : ℝ) :
    ((goodPolynomial n k*biTerm l d a).coeff n) =
      if l≤n then monomial (n-l+d) (allowedFraction (n-l) k*a) else 0 := by
  classical
  unfold goodPolynomial
  rw [sum_mul,finsetSum_coeff]
  simp only [biTerm,monomial_mul_monomial,coeff_monomial]
  by_cases hl : l≤n
  · rw [if_pos hl, sum_eq_single (n-l)]
    · simp [Nat.sub_add_cancel hl]
    · intro i _ ine
      simp [show i+l≠n by omega]
    · simp
  · simp [hl,show ∀ i, i+l≠n by omega]

/-- Full signed algebraic matching with the precise coefficient used in the analytic
estimates; no interchange of an infinite power series is needed. -/
theorem good_mul_badTaylor_coeff (n k N B T d : ℕ) :
    ((goodPolynomial n k * badTaylor k N B T).coeff n).coeff d =
      expandedCoefficient n k N B T d := by
  classical
  rw [badTaylor_eq_words,mul_add,mul_one,mul_sum,coeff_add,coeff_add,finsetSum_coeff,finsetSum_coeff]
  unfold expandedCoefficient
  congr 1
  · have h := coeff_good_term n k 0 0 1
    simpa [coeff_monomial,eq_comm] using congrArg (fun f : Polynomial ℝ ↦ f.coeff d) h
  · apply sum_congr rfl
    intro w _
    rw [coeff_good_term]
    by_cases le : wordLength w≤n
    · have loss : wordLoss w≤wordLength w := sum_le_sum fun i _ ↦ Nat.sub_le ..
      rw [if_pos le,coeff_monomial,show n-wordLength w+(wordLength w-wordLoss w)=n-wordLoss w by omega]
      simp [le,eq_comm]
    · simp [le]

#print axioms badTaylor_eq_words
#print axioms good_mul_badTaylor_coeff
end LongCycleBounds.DescentMesh
