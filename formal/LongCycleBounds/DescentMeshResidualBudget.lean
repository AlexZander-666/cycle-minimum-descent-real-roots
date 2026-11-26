import LongCycleBounds.DescentMeshAtoms
import LongCycleBounds.DescentMeshGlobalBudget

/-! The signed coefficient expansion in ordered bad log terms and an admissible residual. -/
noncomputable section
namespace LongCycleBounds.DescentMesh
open Finset Real FixedCycleCount

/-- Taylor orders 1 through T. The empty word contributes the separate leading term. -/
abbrev LogWord (k N B T : ℕ) := (i : Fin T) × (Fin (i.val+1) → LogAtom k N B)

def wordLength {k N B T} (w : LogWord k N B T) := ∑ i, atomLength (w.2 i)
def wordLoss {k N B T} (w : LogWord k N B T) := ∑ i, atomLoss (w.2 i)
def wordCoefficient {k N B T} (w : LogWord k N B T) : ℝ :=
  (∏ i, atomCoefficient (w.2 i))/((w.1.val+1).factorial:ℝ)

theorem word_loss {k N B T} (hk : 3≤k) (w : LogWord k N B T) :
    wordLength w ≤ 2*wordLoss w := by
  unfold wordLength wordLoss
  rw [mul_sum]
  exact sum_le_sum fun i _ ↦ (atom_loss hk (w.2 i)).2

theorem word_mass_budget {k : ℕ} (hk : 3≤k) (N B T : ℕ) {v : ℝ} (hv : 0≤v) (h1 : v<1) :
    (∑ w : LogWord k N B T, |wordCoefficient w| * v^(wordLoss w)) ≤ exp (badEnvelope v)-1 := by
  classical
  rw [Fintype.sum_sigma]
  apply le_trans _ (exponential_atom_budget hk N B T hv h1)
  apply le_of_eq
  rw [← Fin.sum_univ_eq_sum_range]
  apply sum_congr rfl
  intro i _
  unfold tupleMass
  rw [sum_div]
  apply sum_congr rfl
  intro w _
  simp only [wordCoefficient,wordLoss,abs_div,abs_prod,Nat.abs_cast,prod_mul_distrib,
    prod_pow_eq_pow_sum]
  ring

/-- Real source coefficient expanded in the logarithm of the necklace product with a
good residual. This definition is finite for every choice of the bounding box. -/
def expandedCoefficient (n k N B T h : ℕ) : ℝ :=
  (if h=n then allowedFraction n k else 0) +
  ∑ w : LogWord k N B T, if wordLength w ≤ n ∧ h=n-wordLoss w then
     allowedFraction (n-wordLength w) k * wordCoefficient w else 0

/-- Collect the absolute sizes by alphabet degree. Every ordered word is counted at
most once; selecting lengths at most n also excludes any truncated subtraction artifact. -/
theorem expanded_loss_le (n k N B T : ℕ) {v : ℝ} (hv : 0≤v) :
    lossNorm n (expandedCoefficient n k N B T) v ≤
    ∑ w : LogWord k N B T, if wordLength w ≤ n then
       allowedFraction (n-wordLength w) k * (|wordCoefficient w| * v^(wordLoss w)) else 0 := by
  classical
  have leLoss (w : LogWord k N B T) : wordLoss w ≤ wordLength w :=
    sum_le_sum fun i _ ↦ Nat.sub_le _ _
  let f (h : ℕ) (w : LogWord k N B T) : ℝ := if wordLength w ≤ n ∧ h=n-wordLoss w then
     allowedFraction (n-wordLength w) k * (|wordCoefficient w| * v^(wordLoss w)) else 0
  have per (h : ℕ) (hh : h ∈ Ico 1 n) : |expandedCoefficient n k N B T h| *v^(n-h) ≤ ∑ w, f h w := by
    have ne : h≠n := (mem_Ico.mp hh).2.ne
    simp only [expandedCoefficient,if_neg ne,zero_add]
    apply (mul_le_mul_of_nonneg_right (abs_sum_le_sum_abs _ _) (pow_nonneg hv _)).trans
    rw [sum_mul]
    apply sum_le_sum
    intro w _
    dsimp only [f]
    split_ifs with e
    · have eq : n-h=wordLoss w := by have := leLoss w; omega
      rw [eq,abs_mul,abs_of_nonneg (allowedFraction_nonneg ..),mul_assoc]
    · simp
  apply (sum_le_sum per).trans
  rw [sum_comm]
  apply sum_le_sum
  intro w _
  dsimp only [f]
  by_cases len : wordLength w ≤ n
  · simp only [len,true_and,ite_true,sum_ite_eq']
    split_ifs
    · rfl
    · exact mul_nonneg (allowedFraction_nonneg ..) (by positivity)
  · simp [len]

/-- Nonempty and empty residuals incur different constants. Their sum is bounded
after shrinking the radius in precisely the full-length Taylor contributions. -/
theorem expanded_loss_envelope {n k : ℕ} (hk : 3≤k) (hn : k≤n) (N B T : ℕ)
    {v V : ℝ} (hv : 0≤v) (hV : 0<V) (vr : v≤V) (cap : V<1) :
    lossNorm n (expandedCoefficient n k N B T) v ≤ allowedFraction n k *
      (2*(exp (badEnvelope v)-1) + 2*(k:ℝ)*(v/V)^((n+1)/2)*(exp (badEnvelope V)-1)) := by
  classical
  let u (x : ℝ) (w : LogWord k N B T) := |wordCoefficient w| * x^(wordLoss w)
  let z := (v/V)^((n+1)/2)
  have z0 : 0 ≤ z := pow_nonneg (div_nonneg hv hV.le) _
  let p := allowedFraction n k
  have p0 : 0 ≤ p := allowedFraction_nonneg .. 
  have point (w : LogWord k N B T) (_ : w ∈ univ) :
      (if wordLength w ≤ n then allowedFraction (n-wordLength w) k * u v w else 0) ≤
      2*p*u v w + (2*(k:ℝ)*p*z)*u V w := by
    have v0 : 0 ≤ u v w := mul_nonneg (abs_nonneg _) (pow_nonneg hv _)
    have V0 : 0 ≤ u V w := mul_nonneg (abs_nonneg _) (pow_nonneg hV.le _)
    split_ifs with valid
    · rcases valid.lt_or_eq with sm | fill
      · exact (mul_le_mul_of_nonneg_right (nonempty_residual (by omega) hn (Nat.sub_pos_of_lt sm)) v0).trans
          (le_add_of_nonneg_right (by positivity))
      · have support (a : LogWord k N B T) (mem : a ∈ ({w}:Finset _)) : n ≤ 2*wordLoss a := by
          obtain rfl := mem_singleton.mp mem
          rw [← fill]; exact word_loss hk _
        have h := reweight_empty {w} wordLoss (fun a ↦ |wordCoefficient a|) support hv hV vr
        simp only [sum_singleton,abs_abs] at h
        rw [abs_of_nonneg v0] at h
        rw [fill,Nat.sub_self,allowedFraction_zero,one_mul]
        have hp := mul_le_mul_of_nonneg_right (empty_residual (by omega) hn) (mul_nonneg z0 V0)
        change u v w ≤ z*u V w at h
        dsimp only [p] at *
        nlinarith only [h,hp,mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) p0) v0]
    · positivity
  refine (expanded_loss_le n k N B T hv).trans ((sum_le_sum point).trans ?_)
  rw [sum_add_distrib, ← mul_sum, ← mul_sum]
  have h1 := mul_le_mul_of_nonneg_left (word_mass_budget hk N B T hv (vr.trans_lt cap))
    (show 0≤2*p by positivity)
  have h2 := mul_le_mul_of_nonneg_left (word_mass_budget hk N B T hV.le cap)
    (show 0≤2*(k:ℝ)*p*z by positivity)
  change 2*p*(∑ w, u v w) ≤ _ at h1
  change 2*(k:ℝ)*p*z*(∑ w, u V w) ≤ _ at h2
  change _ ≤ p*(2*(exp (badEnvelope v)-1) + 2*(k:ℝ)*z*(exp (badEnvelope V)-1))
  linarith only [h1,h2]

#print axioms word_mass_budget
#print axioms expanded_loss_envelope
end LongCycleBounds.DescentMesh
