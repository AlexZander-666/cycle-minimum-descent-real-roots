import LongCycleBounds.GeneralCycleSupports

namespace LongCycleBounds.FixedCycleCount
open LongCycles Finset Polynomial
open scoped Classical
noncomputable section

/-- Fraction of ordinary permutations satisfying the minimum cycle length constraint. -/
def allowedFraction (n k : ℕ) : ℝ := (enumerator n k).eval 1 / n.factorial

theorem allowedFraction_zero (k : ℕ) : allowedFraction 0 k = 1 := by
  have h (σ : Equiv.Perm (Fin 0)) : Allowed k σ := by intro i;exact Fin.elim0 i
  simp [allowedFraction,enumerator,h]

private theorem eulerian_eval_one (m : ℕ) : (eulerian m).eval 1=m.factorial := by
  simp [eulerian,eval_finsetSum,Fintype.card_perm]

private theorem anchor_coefficient {n a : ℕ} (ha : 1≤a) (han : a≤n) :
    ((n-1).choose (a-1):ℝ)*(a-1).factorial*((n-a).factorial:ℝ)=(n-1).factorial := by
  have h := Nat.choose_mul_factorial_mul_factorial (n:=n-1) (k:=a-1) (by omega)
  rw [show n-1-(a-1)=n-a by omega] at h
  exact_mod_cast h

theorem allowedFraction_recurrence {n k : ℕ} (hk : 2≤k) (hn : 0<n) :
    (n:ℝ)*allowedFraction n k=∑ a∈Icc k n,allowedFraction (n-a) k := by
  have pos : (0:ℝ)<n := by exact_mod_cast hn
  have fr := Nat.mul_factorial_pred hn.ne'
  have eq : (n.factorial:ℝ) = n*((n-1).factorial:ℝ) := by exact_mod_cast fr.symm
  have row := congrArg (Polynomial.eval 1) (Anchored.anchored_row_recurrence hk (⟨0,hn⟩ : Fin n))
  simp only [eval_finsetSum,eval_mul,eval_C,eval_X,one_mul,eulerian_eval_one] at row
  unfold allowedFraction
  rw [row,eq]
  field_simp
  rw [mul_sum]
  apply sum_congr rfl
  intro a ha
  obtain ⟨lo,hi⟩ := mem_Icc.mp ha
  have m := anchor_coefficient (by omega : 1≤a) hi
  field_simp
  linear_combination ((enumerator (n-a) k).eval 1)*m

theorem allowedFraction_nonneg (n k : ℕ) : 0≤allowedFraction n k := by
  unfold allowedFraction enumerator
  rw [eval_finsetSum]
  apply div_nonneg _ (by positivity)
  apply sum_nonneg
  intro σ _
  split <;> simp

theorem allowedFraction_le {n k : ℕ} (hk : 2≤k) (hn : 0<n) : allowedFraction n k≤1/(k:ℝ) := by
  have kp : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have np : (0:ℝ)<n := by exact_mod_cast hn
    have recurrence := allowedFraction_recurrence hk hn
    by_cases kn : k≤n
    · have last : n∈Icc k n := mem_Icc.mpr ⟨kn,le_rfl⟩
      let S := (Icc k n).erase n
      have split := sum_erase_add _ (fun a ↦ allowedFraction (n-a) k) last
      rw [←split,Nat.sub_self,allowedFraction_zero] at recurrence
      have each (a) (ha : a∈S) : allowedFraction (n-a) k≤1/(k:ℝ) := by
        obtain ⟨ne,inS⟩ := mem_erase.mp ha
        obtain ⟨lo,hi⟩ := mem_Icc.mp inS
        exact ih (n-a) (by omega) (by omega)
      have bound := sum_le_sum each
      have count : S.card=n-k := by dsimp [S];rw [card_erase_of_mem last,Nat.card_Icc];omega
      simp only [sum_const,nsmul_eq_mul,count,Nat.cast_sub kn] at bound
      apply (le_div_iff₀ kp).mpr
      apply le_of_mul_le_mul_left (a:=(n:ℝ)) _ np
      have endcap := mul_le_mul_of_nonneg_right bound kp.le
      dsimp [S] at endcap
      field_simp at endcap
      nlinarith only [recurrence,endcap]
    · rw [Icc_eq_empty_of_lt (by omega : n<k),sum_empty] at recurrence
      have z := (mul_eq_zero.mp recurrence).resolve_left np.ne'
      rw [z]
      positivity

#print axioms allowedFraction_recurrence
#print axioms allowedFraction_le
/-- Ordered sum of reciprocal cycle lengths at a fixed total length. -/
def reciprocalLengths (k n : ℕ) : ℕ → ℝ
  | 0 => if n=0 then 1 else 0
  | h+1 => ∑ a ∈ Icc k n, (1/(a:ℝ))*reciprocalLengths k (n-a) h
termination_by h => h

theorem ordered_at_one {k : ℕ} (hk : 2≤k) (n h : ℕ) :
    (CycleCount.orderedCycleRow n k h).eval 1 / n.factorial = reciprocalLengths k n h := by
  induction h generalizing n with
  | zero =>
    by_cases z : n=0 <;> simp [CycleCount.orderedCycleRow,reciprocalLengths,z]
  | succ h ih =>
    rw [CycleCount.orderedCycleRow,reciprocalLengths,eval_finsetSum,sum_div]
    apply sum_congr rfl
    intro a ha
    obtain ⟨lo,hi⟩ := mem_Icc.mp ha
    have ap : (0:ℝ)<a := by exact_mod_cast (show 0<a by omega)
    have f := Nat.choose_mul_factorial_mul_factorial (n:=n) (k:=a) hi
    rw [←Nat.mul_factorial_pred (by omega : a≠0)] at f
    have f' : (n.choose a:ℝ)*(a*(a-1).factorial : ℝ)*((n-a).factorial:ℝ) = n.factorial := by exact_mod_cast f
    simp only [eval_mul,eval_C,eval_X,one_mul,eulerian_eval_one]
    rw [←ih]
    field_simp
    linear_combination ((CycleCount.orderedCycleRow (n-a) k h).eval 1)*f'

theorem allowedFraction_ordered {k : ℕ} (hk : 2≤k) (n : ℕ) :
    allowedFraction n k = ∑ h ∈ range (n/k+1), reciprocalLengths k n h / h.factorial := by
  unfold allowedFraction
  rw [CycleCount.enumerator_ordered_cycle_rows hk,eval_finsetSum,sum_div]
  apply sum_congr rfl
  intro h _
  rw [eval_mul,eval_C,←ordered_at_one hk]
  ring

/-- All diagonal signed-pole factors, summed over the lengths other than the residual cycle. -/
def diagonalMass (j k : ℕ) : ℝ :=
  ∑ m ∈ range (j-k+1), ∑ h ∈ range (m/k+1), reciprocalLengths k m h / h.factorial

theorem diagonalMass_eq {k : ℕ} (hk : 2≤k) (j : ℕ) :
    diagonalMass j k = ∑ m ∈ range (j-k+1), allowedFraction m k := by
  unfold diagonalMass
  exact sum_congr rfl (fun m _ ↦ (allowedFraction_ordered hk m).symm)

theorem diagonalMass_step {p k : ℕ} (hk : 2≤k) (hp : k≤p) :
    diagonalMass (p+1) k-diagonalMass p k=allowedFraction (p+1-k) k := by
  rw [diagonalMass_eq hk,diagonalMass_eq hk,show p+1-k=p-k+1 by omega,sum_range_succ]
  ring

theorem diagonalMass_bounds {p k : ℕ} (hk : 2≤k) (hp : k≤p) :
    1≤diagonalMass p k ∧ 0≤diagonalMass (p+1) k-diagonalMass p k ∧
      diagonalMass (p+1) k-diagonalMass p k≤1/(k:ℝ) := by
  rw [diagonalMass_step hk hp,diagonalMass_eq hk]
  refine ⟨?_,allowedFraction_nonneg _ _,allowedFraction_le hk (by omega)⟩
  rw [←allowedFraction_zero k]
  exact single_le_sum (fun m _ ↦ allowedFraction_nonneg m k) (mem_range.mpr (by omega))

#print axioms allowedFraction_ordered
#print axioms diagonalMass_step
#print axioms diagonalMass_bounds

end
end LongCycleBounds.FixedCycleCount
