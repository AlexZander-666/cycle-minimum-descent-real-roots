import LongCycleBounds.DescentSignedKernel
import LongCycleBounds.DescentInverseEight

namespace LongCycleBounds.DescentMesh.SignedBounds
open Finset ArithmeticFunction Real
open scoped Moebius

/-- The integer multiplying the positive-loss logarithm after equal powers coalesce. -/
def signedSum (k h l : ℕ) : ℤ := ∑ d∈l.divisors with k ≤ h*d, μ d

def costQ (k i : ℕ) (v : ℚ) : ℚ :=
  (∑ h∈i.divisors with h<k ∧ h < i, (|signedSum k h (i/h)|:ℚ)*v^(i-h))/(i:ℚ)

def headQ (k : ℕ) (v : ℚ) : ℚ := ∑ i∈Icc 1 199, costQ k i v

/-- The complement counts only candidate divisors with h*d<k. -/
theorem abs_signed_le {k h l : ℕ} (hh : 0<h) (hl : 1<l) : |signedSum k h l| ≤ (k:ℤ) := by
  have whole : ∑ d∈l.divisors, μ d = 0 := by
    rw [←coe_mul_zeta_apply,moebius_mul_coe_zeta,one_apply_ne (by omega : l≠1)]
  have split := sum_filter_add_sum_filter_not l.divisors (fun d ↦ k ≤ h*d) (fun d ↦ μ d)
  let S := l.divisors.filter (fun d ↦ ¬k ≤ h*d)
  have sum0 : signedSum k h l = -(∑ d∈S,μ d) := by
    change (∑ d∈l.divisors with k ≤ h*d, μ d) = _
    rw [whole] at split
    exact eq_neg_of_add_eq_zero_left split
  have sub : S ⊆ range k := by
    intro d dm
    exact mem_range.mpr (lt_of_le_of_lt (Nat.le_mul_of_pos_left _ hh) (lt_of_not_ge (mem_filter.mp dm).2))
  rw [sum0,abs_neg]
  apply (abs_sum_le_sum_abs _ _).trans
  apply (sum_le_sum (g:=fun _ ↦ (1:ℤ)) fun d _ ↦ abs_moebius_le_one (n:=d)).trans
  have cc := card_le_card sub
  simpa using (show (S.card:ℤ) ≤ ((range k).card:ℤ) by exact_mod_cast cc)

private def tailQ (k : ℕ) (v : ℚ) : ℚ :=
  k^2*v^(200-k)/(200*(1-v))

def cSmall : ℕ→ℚ | 3 => 672/1000 | 4 => 634/1000 | 5 => 500/1000 | 6 => 478/1000 | _ => 281/1000
def cLarge : ℕ→ℚ | 3 => 1442/1000 | 4 => 1573/1000 | 5 => 1386/1000 | 6 => 1466/1000 | _ => 1068/1000

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
theorem evaluated {k : ℕ} (lo : 3 ≤ k) (hi : k ≤ 7) :
     headQ k (4/5) + tailQ k (4/5) ≤ cSmall k ∧
       headQ k (93/100) + tailQ k (93/100) ≤ cLarge k := by
  interval_cases k <;> decide +kernel

private theorem cost_nonneg (k i : ℕ) {v : ℚ} (hv : 0 ≤ v) : 0 ≤ costQ k i v := by
  unfold costQ
  positivity

private theorem cost_tail {i k : ℕ} (ii : 200 ≤ i) {v : ℚ} (v0 : 0 ≤ v) (v1 : v ≤ 1) :
    costQ k i v ≤ (k:ℚ)^2/200*v^(i-k) := by
  let S := i.divisors.filter (fun h ↦ h<k ∧ h < i)
  have sub : S ⊆ range k := fun d hd ↦ mem_range.mpr (mem_filter.mp hd).2.1
  have hcard : (S.card:ℚ) ≤ k := by exact_mod_cast (show S.card ≤ k by simpa using card_le_card sub)
  have each (h : ℕ) (hm : h∈S) : (|signedSum k h (i/h)|:ℚ)*v^(i-h) ≤ (k:ℚ)*v^(i-k) := by
    obtain ⟨hd,hk,hi⟩ := mem_filter.mp hm
    have hp := Nat.pos_of_mem_divisors hd
    have dv := Nat.dvd_of_mem_divisors hd
    have hq : 1 < i/h := by
      have e := Nat.mul_div_cancel' dv
      by_contra! bad
      have := Nat.mul_le_mul_left h bad
      omega
    exact mul_le_mul (by exact_mod_cast abs_signed_le (k:=k) hp hq)
      (pow_le_pow_of_le_one v0 v1 (Nat.sub_le_sub_left (by omega : h ≤ k) _))
      (pow_nonneg v0 _) (by positivity)
  have H := sum_le_sum each
  simp only [sum_const,nsmul_eq_mul] at H
  have both := H.trans (mul_le_mul_of_nonneg_right hcard (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg v0 _)))
  change _ / (i:ℚ) ≤ _
  have ip : (200:ℚ) ≤ i := by exact_mod_cast ii
  apply (div_le_iff₀ (by linarith : (0:ℚ) < i)).mpr
  apply both.trans
  have z := mul_le_mul_of_nonneg_left ip (show 0 ≤ (k:ℚ)^2/200*v^(i-k) by positivity)
  nlinarith only [z]

theorem sum_cost_bound {k : ℕ} (ku : k ≤ 7) (N : ℕ) {v : ℚ} (v0 : 0 ≤ v) (v1 : v<1) :
    (∑ i∈Icc 1 N,costQ k i v) ≤ headQ k v + tailQ k v := by
  let F := fun i ↦ costQ k i v
  have sub : Icc 1 N ⊆ Ico 1 (200+N) := by intro i hi; have := mem_Icc.mp hi; exact mem_Ico.mpr ⟨by omega,by omega⟩
  apply (sum_le_sum_of_subset_of_nonneg sub (fun i _ _ ↦ cost_nonneg k i v0)).trans
  change (∑ i∈Ico 1 (200+N),F i) ≤ _
  rw [←sum_Ico_consecutive F (show 1≤200 by decide) (by omega : 200≤200+N)]
  apply add_le_add
  · rw [show Ico 1 200=Icc 1 199 by ext i;simp;omega]
    rfl
  · rw [sum_Ico_eq_sum_range]
    have step (i : ℕ) : F (200+i) ≤ (k:ℚ)^2/200*v^(200-k+i) := by
      rw [show 200-k+i=200+i-k by omega]
      exact cost_tail (k:=k) (i:=200+i) (by omega) v0 v1.le
    apply (sum_le_sum fun i _ ↦ step i).trans
    simp_rw [pow_add,←mul_assoc]
    rw [←mul_sum]
    have q : (∑ i∈range (200+N-200),v^i) ≤ 1/(1-v) := by
      apply (le_div_iff₀ (sub_pos.mpr v1)).mpr
      rw [geom_sum_mul_neg]
      linarith only [pow_nonneg v0 (200+N-200)]
    simpa [tailQ,div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using
      mul_le_mul_of_nonneg_left q (show 0 ≤ (k:ℚ)^2/200*v^(200-k) by positivity)

theorem short_atom_budgets {k : ℕ} (hk : 3 ≤ k) (ku : k ≤ 7) (N : ℕ) :
    (∑ i∈Icc 1 N,costQ k i (4/5)) ≤ cSmall k ∧
    (∑ i∈Icc 1 N,costQ k i (93/100)) ≤ cLarge k := by
  obtain ⟨s,b⟩ := evaluated hk ku
  exact ⟨(sum_cost_bound ku N (by norm_num) (by norm_num)).trans s,
    (sum_cost_bound ku N (by norm_num) (by norm_num)).trans b⟩

#print axioms abs_signed_le
#print axioms short_atom_budgets
end LongCycleBounds.DescentMesh.SignedBounds
