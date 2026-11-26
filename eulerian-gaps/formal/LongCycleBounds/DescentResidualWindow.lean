import LongCycleBounds.CycleProbability

namespace LongCycleBounds.DescentMesh.ResidualWindow
open Finset FixedCycleCount

private theorem prefix_sum {k n : ℕ} (hk : 2 ≤ k) (hn : 0<n) :
    (n:ℝ)*allowedFraction n k = ∑ b∈range (n+1-k),allowedFraction b k := by
  rw [allowedFraction_recurrence hk hn]
  refine sum_nbij' (fun a ↦ n-a) (fun b ↦ n-b) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    have h := mem_Icc.mp ha
    exact mem_range.mpr (by omega)
  · intro b hb
    have h := mem_range.mp hb
    exact mem_Icc.mpr ⟨by omega,by omega⟩
  · intro a ha; have h := mem_Icc.mp ha; omega
  · intro b hb; have h := mem_range.mp hb; omega
  · intro a _; rfl

theorem convex_step {k n : ℕ} (hk : 2 ≤ k) (kn : k ≤ n+1) :
    ((n:ℝ)+1)*allowedFraction (n+1) k =
      (n:ℝ)*allowedFraction n k + allowedFraction (n+1-k) k := by
  have h := prefix_sum (k:=k) (n:=n+1) hk (by omega)
  rw [show n+1+1-k = (n+1-k)+1 by omega,sum_range_succ,← prefix_sum hk (by omega)] at h
  simpa only [Nat.cast_succ] using h

theorem propagate {k b : ℕ} (hk : 2 ≤ k) (L U : ℝ)
    (start : ∀ i∈Ico b (b+k), L ≤ allowedFraction i k ∧ allowedFraction i k ≤ U) :
    ∀ m, b ≤ m → L ≤ allowedFraction m k ∧ allowedFraction m k ≤ U := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro bm
    by_cases small : m<b+k
    · exact start m (mem_Ico.mpr ⟨bm,small⟩)
    obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m≠0)
    have h₁ := ih n (by omega) (by omega)
    have h₂ := ih (n+1-k) (by omega) (by omega)
    have eq := convex_step (n:=n) hk (by omega)
    have pos : 0<(n:ℝ)+1 := by positivity
    constructor
    · apply le_of_mul_le_mul_left (a:=(n:ℝ)+1) _ pos
      linarith only [eq,h₂.1,mul_le_mul_of_nonneg_left h₁.1 (Nat.cast_nonneg (α:=ℝ) n)]
    · apply le_of_mul_le_mul_left (a:=(n:ℝ)+1) _ pos
      linarith only [eq,h₂.2,mul_le_mul_of_nonneg_left h₁.2 (Nat.cast_nonneg (α:=ℝ) n)]

/-- k is encoded as t+2 so both recursive indices are strictly smaller. -/
def pQ (t : ℕ) : ℕ → ℚ
  | 0 => 1
  | n+1 => if t+2 ≤ n+1 then ((n:ℚ)*pQ t n + pQ t (n+1-(t+2)))/(n+1) else 0
termination_by n => n
decreasing_by all_goals omega

theorem pQ_cast (t n : ℕ) : (pQ t n : ℝ) = allowedFraction n (t+2) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [pQ,allowedFraction_zero]
    | succ n =>
      rw [pQ]
      split_ifs with hk
      · push_cast
        rw [ih n (by omega),ih (n-(t+1)) (by omega),show n-(t+1)=n+1-(t+2) by omega]
        apply (div_eq_iff (by positivity : (n:ℝ)+1≠0)).mpr
        rw [mul_comm (allowedFraction ..)]
        exact (convex_step (by omega : 2 ≤ t+2) hk).symm
      · have h := prefix_sum (n:=n+1) (k:=t+2) (by omega) (by omega)
        have len : n+1+1-(t+2)=0 := by omega
        rw [len,sum_range_zero] at h
        simpa using ((mul_eq_zero.mp h).resolve_left (by positivity)).symm

def bounds : ℕ → ℕ × ℕ
  | 3 => (22313,22314)
  | 4 => (15987,15988)
  | 5 => (12451,12453)
  | 6 => (10184,10196)
  | _ => (8619,8651)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
private theorem verified_window {k : ℕ} (hk : 3 ≤ k) (ku : k ≤ 7) :
    ∀ i:Fin 27,20 ≤ i.val → i.val<20+k →
    ((bounds k).1:ℚ)/100000 ≤ pQ (k-2) i.val ∧ pQ (k-2) i.val ≤ ((bounds k).2:ℚ)/100000 := by
  interval_cases k <;> decide +kernel

/-- Any two positive residual sizes at least 20 have comparable genuine permutation
fractions throughout the five short cutoffs. -/
theorem residual_ratio {k n m : ℕ} (hk : 3 ≤ k) (ku : k ≤ 7) (hn : 20 ≤ n) (hm : 20 ≤ m) :
    allowedFraction m k ≤ (201/200:ℝ)*allowedFraction n k := by
  have H := propagate (k:=k) (b:=20) (by omega) (((bounds k).1:ℝ)/100000)
    (((bounds k).2:ℝ)/100000) (by
      intro i hi
      obtain ⟨lo,up⟩ := mem_Ico.mp hi
      have e := verified_window hk ku ⟨i,by omega⟩ lo up
      have cast : (pQ (k-2) i:ℝ)=allowedFraction i k := by
        simpa only [show k-2+2=k by omega] using pQ_cast (k-2) i
      rw [←cast]
      constructor
      · simpa using (Rat.cast_le (K:=ℝ)).mpr e.1
      · simpa using (Rat.cast_le (K:=ℝ)).mpr e.2)
  have cmp : ((bounds k).2:ℝ)/100000 ≤ (201/200:ℝ)*(((bounds k).1:ℝ)/100000) := by
    interval_cases k <;> norm_num [bounds]
  exact (H m hm).2.trans (cmp.trans (mul_le_mul_of_nonneg_left (H n hn).1 (by norm_num)))

#print axioms convex_step
#print axioms residual_ratio
end LongCycleBounds.DescentMesh.ResidualWindow
