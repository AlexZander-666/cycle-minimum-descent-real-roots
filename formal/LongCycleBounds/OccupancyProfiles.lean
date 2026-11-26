import LongCycleBounds.GeneralCyclePositiveSeries

/-! Slot lengths and allocations of distinguishable balls in the original positive-label series. -/
noncomputable section
namespace LongCycleBounds.Occupancy
open Finset FixedCycleCount
open scoped Classical

/-- Conditional number of legal allocations for an ordered slot-cycle profile.
There are n labelled balls, and cycle i has l i labelled slots. -/
def allocations {h : ℕ} (n k : ℕ) (l : Fin h → ℕ) : ℕ :=
  ∑ a ∈ (piAntidiag (univ : Finset (Fin h)) n).filter (fun a ↦ ∀ i, k ≤ a i),
    Nat.multinomial univ a * ∏ i, (l i)^(a i)

/-- Sum over ordered positive slot lengths of total m with the cycle-index divisor.
The 1/h! for ordering the cycles is taken separately. -/
def slotSum (h n k m : ℕ) : ℚ :=
  ∑ l ∈ (piAntidiag (univ : Finset (Fin h)) m).filter (fun l ↦ ∀ i, 0 < l i),
    (allocations n k l : ℚ) / ∏ i, (l i : ℚ)

private theorem shift {R : Type*} [AddCommMonoid R] (h d k : ℕ) (hk : 1 ≤ k)
    (F : (Fin h → ℕ) → R) :
    (∑ a ∈ (piAntidiag (univ : Finset (Fin h)) (d+h)).filter (fun a ↦ ∀ i, k ≤ a i), F a) =
      ∑ f ∈ (piAntidiag (univ : Finset (Fin h)) d).filter (fun f ↦ ∀ i, k ≤ f i+1),
        F (fun i ↦ f i+1) := by
  symm
  apply sum_nbij' (fun f i ↦ f i+1) (fun a i ↦ a i-1)
  case hi =>
    intro f hf
    simp only [mem_filter,mem_piAntidiag,mem_univ,implies_true,and_true] at hf ⊢
    refine ⟨?_,hf.2⟩
    simpa [sum_add_distrib] using hf.1
  case hj =>
    intro a ha
    simp only [mem_filter,mem_piAntidiag,mem_univ,implies_true,and_true] at ha ⊢
    have sub (i : Fin h) : a i-1+1 = a i := Nat.sub_add_cancel (hk.trans (ha.2 i))
    have eq : (∑ i, ((a i-1)+1))=d+h :=
      (sum_congr rfl fun i _ ↦ sub i).trans ha.1
    simp only [sum_add_distrib,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one,Nat.cast_id] at eq
    exact ⟨by omega,fun i ↦ (sub i).symm ▸ ha.2 i⟩
  case left_neg => intro f _; funext i; simp
  case right_neg => intro a ha; funext i; exact Nat.sub_add_cancel (hk.trans ((mem_filter.mp ha).2 i))
  case h => intros; rfl

private theorem label_sum {R : Type*} [AddCommMonoid R] (h d : ℕ)
    (F : (Fin (h+1) → ℕ) → R) :
    (∑ g ∈ labelPieces h d, F g) = ∑ g ∈ piAntidiag (univ : Finset (Fin (h+1))) d, F g := by
  let e : (Fin (h+1) →₀ ℕ) ≃ (Fin (h+1) → ℕ) := Finsupp.equivFunOnFinite
  apply sum_nbij' e e.symm
  · intro g hg
    exact mem_piAntidiag.mpr ⟨(mem_finsuppAntidiag.mp hg).1,fun _ _ ↦ mem_univ _⟩
  · intro f hf
    refine mem_finsuppAntidiag.mpr ⟨?_,subset_univ _⟩
    have eq : (⇑(e.symm f)) = f := e.apply_symm_apply f
    rw [eq]
    exact (mem_piAntidiag.mp hf).1
  · exact fun f _ ↦ e.symm_apply_apply f
  · exact fun f _ ↦ e.apply_symm_apply f
  · intros; rfl

private theorem slot_shift (h d : ℕ) (F : (Fin h → ℕ) → ℚ) :
    (∑ l ∈ (piAntidiag (univ : Finset (Fin h)) (d+h)).filter (fun l ↦ ∀ i, 0 < l i), F l)
      = ∑ g ∈ piAntidiag (univ : Finset (Fin h)) d, F (fun i ↦ g i+1) := by
  have e := shift h d 1 le_rfl F
  simpa only [Nat.succ_le_iff, Nat.zero_lt_succ, implies_true, filter_true_of_mem] using e

private theorem cancel_lengths {h : ℕ} (g f : Fin h → ℕ) :
    (∏ i, ((g i+1:ℕ):ℚ)^(f i+1)) / (∏ i, ((g i+1:ℕ):ℚ)) =
      ∏ i, ((g i+1:ℕ):ℚ)^(f i) := by
  have pos : (∏ i, ((g i+1:ℕ):ℚ)) ≠ 0 := by positivity
  apply (div_eq_iff pos).mpr
  simp only [pow_succ,prod_mul_distrib]

theorem slotSum_eq_ordered (h n k m : ℕ) (hk : 1 ≤ k) (hn : h+1 ≤ n) :
    slotSum (h+1) n k m = (orderedLabelCoeff n k h m : ℚ) := by
  by_cases hm : h+1 ≤ m
  · obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le hm
    obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [slotSum,add_comm (h+1) d,slot_shift,orderedLabelCoeff,if_pos (by omega)]
    simp only [Nat.add_sub_cancel,Nat.add_sub_cancel_left]
    unfold orderedLabelSum
    push_cast
    rw [label_sum h d (fun g ↦ ∑ f ∈ (piAntidiag (univ : Finset (Fin (h+1))) j).filter (fun f ↦ ∀ i, k ≤ f i+1),
      (Nat.multinomial univ (fun i ↦ f i+1):ℚ) * ∏ i, ((g i:ℚ)+1)^(f i))]
    apply sum_congr rfl
    intro g _
    unfold allocations
    rw [add_comm (h+1) j,shift _ _ _ hk]
    push_cast
    rw [sum_div]
    apply sum_congr rfl
    intro f _
    rw [mul_div_assoc]
    congr 1
    simpa only [Nat.cast_add,Nat.cast_one] using cancel_lengths g f
  · rw [orderedLabelCoeff_below (by omega : m<h+1),Nat.cast_zero,slotSum]
    apply sum_eq_zero
    intro l hl
    obtain ⟨hm',hp⟩ := mem_filter.mp hl
    have eq := (mem_piAntidiag.mp hm').1
    have low := sum_le_sum (s:=(univ : Finset (Fin (h+1)))) (f:=fun _ ↦ 1) (g:=l) (fun i _ ↦ hp i)
    simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one,Nat.cast_id] at low
    change (∑ i, l i)=m at eq
    omega

/-- The cycle-index form of the survival probability is rational at every positive label. -/
def cycleIndexSurvival (n k m : ℕ) : ℚ :=
  (∑ h ∈ range (n/k), slotSum (h+1) n k m / (h+1).factorial) / (m:ℚ)^n

theorem originalLabelCoeff_eq_cycleIndex {n k m : ℕ} (hk : 2 ≤ k) (hm : 0 < m) :
    originalLabelCoeff n k m = ((m:ℚ)^n * cycleIndexSurvival n k m : ℚ) := by
  have ne : (m:ℚ)^n ≠ 0 := by positivity
  rw [cycleIndexSurvival,mul_div_cancel₀ _ ne]
  unfold originalLabelCoeff
  push_cast
  apply sum_congr rfl
  intro h hh
  have le := (Nat.lt_iff_add_one_le.mp (mem_range.mp hh)).trans (Nat.div_le_self n k)
  rw [slotSum_eq_ordered h n k m (by omega) le]
  push_cast
  ring

#print axioms slotSum_eq_ordered
#print axioms originalLabelCoeff_eq_cycleIndex
end LongCycleBounds.Occupancy
