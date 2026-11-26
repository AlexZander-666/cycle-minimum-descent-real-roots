import LongCycleBounds.OccupancyCycleIndex

/-! Finite sampling of an actual slot permutation, an ordering of its complete
cycle-length profile, and genuine allocations of the labelled balls. -/
noncomputable section
namespace LongCycleBounds.Occupancy
open Equiv Finset FixedCycleCount
open scoped Classical

def orderMultiplicity {h : ℕ} (m : ℕ) (l : Fin h → ℕ) : ℕ :=
  Nat.multinomial (range (m+1)) (counts l)

private theorem order_spec {h m : ℕ} (l : Fin h → ℕ) (total : ∑ i,l i = m) :
    (∏ a ∈ range (m+1),(counts l a).factorial) * orderMultiplicity m l = h.factorial := by
  have maps (i : Fin h) (_ : i ∈ univ) : l i ∈ range (m+1) :=
    mem_range.mpr (Nat.lt_succ_of_le ((single_le_sum (s:=univ) (f:=l)
      (fun _ _ ↦ Nat.zero_le _) (mem_univ i)).trans_eq total))
  have eq := card_eq_sum_card_fiberwise maps
  rw [card_univ,Fintype.card_fin] at eq
  have e := Nat.multinomial_spec (range (m+1)) (counts l)
  rwa [show ∑ a ∈ range (m+1), counts l a=h from eq.symm] at e

/-- The law of one ordering of the complete cycle lengths of the uniform slot permutation. -/
theorem ordered_slot_law {h m : ℕ} (hm : 0 < m) (l : Fin h → ℕ) (pos : ∀ i,0 < l i)
    (total : ∑ i,l i=m) :
    ((matchingPerms m l).card:ℚ) / (m.factorial * (orderMultiplicity m l:ℚ)) =
      1 / (h.factorial * (∏ i,l i:ℕ) : ℚ) := by
  let D := ∏ a ∈ range (m+1),(counts l a).factorial
  let Q := orderMultiplicity m l
  let L := ∏ i,l i
  let G := (matchingPerms m l).card
  have eh : (D:ℚ)*Q = h.factorial := by exact_mod_cast order_spec l total
  have em : (G:ℚ)*((L:ℚ)*D) = m.factorial := by exact_mod_cast matchingPerms_card hm l pos total
  have hL : 0 < L := prod_pos (fun i _ ↦ pos i)
  have hQ : 0 < Q := Nat.multinomial_pos _ _
  change (G:ℚ)/(m.factorial * (Q:ℚ)) = 1 / (h.factorial * (L:ℚ))
  apply (div_eq_div_iff (by positivity) (by positivity)).mpr
  rw [←eh,←em]
  ring

abbrev Slots {h : ℕ} (l : Fin h → ℕ) := Σ i, Fin (l i)

private theorem slot_counts {h : ℕ} (l : Fin h → ℕ) :
    counts (fun z : Slots l ↦ z.1) = l := by
  funext i
  let e : {z : Slots l // z.1=i} ≃ Fin (l i) :=
    { toFun := fun z ↦ Fin.cast (congrArg l z.property) z.val.2
      invFun := fun t ↦ ⟨⟨i,t⟩,rfl⟩
      left_inv := by rintro ⟨⟨z,a⟩,rfl⟩; rfl
      right_inv := fun _ ↦ rfl }
  have q := Fintype.card_congr e
  simpa [Fintype.subtype_card,counts] using q

/-- Literal ball-to-slot functions, with the cycle occupancy restriction in the predicate. -/
def accepted {h : ℕ} (n k : ℕ) (l : Fin h → ℕ) : ℕ :=
  (univ.filter (fun f : Fin n → Slots l ↦ ∀ i, k ≤ counts (fun b ↦ (f b).1) i)).card

theorem accepted_eq_allocations {h : ℕ} (n k : ℕ) (l : Fin h → ℕ) :
    accepted n k l=allocations n k l := by
  have e := allocations_eq_card (n:=n) (k:=k) (fun z : Slots l ↦ z.1)
  rw [slot_counts] at e
  exact e.symm

def goodLengths (h m : ℕ) : Finset (Fin h → ℕ) :=
  (piAntidiag univ m).filter (fun l ↦ ∀ i, 0 < l i)

/-- Expected accepted placements for one observed cycle count, multiplied by m!. -/
def stratumCount (h n k m : ℕ) : ℚ :=
  ∑ σ : Perm (Fin m), ∑ l ∈ goodLengths h m,
    if σ.partition.parts=bag l then (accepted n k l:ℚ) / orderMultiplicity m l else 0

theorem stratum_eq {m : ℕ} (hm : 0 < m) (h n k : ℕ) :
    stratumCount h n k m = (m.factorial:ℚ) * (slotSum h n k m / h.factorial) := by
  rw [stratumCount,sum_comm,slotSum,sum_div,mul_sum]
  apply sum_congr rfl
  intro l hl
  have pos := (mem_filter.mp hl).2
  have total := (mem_piAntidiag.mp (mem_filter.mp hl).1).1
  have e := ordered_slot_law hm l pos total
  rw [←sum_filter,sum_const,nsmul_eq_mul,accepted_eq_allocations]
  change ((matchingPerms m l).card:ℚ)*((allocations n k l:ℚ)/orderMultiplicity m l) = _
  have q : (orderMultiplicity m l:ℚ)≠0 := by exact_mod_cast (Nat.multinomial_pos _ _).ne'
  have L : (∏ i,(l i:ℚ))≠0 := (prod_pos (fun i _ ↦ (show 0 < (l i:ℚ) by exact_mod_cast pos i))).ne'
  push_cast at e
  field_simp at e ⊢
  linear_combination (allocations n k l:ℚ) * e

/-- Exact rational probability obtained from the finite slot permutation and ball-placement model.
More than n/k cycles give zero legal placements when k is positive. -/
def survival (n k m : ℕ) : ℚ :=
  (∑ h ∈ range (n/k), stratumCount (h+1) n k m) / ((m.factorial:ℚ)*(m:ℚ)^n)

theorem survival_eq_cycleIndex {m : ℕ} (hm : 0 < m) (n k : ℕ) :
    survival n k m=cycleIndexSurvival n k m := by
  simp only [survival,cycleIndexSurvival,stratum_eq hm,←mul_sum]
  field_simp

theorem actual_coefficient_eq_survival {n k m : ℕ} (hk : 2 ≤ k) (hm : 0 < m) :
    originalLabelCoeff n k m = ((m:ℚ)^n * survival n k m : ℚ) := by
  rw [survival_eq_cycleIndex hm]
  exact originalLabelCoeff_eq_cycleIndex hk hm

#print axioms ordered_slot_law
#print axioms accepted_eq_allocations
#print axioms actual_coefficient_eq_survival
end LongCycleBounds.Occupancy
