import LongCycleBounds.OccupancyOrderings

/-! The positive-label coefficient of the original genuine row equals the
success probability in the uniform product of slot permutations and ball maps, times m^n. -/
noncomputable section
namespace LongCycleBounds.Occupancy
open Equiv Finset FixedCycleCount
open scoped Classical

private theorem tag_surj {m : ℕ} (σ : Perm (Fin m)) : Function.Surjective (tag σ) := by
  intro t
  cases t with
  | inl i => exact ⟨i.val,by simp [tag,i.property]⟩
  | inr s =>
    obtain ⟨i,hi⟩ := (Perm.mem_cycleFactorsFinset_iff.mp s.property).1.nonempty_support
    have move : σ i ≠ i := Perm.mem_support.mp ((Perm.support_cycleOf_le σ i)
      ((Perm.cycle_is_cycleOf hi s.property) ▸ hi))
    refine ⟨i,?_⟩
    simp only [tag,dif_neg move,Sum.inr.injEq,Subtype.ext_iff]
    exact (Perm.cycle_is_cycleOf hi s.property).symm

/-- Every actual orbit, including the orbit of any fixed slot, receives at least k balls. -/
def AllHit {m n : ℕ} (k : ℕ) (σ : Perm (Fin m)) (b : Fin n → Fin m) : Prop :=
  ∀ x : Fin m, k ≤ (univ.filter (fun y ↦ σ.SameCycle (b y) x)).card

theorem allHit_iff {m n k : ℕ} (σ : Perm (Fin m)) (b : Fin n → Fin m) :
    AllHit k σ b ↔ ∀ u : Tag σ, k ≤ counts (tag σ ∘ b) u := by
  have eq (i : Fin m) : (univ.filter (fun y ↦ σ.SameCycle (b y) i)).card =
      counts (tag σ ∘ b) (tag σ i) := by
    unfold counts
    congr 1
    ext j
    simpa only [mem_filter,mem_univ,true_and,Function.comp_apply] using (tag_eq_iff σ (b j) i).symm
  constructor
  · intro h u
    obtain ⟨i,rfl⟩ := tag_surj σ u
    rw [←eq]
    exact h i
  · intro h i
    rw [eq]
    exact h (tag σ i)

private def innerCount {m : ℕ} (σ : Perm (Fin m)) (n k h : ℕ) : ℚ :=
  ∑ l ∈ goodLengths h m, if σ.partition.parts=bag l then (accepted n k l:ℚ)/orderMultiplicity m l else 0

private theorem inner_eq {m h : ℕ} (σ : Perm (Fin m)) (n k : ℕ) (l : Fin h → ℕ)
    (good : l∈goodLengths h m) (same : σ.partition.parts=bag l) :
    innerCount σ n k h = goodMaps n k σ := by
  unfold innerCount
  rw [same,←sum_filter]
  have dom : (goodLengths h m).filter (fun v ↦ bag l=bag v)=orderings m l := by
    ext v; simp only [orderings,mem_filter,eq_comm (a:=bag l)]
  rw [dom]
  have terms (v : Fin h → ℕ) (hv : v∈orderings m l) :
      (accepted n k v:ℚ)/orderMultiplicity m v = (goodMaps n k σ:ℚ)/orderMultiplicity m l := by
    have bags := (mem_filter.mp hv).2
    have hist := bag_eq_counts_iff.mp bags
    rw [accepted_eq_allocations,allocations_eq_goodMaps σ v (same.trans bags.symm)]
    simp only [orderMultiplicity,hist]
  rw [sum_congr rfl terms,sum_const,nsmul_eq_mul,orderings_card l good]
  have ne : (orderMultiplicity m l:ℚ)≠0 := by exact_mod_cast (Nat.multinomial_pos _ _).ne'
  field_simp

private theorem inner_zero_of_goodMaps_zero {m : ℕ} (σ : Perm (Fin m)) (n k h : ℕ)
    (hz : goodMaps n k σ=0) : innerCount σ n k h = 0 := by
  apply sum_eq_zero
  intro l _
  split_ifs with h
  · rw [accepted_eq_allocations,allocations_eq_goodMaps σ l h,hz]
    simp
  · rfl

private theorem bag_transport {I : Type*} [Fintype I] {h : ℕ} (e : I ≃ Fin h) (f : I → ℕ) :
    bag (f ∘ e.symm) = bagF f := by
  ext a
  change (bagF _).count a=_
  rw [bagF_count,bagF_count]
  unfold counts
  apply card_bijective e.symm e.symm.bijective
  intro t
  simp

private theorem conditional_sum {m : ℕ} (hm : 0 < m) (n k : ℕ) (hk : 2 ≤ k) (σ : Perm (Fin m)) :
    ∑ r∈range (n/k), innerCount σ n k (r+1) = (goodMaps n k σ:ℚ) := by
  by_cases zero : goodMaps n k σ=0
  · simp [zero,inner_zero_of_goodMaps_zero σ n k _ zero]
  let H := Fintype.card (Tag σ)
  let e := Fintype.equivFin (Tag σ)
  let l : Fin H → ℕ := counts (tag σ) ∘ e.symm
  have same : σ.partition.parts=bag l :=
    (bagF_tag σ).symm.trans (bag_transport e (counts (tag σ))).symm
  have pos (i : Fin H) : 0 < l i := by
    obtain ⟨j,hj⟩ := tag_surj σ (e.symm i)
    change 0 < (univ.filter (fun x ↦ tag σ x=e.symm i)).card
    apply card_pos.mpr
    exact ⟨j,mem_filter.mpr ⟨mem_univ _,hj⟩⟩
  have total : ∑ i,l i=m := by
    change (bag l).sum=m
    rw [←same,σ.partition.parts_sum,Fintype.card_fin]
  have good : l∈goodLengths H m := mem_filter.mpr ⟨mem_piAntidiag.mpr ⟨total,fun _ _ ↦ mem_univ _⟩,pos⟩
  have hpos : 0 < H := Fintype.card_pos_iff.mpr ⟨tag σ ⟨0,hm⟩⟩
  obtain ⟨b,hb⟩ := card_pos.mp (Nat.pos_of_ne_zero zero)
  have hits : ∀ i : Tag σ, k ≤ counts (tag σ ∘ b) i := (mem_filter.mp hb).2
  have cap := sum_le_sum (s:=univ) (fun (i : Tag σ) _ ↦ hits i)
  rw [sum_counts,Fintype.card_fin,sum_const,card_univ,nsmul_eq_mul,Nat.cast_id] at cap
  have hle : H≤n/k := (Nat.le_div_iff_mul_le (by omega : 0 < k)).mpr cap
  have hr : H-1∈range (n/k) := mem_range.mpr (by omega)
  rw [sum_eq_single_of_mem (H-1) hr,show H-1+1=H by omega]
  · exact inner_eq σ n k l good same
  · intro r _ ne
    apply sum_eq_zero
    intro v _
    rw [if_neg]
    intro sv
    have bEq : bag v=bag l := sv.symm.trans same
    have c := congrArg Multiset.card bEq
    simp only [bag,Multiset.card_map,Finset.card_val,card_univ,Fintype.card_fin] at c
    omega

/-- Number of successful outcomes in the literal finite product sample space. -/
def jointSuccesses (n k m : ℕ) : ℕ :=
  (univ.filter (fun ω : Perm (Fin m) × (Fin n → Fin m) ↦ AllHit k ω.1 ω.2)).card

private theorem joint_sum (n k m : ℕ) : jointSuccesses n k m = ∑ σ : Perm (Fin m),goodMaps n k σ := by
  unfold jointSuccesses goodMaps
  simp only [card_eq_sum_ones,sum_filter,Fintype.sum_prod_type,allHit_iff]

/-- The survival probability of the uniform, independently chosen permutation and ball map. -/
def literalProbability (n k m : ℕ) : ℚ :=
  (jointSuccesses n k m:ℚ)/((m.factorial:ℚ)*(m:ℚ)^n)

theorem survival_eq_literal {m k : ℕ} (hk : 2 ≤ k) (hm : 0 < m) (n : ℕ) :
    survival n k m=literalProbability n k m := by
  unfold survival literalProbability
  rw [joint_sum,Nat.cast_sum]
  congr 1
  change (∑ r∈range (n/k), ∑ σ : Perm (Fin m), innerCount σ n k (r+1)) = _
  rw [sum_comm]
  apply sum_congr rfl
  exact fun σ _ ↦ conditional_sum hm n k hk σ

/-- Exact equality for the genuine excedance row at a positive label m. -/
theorem original_eq_slot_probability {m k : ℕ} (hk : 2 ≤ k) (hm : 0 < m) (n : ℕ) :
    originalLabelCoeff n k m = ((m:ℚ)^n * literalProbability n k m : ℚ) := by
  rw [←survival_eq_literal hk hm]
  exact actual_coefficient_eq_survival hk hm

#print axioms allHit_iff
#print axioms original_eq_slot_probability
end LongCycleBounds.Occupancy
