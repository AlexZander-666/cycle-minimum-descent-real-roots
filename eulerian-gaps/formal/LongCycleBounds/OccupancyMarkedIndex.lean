import LongCycleBounds.OccupancyAnchoredSeries

/-! The complete slot-permutation cycle index for arbitrary tests of its length multiset. -/
noncomputable section
namespace LongCycleBounds.Occupancy
open Finset Equiv
open scoped Classical

private theorem profile_ordering {m : ℕ} (σ : Perm (Fin m)) :
    ∃ h ≤ m, ∃ l ∈ goodLengths h m, σ.partition.parts = bag l := by
  let H := Fintype.card (Tag σ)
  let e := Fintype.equivFin (Tag σ)
  let l : Fin H → ℕ := counts (tag σ) ∘ e.symm
  have transported : bag l=bagF (counts (tag σ)) := by
    ext a
    change (bagF _).count a=_
    rw [bagF_count,bagF_count]
    unfold counts
    apply card_bijective e.symm e.symm.bijective
    intro t
    simp only [mem_filter,mem_univ,true_and,l,Function.comp_apply]
    rfl
  have same := (bagF_tag σ).symm.trans transported.symm
  have total : ∑ i,l i=m := by
    change (bag l).sum=m
    rw [←same,σ.partition.parts_sum,Fintype.card_fin]
  have pos (i : Fin H) : 0<l i := by
    apply σ.partition.parts_pos
    rw [same]
    exact Multiset.mem_map.mpr ⟨i,Finset.mem_val.mpr (mem_univ _),rfl⟩
  have count := sum_le_sum (s:=univ) (f:=fun _ : Fin H ↦ 1) fun i _ ↦ pos i
  simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one,total] at count
  exact ⟨H,count,l,mem_filter.mpr ⟨mem_piAntidiag.mpr ⟨total,fun _ _ ↦ mem_univ _⟩,pos⟩,same⟩

/-- Every ordering of one slot permutation carries reciprocal order multiplicity, summing to one. -/
theorem complete_ordering_mass {m : ℕ} (σ : Perm (Fin m)) :
    (∑ h ∈ range (m+1), ∑ l ∈ goodLengths h m,
      if σ.partition.parts=bag l then (1:ℝ)/orderMultiplicity m l else 0) = 1 := by
  obtain ⟨h,hm,l,hl,same⟩ := profile_ordering σ
  rw [sum_eq_single_of_mem h (mem_range.mpr (by omega))]
  · rw [same,←sum_filter]
    have eq : (goodLengths h m).filter (fun z ↦ bag l=bag z)=orderings m l := by
      ext z
      simp only [orderings,mem_filter,eq_comm (a:=bag l)]
    rw [eq]
    have wt (z : Fin h → ℕ) (hz : z∈orderings m l) :
        (1:ℝ)/orderMultiplicity m z=1/orderMultiplicity m l := by
      rw [orderMultiplicity,orderMultiplicity,bag_eq_counts_iff.mp (mem_filter.mp hz).2]
    rw [sum_congr rfl wt,sum_const,nsmul_eq_mul,orderings_card l hl]
    have p : (orderMultiplicity m l:ℝ) ≠ 0 := by exact_mod_cast (Nat.multinomial_pos _ _).ne'
    field_simp
  · intro h' _ ne
    apply sum_eq_zero
    intro z _
    rw [if_neg]
    intro eq
    have sizes := congrArg Multiset.card (same.symm.trans eq)
    simp only [bag,Multiset.card_map,Finset.card_val,card_univ,Fintype.card_fin] at sizes
    omega

/-- Test-function form of the exact slot cycle index, including all singleton cycles. -/
theorem complete_slot_cycle_index {m : ℕ} (hm : 0 < m) (V : Multiset ℕ → ℝ) :
    (∑ σ : Perm (Fin m), V σ.partition.parts)/(m.factorial:ℝ) =
      ∑ h ∈ range (m+1), ∑ l ∈ goodLengths h m,
        V (bag l)/((h.factorial:ℝ)*∏ i, (l i:ℝ)) := by
  have per (σ : Perm (Fin m)) : V σ.partition.parts/(m.factorial:ℝ) =
      ∑ h ∈ range (m+1), ∑ l ∈ goodLengths h m,
        if σ.partition.parts=bag l then
          V (bag l)/((m.factorial:ℝ)*orderMultiplicity m l) else 0 := by
    calc
      _ = (V σ.partition.parts/(m.factorial:ℝ))*
          (∑ h ∈ range (m+1), ∑ l ∈ goodLengths h m,
            if σ.partition.parts=bag l then (1:ℝ)/orderMultiplicity m l else 0) := by
              rw [complete_ordering_mass,mul_one]
      _ = _ := by
        simp only [mul_sum]
        apply sum_congr rfl; intro h _
        apply sum_congr rfl; intro l _
        split_ifs with same
        · rw [same,div_mul_eq_div_div];ring
        · ring
  rw [sum_div]
  simp_rw [per]
  rw [sum_comm]
  apply sum_congr rfl
  intro h _
  rw [sum_comm]
  apply sum_congr rfl
  intro l hl
  rw [←sum_filter,sum_const,nsmul_eq_mul]
  have eq := ordered_slot_law hm l (mem_filter.mp hl).2 (mem_piAntidiag.mp (mem_filter.mp hl).1).1
  have casted := congrArg (fun q : ℚ ↦ (q:ℝ)) eq
  push_cast at casted
  change ((matchingPerms m l).card:ℝ)*(V (bag l)/((m.factorial:ℝ)*orderMultiplicity m l))=_
  linear_combination V (bag l)*casted

#print axioms complete_slot_cycle_index
end LongCycleBounds.Occupancy
