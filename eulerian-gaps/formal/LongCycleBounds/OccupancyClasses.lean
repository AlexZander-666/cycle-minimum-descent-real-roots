import LongCycleBounds.OccupancySurvival

/-! The actual slot cycles of a given permutation and the transport of ball placements. -/
noncomputable section
namespace LongCycleBounds.Occupancy
open Finset Equiv
open scoped Classical

abbrev Tag {m : ℕ} (σ : Perm (Fin m)) :=
  {i : Fin m // σ i=i} ⊕ (σ.cycleFactorsFinset : Type)

def tag {m : ℕ} (σ : Perm (Fin m)) (i : Fin m) : Tag σ :=
  if hi : σ i=i then Sum.inl ⟨i,hi⟩
  else Sum.inr ⟨σ.cycleOf i, Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr (Perm.mem_support.mpr hi)⟩

private theorem tag_fixed {m : ℕ} (σ : Perm (Fin m)) (b : {i : Fin m // σ i=i}) (i : Fin m) :
    tag σ i = Sum.inl b ↔ i=b.val := by
  by_cases hi : σ i=i
  · simp [tag,hi,Subtype.ext_iff]
  · simp [tag,hi]
    exact fun eq ↦ hi (eq ▸ b.property)

private theorem tag_cycle {m : ℕ} (σ : Perm (Fin m)) (b : σ.cycleFactorsFinset) (i : Fin m) :
    tag σ i = Sum.inr b ↔ i∈b.val.support := by
  by_cases hi : σ i=i
  · simp only [tag,dif_pos hi,Sum.inl_ne_inr,false_iff]
    intro hin
    have eq := Perm.cycle_is_cycleOf hin b.property
    rw [(Perm.cycleOf_eq_one_iff σ).mpr hi] at eq
    exact (Perm.mem_cycleFactorsFinset_iff.mp b.property).1.ne_one eq
  · simp only [tag,dif_neg hi,Sum.inr.injEq,Subtype.ext_iff]
    exact eq_comm.trans (σ.eq_cycleOf_of_mem_cycleFactorsFinset_iff _ b.property i)

theorem counts_tag_fixed {m : ℕ} (σ : Perm (Fin m)) (b : {i : Fin m // σ i=i}) :
    counts (tag σ) (Sum.inl b) = 1 := by
  have setEq : univ.filter (fun i ↦ tag σ i=Sum.inl b)={b.val} := by
    ext i
    simpa only [mem_filter,mem_univ,true_and,mem_singleton] using tag_fixed σ b i
  exact (congrArg Finset.card setEq).trans (card_singleton _)

theorem counts_tag_cycle {m : ℕ} (σ : Perm (Fin m)) (b : σ.cycleFactorsFinset) :
    counts (tag σ) (Sum.inr b) = b.val.support.card := by
  apply congrArg Finset.card
  ext i
  simpa only [mem_filter,mem_univ,true_and] using tag_cycle σ b i

theorem tag_eq_iff {m : ℕ} (σ : Perm (Fin m)) (i j : Fin m) :
    tag σ i = tag σ j ↔ σ.SameCycle i j := by
  by_cases hi : σ i=i
  · rw [show tag σ i = Sum.inl ⟨i,hi⟩ from (tag_fixed σ _ _).mpr rfl,eq_comm,tag_fixed]
    constructor
    · rintro rfl; exact Perm.SameCycle.refl _ _
    · rintro ⟨p,hp⟩
      simpa [Perm.zpow_apply_eq_self_of_apply_eq_self hi] using hp.symm
  · by_cases hj : σ j=j
    · rw [show tag σ j = Sum.inl ⟨j,hj⟩ from (tag_fixed σ _ _).mpr rfl,tag_fixed]
      constructor
      · rintro rfl; exact Perm.SameCycle.refl _ _
      · intro same
        exact (hi (same.apply_eq_self_iff.mpr hj)).elim
    · simp only [tag,dif_neg hi,dif_neg hj,Sum.inr.injEq,Subtype.ext_iff]
      exact (Perm.sameCycle_iff_cycleOf_eq_of_mem_support
        (Perm.mem_support.mpr hi) (Perm.mem_support.mpr hj)).symm

def bagF {I : Type*} [Fintype I] (f : I → ℕ) : Multiset ℕ := univ.val.map f

theorem bagF_count {I : Type*} [Fintype I] (f : I → ℕ) (a : ℕ) :
    (bagF f).count a=counts f a := by
  unfold bagF counts
  rw [Multiset.count_map,←Finset.filter_val]
  simp only [eq_comm (a:=a)]
  rfl

private theorem count_card {I A : Type*} [Fintype I] [DecidableEq A] (f : I → A) (a : A) :
    Fintype.card {i // f i=a} = counts f a := by simp [counts,Fintype.subtype_card]

theorem bagF_tag {m : ℕ} (σ : Perm (Fin m)) :
    bagF (counts (tag σ))=σ.partition.parts := by
  ext a
  rw [bagF_count,Perm.parts_partition,Multiset.count_add,Perm.CycleType.count_def]
  rw [←count_card]
  let U := {i : Fin m // σ i=i}
  let V := (σ.cycleFactorsFinset : Type)
  have part : Fintype.card {t : Tag σ // counts (tag σ) t=a} =
      Fintype.card {i : U // 1=a} + Fintype.card {v : V // v.val.support.card=a} := by
    let e : {t : Tag σ // counts (tag σ) t=a} ≃ {i : U // 1=a} ⊕ {v : V // v.val.support.card=a} :=
      { toFun := fun t ↦ match t with
          | ⟨Sum.inl i,hi⟩ => Sum.inl ⟨i,(counts_tag_fixed σ i).symm.trans hi⟩
          | ⟨Sum.inr v,hv⟩ => Sum.inr ⟨v,(counts_tag_cycle σ v).symm.trans hv⟩
        invFun := fun t ↦ match t with
          | Sum.inl ⟨i,hi⟩ => ⟨Sum.inl i,(counts_tag_fixed σ i).trans hi⟩
          | Sum.inr ⟨v,hv⟩ => ⟨Sum.inr v,(counts_tag_cycle σ v).trans hv⟩
        left_inv := by rintro ⟨i,hi⟩; cases i <;> rfl
        right_inv := by intro i; cases i <;> rfl }
    rw [Fintype.card_congr e,Fintype.card_sum]
  rw [part,add_comm]
  congr 1
  by_cases h : a=1
  · subst a
    simp only [Multiset.count_replicate_self]
    rw [Fintype.card_subtype_true]
    change Fintype.card (Function.fixedPoints σ)=_
    rw [Perm.card_fixedPoints,Perm.sum_cycleType]
  · have ne : a∉Multiset.replicate (Fintype.card (Fin m)-σ.support.card) 1 :=
      fun ha ↦ h (Multiset.eq_of_mem_replicate ha)
    rw [Multiset.count_eq_zero.mpr ne,Fintype.card_eq_zero_iff]
    exact ⟨fun z ↦ h z.property.symm⟩

private def relabel {I A : Type*} [Fintype I] [Fintype A] (f : I → ℕ) (g : A → ℕ)
    (eq : bagF f=bagF g) : I ≃ A :=
  Equiv.ofFiberEquiv (f:=f) (g:=g) fun a ↦ Fintype.equivOfCardEq (by
    rw [count_card,count_card,←bagF_count,←bagF_count,eq])

private theorem relabel_apply {I A : Type*} [Fintype I] [Fintype A] (f : I → ℕ) (g : A → ℕ)
    (eq : bagF f=bagF g) (i : I) : g (relabel f g eq i)=f i :=
  Equiv.ofFiberEquiv_map (f:=f) (g:=g) _ i

private theorem counts_comp {I A B : Type*} [Fintype I] [DecidableEq A] [DecidableEq B]
    (e : A ≃ B) (f : I → A) (a : A) : counts (e ∘ f) (e a) = counts f a := by
  simp [counts]

/-- Legal maps defined solely by the cycles of the actual slot permutation. -/
def goodMaps {m : ℕ} (n k : ℕ) (σ : Perm (Fin m)) : ℕ :=
  (univ.filter (fun f : Fin n → Fin m ↦ ∀ u : Tag σ, k ≤ counts (tag σ ∘ f) u)).card

theorem allocations_eq_goodMaps {h m n k : ℕ} (σ : Perm (Fin m)) (l : Fin h → ℕ)
    (same : σ.partition.parts = bag l) : allocations n k l=goodMaps n k σ := by
  have eq : bagF (counts (tag σ))=bagF l := (bagF_tag σ).trans same
  let e := relabel (counts (tag σ)) l eq
  have lens : counts (e ∘ tag σ)=l := by
    funext i
    obtain ⟨t,rfl⟩ := e.surjective i
    exact (counts_comp e (tag σ) t).trans (relabel_apply _ _ eq t).symm
  rw [←lens,allocations_eq_card]
  unfold goodMaps
  congr 1
  ext f
  simp only [mem_filter,mem_univ,true_and]
  constructor
  · intro good t
    have h := good (e t)
    change k ≤ counts (e ∘ (tag σ ∘ f)) (e t) at h
    rwa [counts_comp] at h
  · intro good i
    obtain ⟨t,rfl⟩ := e.surjective i
    change k ≤ counts (e ∘ (tag σ ∘ f)) (e t)
    rw [counts_comp]
    exact good t

#print axioms tag_eq_iff
#print axioms allocations_eq_goodMaps
end LongCycleBounds.Occupancy
