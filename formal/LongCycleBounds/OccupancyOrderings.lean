import LongCycleBounds.OccupancyClasses

/-! Completely labelled and ordered length profiles have the usual multinomial multiplicity. -/
noncomputable section
namespace LongCycleBounds.Occupancy
open Finset Equiv

theorem bag_eq_counts_iff {h : ℕ} {l v : Fin h → ℕ} :
    bag l=bag v ↔ counts l=counts v := by
  change bagF l=bagF v ↔ _
  constructor
  · intro h
    funext a
    rw [←bagF_count,←bagF_count,h]
  · intro h
    ext a
    rw [bagF_count,bagF_count,h]

def orderings {h : ℕ} (m : ℕ) (l : Fin h → ℕ) :=
  (goodLengths h m).filter (fun v ↦ bag v=bag l)

private theorem bound {h m : ℕ} {v : Fin h → ℕ} (hv : v ∈ goodLengths h m) (i : Fin h) :
    v i < m+1 :=
  Nat.lt_succ_of_le ((single_le_sum (f:=v) (fun _ _ ↦ Nat.zero_le _) (mem_univ i)).trans_eq
    (mem_piAntidiag.mp (mem_filter.mp hv).1).1)

private theorem counts_val {h m : ℕ} (w : Fin h → Fin (m+1)) (a : Fin (m+1)) :
    counts (fun i ↦ (w i).val) a.val=counts w a := by
  unfold counts
  congr 1
  ext i
  simp only [mem_filter,mem_univ,true_and]
  exact Fin.val_inj

theorem orderings_card {h m : ℕ} (l : Fin h → ℕ) (good : l ∈ goodLengths h m) :
    (orderings m l).card=orderMultiplicity m l := by
  classical
  let a : Fin (m+1) → ℕ := fun i ↦ counts l i.val
  let S := univ.filter (fun w : Fin h → Fin (m+1) ↦ counts w=a)
  let pack (v : Fin h → ℕ) (hv : v ∈ orderings m l) (i : Fin h) : Fin (m+1) :=
    ⟨v i,bound (mem_filter.mp hv).1 i⟩
  have bij : (orderings m l).card=S.card := by
    apply card_bij (fun v hv ↦ pack v hv)
    · intro v hv
      refine mem_filter.mpr ⟨mem_univ _,?_⟩
      funext i
      have hist := bag_eq_counts_iff.mp (mem_filter.mp hv).2
      exact (counts_val (pack v hv) i).symm.trans (congrFun hist i.val)
    · intro v hv w hw eq
      funext i
      exact congrArg Fin.val (congrFun eq i)
    · intro w hw
      let v := fun i ↦ (w i).val
      have hist : counts v=counts l := by
        funext z
        by_cases small : z < m+1
        · let i : Fin (m+1) := ⟨z,small⟩
          exact (counts_val w i).trans (congrFun (mem_filter.mp hw).2 i)
        · have aux (g : Fin h → ℕ) (cap : ∀ i, g i < m+1) : counts g z=0 := by
            unfold counts
            rw [card_eq_zero,filter_eq_empty_iff]
            intro i _ eq
            exact small (eq ▸ cap i)
          rw [aux v (fun i ↦ (w i).isLt), aux l (bound good)]
      have bags := bag_eq_counts_iff.mpr hist
      have sumV : (∑ i,v i)=m := (congrArg Multiset.sum bags).trans (mem_piAntidiag.mp (mem_filter.mp good).1).1
      have posV (i : Fin h) : 0 < v i := by
        have bm : v i ∈ bag l := bags ▸ Multiset.mem_map.mpr ⟨i,Finset.mem_val.mpr (mem_univ _),rfl⟩
        obtain ⟨t,_,eq⟩ := Multiset.mem_map.mp bm
        exact eq ▸ (mem_filter.mp good).2 t
      have hv : v∈orderings m l := mem_filter.mpr ⟨mem_filter.mpr
        ⟨mem_piAntidiag.mpr ⟨sumV,fun _ _ ↦ mem_univ _⟩,posV⟩,bags⟩
      exact ⟨v,hv,rfl⟩
  rw [bij]
  have total : ∑ i,a i=h := by
    rw [show (∑ i,a i)=∑ i ∈ range (m+1), counts l i from Fin.sum_univ_eq_sum_range (counts l) (m+1)]
    have eq := card_eq_sum_card_fiberwise (s:=univ) (t:=range (m+1)) (f:=l)
      (fun i _ ↦ mem_range.mpr (bound good i))
    simpa [counts] using eq.symm
  have count := card_placements_profile h (id : Fin (m+1) → Fin (m+1)) a total
  have one (i : Fin (m+1)) : counts (id : Fin (m+1) → Fin (m+1)) i=1 := by
    unfold counts
    have e : univ.filter (fun x : Fin (m+1) ↦ id x=i)={i} := by ext x; simp
    rw [e,card_singleton]
  simp only [Function.id_comp,one,one_pow,prod_const_one,mul_one] at count
  change (univ.filter (fun w : Fin h → Fin (m+1) ↦ counts w=a)).card = _
  rw [count]
  simp only [orderMultiplicity,Nat.multinomial,a,Fin.sum_univ_eq_sum_range]
  rw [Fin.prod_univ_eq_prod_range (fun z ↦ (counts l z).factorial) (m+1)]

#print axioms orderings_card
end LongCycleBounds.Occupancy
