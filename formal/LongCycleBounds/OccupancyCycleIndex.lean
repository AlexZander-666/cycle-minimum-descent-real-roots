import LongCycleBounds.OccupancyAllocations
import Mathlib.GroupTheory.Perm.Centralizer

/-! Cardinality of a prescribed complete slot-cycle profile, with all fixed slots included. -/
noncomputable section
namespace LongCycleBounds.Occupancy
open Equiv Finset
open scoped Classical

/-- Full slot-cycle lengths recorded as a multiset, so singleton slots are retained. -/
def bag {h : ℕ} (l : Fin h → ℕ) : Multiset ℕ := univ.val.map l

private theorem bag_count {h : ℕ} (l : Fin h → ℕ) (i : ℕ) :
    (bag l).count i = counts l i := by
  unfold bag counts
  rw [Multiset.count_map,←Finset.filter_val]
  simp only [eq_comm (a:=i)]
  rfl

def matchingPerms {h : ℕ} (m : ℕ) (l : Fin h → ℕ) : Finset (Perm (Fin m)) :=
  univ.filter (fun σ ↦ σ.partition.parts = bag l)

private theorem split_parts (u : Multiset ℕ) (pos : ∀ i∈u, 0 < i) :
    u = u.filter (2 ≤ ·) + Multiset.replicate (u.count 1) 1 := by
  ext i
  by_cases one : i=1
  · subst i; simp
  · have zero : (Multiset.replicate (u.count 1) 1).count i=0 :=
      Multiset.count_eq_zero.mpr (fun e ↦ one (Multiset.eq_of_mem_replicate e))
    rw [Multiset.count_add,zero,add_zero,Multiset.count_filter]
    by_cases hi : 2 ≤ i
    · simp [hi]
    · have absent : i∉u := fun hin ↦ by have := pos i hin; omega
      simp [Multiset.count_eq_zero.mpr absent,hi]

private theorem multiplicities (u : Multiset ℕ) (m : ℕ) (hm : 0 < m)
    (pos : ∀ i∈u, 0 < i) (cap : ∀ i∈u, i ≤ m) :
    (∏ i ∈ range (m+1), (u.count i).factorial) =
      (u.count 1).factorial * ∏ i ∈ (u.filter (2 ≤ ·)).toFinset, ((u.filter (2 ≤ ·)).count i).factorial := by
  let t := u.filter (2 ≤ ·)
  have sub : insert 1 t.toFinset ⊆ range (m+1) := by
    intro i hi
    rcases mem_insert.mp hi with rfl | hit
    · exact mem_range.mpr (by omega)
    · have hu := (Multiset.mem_filter.mp (Multiset.mem_toFinset.mp hit)).1
      exact mem_range.mpr (by have := cap i hu;omega)
  have off (i : ℕ) (_ : i∈range (m+1)) (hi : i∉insert 1 t.toFinset) :
      (u.count i).factorial=1 := by
    have hu : i∉u := by
      intro hiu
      have p := pos i hiu
      have ne : i≠1 := fun e ↦ hi (mem_insert.mpr (Or.inl e))
      exact hi (mem_insert.mpr (Or.inr (Multiset.mem_toFinset.mpr
        (Multiset.mem_filter.mpr ⟨hiu,by omega⟩))))
    simp [Multiset.count_eq_zero.mpr hu]
  have one : 1∉t.toFinset := by simp [t]
  rw [←prod_subset sub off, prod_insert one]
  congr 1
  apply prod_congr rfl
  intro i hi
  exact congrArg Nat.factorial (Multiset.count_filter_of_pos (Multiset.mem_filter.mp
    (Multiset.mem_toFinset.mp hi)).2).symm

/-- Finite class equation for the actual permutations of the m slots. The product over
all lengths includes the factorial for repeated fixed points. -/
theorem matchingPerms_card {h m : ℕ} (hm : 0 < m) (l : Fin h → ℕ)
    (pos : ∀ i, 0 < l i) (total : ∑ i,l i=m) :
    (matchingPerms m l).card * ((∏ i,l i) * ∏ a ∈ range (m+1),(counts l a).factorial) = m.factorial := by
  let u := bag l
  let t := u.filter (2 ≤ ·)
  have us : u.sum=m := total
  have up (i) (hi : i∈u) : 0 < i := by obtain ⟨b,_,rfl⟩ := Multiset.mem_map.mp hi;exact pos b
  have ub (i) (hi : i∈u) : i ≤ m := by
    obtain ⟨b,_,rfl⟩ := Multiset.mem_map.mp hi
    exact (single_le_sum (f:=l) (fun _ _ ↦ Nat.zero_le _) (mem_univ b)).trans_eq total
  have split : u=t+Multiset.replicate (u.count 1) 1 := split_parts u up
  have mass : t.sum+u.count 1=m := by
    calc _ = (t+Multiset.replicate (u.count 1) 1).sum := by simp
      _ = m := split ▸ us
  have hi : t.sum ≤ m := by omega
  have tpos (a : ℕ) (ha : a∈t) : 2 ≤ a := (Multiset.mem_filter.mp ha).2
  have filt : matchingPerms m l = univ.filter (fun σ : Perm (Fin m) ↦ σ.cycleType=t) := by
    ext σ
    simp only [matchingPerms,mem_filter,mem_univ,true_and]
    constructor
    · intro eq
      change σ.cycleType=(bag l).filter (2 ≤ ·)
      rw [←eq,Perm.filter_parts_partition_eq_cycleType]
    · intro eq
      change σ.partition.parts=u
      rw [Perm.parts_partition,←Perm.sum_cycleType,eq,Fintype.card_fin,
        show m-t.sum=u.count 1 by omega,←split]
  have classEq := Perm.card_of_cycleType_mul_eq (Fin m) t
  simp only [Fintype.card_fin,if_pos (And.intro hi tpos)] at classEq
  have product : (∏ i,l i)=t.prod := by
    change u.prod=t.prod
    conv_lhs => rw [split,Multiset.prod_add]; simp
  have countEq : ∀ a, counts l a = u.count a := fun a ↦ (bag_count l a).symm
  simp only [filt,product,countEq,multiplicities u m hm up ub]
  rw [show m-t.sum=u.count 1 by omega] at classEq
  convert classEq using 1
  ring

#print axioms matchingPerms_card
end LongCycleBounds.Occupancy
