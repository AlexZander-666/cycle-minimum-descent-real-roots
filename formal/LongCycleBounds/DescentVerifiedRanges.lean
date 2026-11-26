import LongCycleBounds.DescentMixturesThrough32
import LongCycleBounds.DescentAllLarge
import LongCycleBounds.DescentFiniteThrough32

/-! Unconditional real splitting on the directly checked prefix and the entire analytic range. -/
noncomputable section
namespace LongCycleBounds.DescentNecklace
open Finset Polynomial DescentTwoLetters DescentMesh

theorem original_splits_verified_ranges {n k : ℕ} (hk : 3≤k) (kn : k≤n)
    (range : n≤32 ∨ 128≤n) : ((row n k).map (Int.castRingHom ℝ)).Splits := by
  rcases range with small|large
  · exact splits_through32 (by omega) small hk kn
  · obtain ⟨_,_,_,splits,_⟩ := roots_all_large hk kn large
    exact splits

theorem mixtures_split_verified_ranges {n : ℕ} (hn : 3≤n) (range : n≤32 ∨ 128≤n)
    (w : ℕ→ℝ) (nonneg : ∀ k ∈ Icc 3 n, 0≤w k) (positive : ∃ k ∈ Icc 3 n, 0<w k) :
    (∑ k ∈ Icc 3 n,C (w k)*(row n k).map (Int.castRingHom ℝ)).Splits := by
  rcases range with small|large
  · exact mixture_splits_through32 hn small w nonneg positive
  · obtain ⟨_,_,_,split,_⟩ := mixtures_all_large large w nonneg positive
    exact split

private theorem finite_mesh_geometry {a : Array LongCycleFinite.Dyadic} {c : List ℤ}
    (check : negativeMeshOK c a=true) :
    let u := fun i : ℕ ↦ (a.getD i LongCycleFinite.Dyadic.zero).value
    (∀ i, i < a.size → u i<0) ∧ (∀ i j, i ≤ j → j < a.size → u i≤u j) := by
  dsimp only
  constructor
  · intro i hi
    have data := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp check).1).2
    have h := (LongCycleFinite.Dyadic.less_iff _ _).mp (Bool.and_eq_true_iff.mp
      (List.all_eq_true.mp data i (List.mem_range.mpr hi))).1
    change (a.getD i LongCycleFinite.Dyadic.zero).value < LongCycleFinite.Dyadic.zero.value at h
    rwa [LongCycleFinite.Dyadic.value_zero] at h
  · intro i j hij hj
    induction j with
    | zero => simp [Nat.eq_zero_of_le_zero hij]
    | succ j ih =>
      rcases Nat.eq_or_lt_of_le hij with eq|lt
      · rw [eq]
      · apply (ih (by omega) (by omega)).trans
        exact ((LongCycleFinite.Dyadic.less_iff _ _).mp (List.all_eq_true.mp
          (Bool.and_eq_true_iff.mp check).2 j (List.mem_range.mpr (by omega)))).le

private theorem separated_of_le {a b c d : ℝ} (le : b≤c) :
    Disjoint (Set.Ioo a b) (Set.Ioo c d) :=
  Set.Ioo_disjoint_Ioo.mpr ((min_le_left ..).trans (le.trans (le_max_right ..)))

/-- One negative interval system works simultaneously for every nonzero nonnegative mixture. -/
def SharedRootIntervals (n : ℕ) : Prop :=
    ∃ lower upper : Fin (n-3)→ℝ, (∀ i, upper i<0) ∧
      Pairwise (fun i j ↦ Disjoint (Set.Ioo (lower i) (upper i)) (Set.Ioo (lower j) (upper j))) ∧
      ∀ w : ℕ→ℝ,
      (∀ k ∈ Icc 3 n, 0≤w k) → (∃ k ∈ Icc 3 n, 0<w k) →
      let p := ∑ k ∈ Icc 3 n,C (w k)*(row n k).map (Int.castRingHom ℝ)
      ∃ r : Fin (n-3)→ℝ, Function.Injective r ∧
        (∀ i, lower i < r i ∧ r i < upper i ∧ r i<0 ∧ p.eval (r i)=0) ∧
        p.Splits ∧ p.roots.Nodup ∧ 0∈p.roots ∧ p.natDegree=n-2 ∧ (p.roots.filter (· < 0)).card=n-3

theorem shared_intervals_of_evidence {n : ℕ} (hn : 3≤n)
    (evidence : (∃ a : Array LongCycleFinite.Dyadic, ∃ rows : Array (List ℤ),
      a.size=n-2 ∧ RepresentativeChecks n a rows) ∨ 128≤n) :
    SharedRootIntervals n := by
  rcases evidence with finite|large
  · obtain ⟨nodes,rows,size,checks⟩ := finite
    have rep : 0 < lastRepresentative n - 2 := by have h : 3≤lastRepresentative n := le_max_left ..; omega
    have geom := finite_mesh_geometry (checks ⟨0,rep⟩).2
    refine ⟨fun i ↦ (nodes.getD i.val LongCycleFinite.Dyadic.zero).value,
      fun i ↦ (nodes.getD (i.val+1) LongCycleFinite.Dyadic.zero).value,?_,?_,?_⟩
    · intro i; have hi := i.isLt; exact geom.1 _ (by omega)
    · intro i j ne
      rcases lt_or_gt_of_ne ne with lt|gt
      · exact separated_of_le (geom.2 (i.val+1) j.val (by exact lt) (by have h := j.isLt; omega))
      · exact (separated_of_le (geom.2 (j.val+1) i.val (by exact gt) (by have h := i.isLt; omega))).symm
    intro w hw hp
    obtain ⟨q,eq,⟨m⟩,split,nodup,zero,card,neg⟩ := representative_mixtures hn size checks w hw hp
    refine ⟨m.point,m.ordered.injective,fun i ↦ ⟨(m.located i).1,(m.located i).2,m.negative i,?_⟩,
      split,nodup,zero,(splits_iff_card_roots.mp split).symm.trans card,neg⟩
    rw [eq,eval_mul,m.roots,mul_zero]
  · refine ⟨fun i ↦ rootNode n (i.val+3),fun i ↦ rootNode n (i.val+2),fun _ ↦ nodeAt_negative _,?_,?_⟩
    · have sep (i j : Fin (n-3)) (lt : i < j) : rootNode n (j.val+2)≤rootNode n (i.val+3) := by
        rcases Nat.eq_or_lt_of_le (by omega : i.val+3 ≤ j.val+2) with eq|h
        · rw [eq]
        · exact (rootNode_order (by omega) h (by have hj := j.isLt; omega)).le
      intro i j ne
      rcases lt_or_gt_of_ne ne with lt|gt
      · exact (separated_of_le (sep i j lt)).symm
      · exact separated_of_le (sep j i gt)
    intro w hw hp
    obtain ⟨r,strict,located,rest⟩ := mixtures_all_large large w hw hp
    exact ⟨r,strict.injective,fun i ↦ ⟨(located i).1,(located i).2.1,
      (located i).2.1.trans (nodeAt_negative _),(located i).2.2⟩,rest⟩


theorem common_root_intervals_verified {n : ℕ} (hn : 3≤n) (five : n≠5)
    (range : n≤32 ∨ 128≤n) : SharedRootIntervals n :=
  shared_intervals_of_evidence hn (range.imp_left fun upper ↦
    FrozenCertificates.finite_certificate_through32 hn upper five)

#print axioms original_splits_verified_ranges
#print axioms mixtures_split_verified_ranges
#print axioms common_root_intervals_verified
end LongCycleBounds.DescentNecklace

