import LongCycleBounds.DescentFiniteBlocks

/-! Common dyadic brackets survive all nonzero nonnegative linear combinations. -/
noncomputable section
namespace LongCycleBounds.DescentNecklace
open Finset LongCycleFinite Polynomial

private abbrev node (a : Array LongCycleFinite.Dyadic) (i : ℕ) := a.getD i LongCycleFinite.Dyadic.zero
private abbrev orientation (d i : ℕ) := decide ((d-i)%2=1)

private theorem exact_node_sign {c : List ℤ} {a : Array LongCycleFinite.Dyadic} (check : negativeMeshOK c a=true)
    {i : ℕ} (hi : i < a.size) :
    HasSign (orientation (a.size-1) i) ((ofCoeffs c).eval (node a i).value) := by
  have h := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp check).1).2
  exact K3.naturalSign_sound (Bool.and_eq_true_iff.mp (List.all_eq_true.mp h i (List.mem_range.mpr hi))).2

private theorem intervals_order {c : List ℤ} {a : Array LongCycleFinite.Dyadic} (check : negativeMeshOK c a=true)
    {i j : ℕ} (hi : i≤j) (hj : j < a.size) : (node a i).value ≤ (node a j).value := by
  induction j with
  | zero => simp [Nat.eq_zero_of_le_zero hi]
  | succ j ih =>
    by_cases h : i=j+1
    · rw [h]
    · apply (ih (by omega) (by omega)).trans
      exact ((Dyadic.less_iff _ _).mp (List.all_eq_true.mp (Bool.and_eq_true_iff.mp check).2 j
        (List.mem_range.mpr (by omega)))).le

private theorem weigh_sign {b : Bool} {f w : ℕ → ℝ} {s : Finset ℕ}
    (sign : ∀ k ∈ s, HasSign b (f k)) (pos : ∃ k ∈ s, 0<w k) (nonneg : ∀ k ∈ s, 0≤w k) :
    HasSign b (∑ k ∈ s,w k*f k) := by
  obtain ⟨k,hk,hw⟩ := pos
  cases b
  · exact sum_pos' (fun j hj ↦ mul_nonneg (nonneg j hj) (le_of_lt (show 0<f j from sign j hj)))
      ⟨k,hk,mul_pos hw (sign k hk)⟩
  · exact sum_neg' (fun j hj ↦ mul_nonpos_of_nonneg_of_nonpos (nonneg j hj) (le_of_lt (show f j<0 from sign j hj)))
      ⟨k,hk,mul_neg_of_pos_of_neg hw (sign k hk)⟩

theorem mixture_dyadic_roots {s : Finset ℕ} (cs : ℕ → List ℤ) {a : Array LongCycleFinite.Dyadic} (w : ℕ → ℝ)
    (check : ∀ k ∈ s, negativeMeshOK (cs k) a=true)
    (pos : ∃ k ∈ s, 0<w k) (nonneg : ∀ k ∈ s, 0≤w k) :
    Nonempty (QuotientMeshRoots (∑ k ∈ s, C (w k)*ofCoeffs (cs k)) a (a.size-1)) := by
  classical
  let p := ∑ k ∈ s, C (w k)*ofCoeffs (cs k)
  have ev (x : ℝ) : p.eval x = ∑ k ∈ s,w k*(ofCoeffs (cs k)).eval x := by simp [p,eval_finsetSum]
  obtain ⟨k₀,h₀,_⟩ := (show ∃ k ∈ s, 0 < w k from pos)
  have rep := check k₀ h₀
  have witness (k : ℕ) (hk : k∈s) := (negativeMeshOK_sound (check k hk)).some
  have P0 : 0<p.eval 0 := by
    rw [ev]; exact weigh_sign (b:=false) (fun k hk ↦ (witness k hk).positiveAtZero) pos nonneg
  have cap : p.natDegree≤a.size-1 := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    simp only [p,finsetSum_coeff,coeff_C_mul]
    apply sum_eq_zero
    intro k hk
    rw [natDegree_le_iff_coeff_eq_zero.mp (witness k hk).degreeBound i hi,mul_zero]
  have vals {i : ℕ} (hi : i < a.size) :
      HasSign (orientation (a.size-1) i) (p.eval (node a i).value) := by
    rw [ev]
    exact weigh_sign (fun k hk ↦ exact_node_sign (check k hk) hi) pos nonneg
  have bracket (i : Fin (a.size-1)) : ∃ x, (node a i.val).value<x ∧
      x<(node a (i.val+1)).value ∧ p.eval x=0 := by
    have h := i.isLt
    apply root_between
    · exact (Dyadic.less_iff _ _).mp (List.all_eq_true.mp (Bool.and_eq_true_iff.mp rep).2 _ (List.mem_range.mpr h))
    · have l := vals (i:=i.val) (by omega)
      have r := vals (i:=i.val+1) (by omega)
      by_cases odd : (a.size-1-i.val)%2=1
      · have even : (a.size-1-(i.val+1))%2 ≠ 1 := by omega
        exact mul_neg_of_neg_of_pos (by simpa [HasSign,orientation,odd] using l)
          (by simpa [HasSign,orientation,even] using r)
      · have next : (a.size-1-(i.val+1))%2=1 := by omega
        exact mul_neg_of_pos_of_neg (by simpa [HasSign,orientation,odd] using l)
          (by simpa [HasSign,orientation,next] using r)
  choose r loc using bracket
  have sorted : StrictMono r := by
    intro i j ij
    have hj := j.isLt
    have step := intervals_order rep (by exact ij : i.val+1≤j.val) (by omega : j.val<a.size)
    exact (loc i).2.1.trans_le (step.trans (loc j).1.le)
  have neg (i : Fin (a.size-1)) : r i<0 := by
    have h := i.isLt
    have data := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp rep).1).2
    have x := (Dyadic.less_iff _ _).mp (Bool.and_eq_true_iff.mp
      (List.all_eq_true.mp data (i.val+1) (List.mem_range.mpr (by omega)))).1
    change (node a (i.val+1)).value < LongCycleFinite.Dyadic.zero.value at x
    rw [LongCycleFinite.Dyadic.value_zero] at x
    exact (loc i).2.1.trans x
  have ne : p≠0 := fun e ↦ by simp [e] at P0
  exact ⟨⟨r,P0,cap,sorted,neg,fun i ↦ (loc i).2.2,fun i ↦ ⟨(loc i).1,(loc i).2.1⟩,
    factor_of_degree_bound r ne cap sorted.injective (fun i ↦ (loc i).2.2)⟩⟩

/-- A common dyadic certificate at one size gives the original weighted polynomial,
with one root in each common interval and simplicity after reinserting zero. -/
theorem representative_mixtures {n : ℕ} (hn : 3≤n) {a : Array LongCycleFinite.Dyadic}
    (size : a.size=n-2) {rows : Array (List ℤ)} (checks : RepresentativeChecks n a rows)
    (w : ℕ→ℝ) (nonneg : ∀ k ∈ Icc 3 n, 0≤w k) (pos : ∃ k ∈ Icc 3 n, 0<w k) :
    let p := ∑ k ∈ Icc 3 n, C (w k)*(DescentTwoLetters.row n k).map (Int.castRingHom ℝ)
    ∃ q : ℝ[X], p=X*q ∧ Nonempty (QuotientMeshRoots q a (n-3)) ∧
      p.Splits ∧ p.roots.Nodup ∧ 0 ∈ p.roots ∧ p.roots.card=n-2 ∧
      (p.roots.filter (· < 0)).card=n-3 := by
  classical
  let cut (k : ℕ) := min k (lastRepresentative n)
  let cs (k : ℕ) := rows.getD (cut k-3) []
  have data (k : ℕ) (hk : k∈Icc 3 n) :
      (DescentTwoLetters.row n k).map (Int.castRingHom ℝ) = X*ofCoeffs (cs k) ∧
      negativeMeshOK (cs k) a=true := by
    have b := mem_Icc.mp hk
    have lower : 3≤cut k := le_min b.1 (le_max_left ..)
    have upper : cut k≤lastRepresentative n := min_le_right .. 
    let idx : Fin (lastRepresentative n-2) := ⟨cut k-3,by omega⟩
    obtain ⟨counts,signs⟩ := checks idx
    change descentRowDP n (cut k-3+3)=(0::cs k)++[0] at counts
    rw [Nat.sub_add_cancel lower] at counts
    exact ⟨by rw [row_eq_representative b.1 b.2]; exact row_eq_of_checkedCoeffs (by omega) counts,signs⟩
  let q := ∑ k ∈ Icc 3 n, C (w k)*ofCoeffs (cs k)
  have split : (∑ k ∈ Icc 3 n, C (w k)*(DescentTwoLetters.row n k).map (Int.castRingHom ℝ))=X*q := by
    simp only [q,mul_sum]
    exact sum_congr rfl fun k hk ↦ by rw [(data k hk).1]; ring
  obtain ⟨r⟩ := mixture_dyadic_roots cs w (fun k hk ↦ (data k hk).2) pos nonneg
  have d : a.size-1=n-3 := by omega
  have plus : n-3+1=n-2 := by omega
  refine ⟨q,split,d ▸ ⟨r⟩,?_⟩
  rw [split]
  simpa only [d,plus] using r.full_root_count

#print axioms representative_mixtures
#print axioms mixture_dyadic_roots
end LongCycleBounds.DescentNecklace
