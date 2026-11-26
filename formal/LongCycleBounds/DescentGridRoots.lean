import LongCycleBounds.DescentRootGrid
import LongCycleFinite.Interlacing

/-! Exhaustion of the roots from the ordered analytic sign nodes. -/
noncomputable section
namespace LongCycleBounds.DescentMesh
open Polynomial Finset Real LongCycles DescentTwoLetters

theorem row_degree_cap {n k : ℕ} (hn : 3≤n) (hk : 3≤k) :
    ((row n k).map (Int.castRingHom ℝ)).natDegree ≤ n-2 := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n≠0)
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro r hr
  rw [coeff_map]
  suffices h : (row (m+1) k).coeff r=0 by rw [h,map_zero]
  by_cases eq : r=m
  · subst r; exact top_zero m hk
  rw [coeff_row]
  apply sum_eq_zero
  intro σ _
  apply if_neg
  rintro ⟨_,e⟩
  have bound : descents σ ≤ m := by
    rw [descents_eq_card]
    exact (card_filter_le _ _).trans_eq (by simp)
  omega

theorem grid_roots {n : ℕ} (hn : 4≤n) {p : ℝ[X]} (zero : p.eval 0=0)
    (degree : p.natDegree ≤ n-2)
    (signs : ∀ i, 2 ≤ i → i < n → (-1:ℝ)^i*p.eval (rootNode n i)<0) :
    ∃ r : Fin (n-3) → ℝ, StrictAnti r ∧
      (∀ i, rootNode n (i.val+3) < r i ∧ r i < rootNode n (i.val+2) ∧ p.eval (r i)=0) ∧
      p.Splits ∧ p.roots.Nodup ∧ 0 ∈ p.roots ∧ p.natDegree=n-2 ∧
      (p.roots.filter (· < 0)).card=n-3 := by
  classical
  have bracket (i : Fin (n-3)) : ∃ x, rootNode n (i.val+3)<x ∧
      x<rootNode n (i.val+2) ∧ p.eval x=0 := by
    have bound := i.isLt
    apply LongCycleFinite.root_between _ (rootNode_order (by omega) (by omega) (by omega))
    let a := (-1:ℝ)^(i.val+2)
    have h₁ := signs (i.val+2) (by omega) (by omega)
    have h₂ := signs (i.val+3) (by omega) (by omega)
    rw [show i.val+3=i.val+2+1 by omega,pow_succ] at h₂
    have pos := mul_pos_of_neg_of_neg h₁ h₂
    have sq : a*a=1 := by unfold a; rw [← mul_pow]; norm_num
    change 0 < (a*_)*(a*(-1)*_) at pos
    have alg (u v : ℝ) : (a*u)*(a*(-1)*v) = -(v*u) := by calc
      _ = (a*a)*(-(v*u)) := by ring
      _ = _ := by rw [sq,one_mul]
    rw [alg] at pos
    exact neg_pos.mp pos
  choose r located using bracket
  have sorted : StrictAnti r := by
    intro i j ij
    have bound := j.isLt
    have step : rootNode n (j.val+2) ≤ rootNode n (i.val+3) := by
      rcases Nat.eq_or_lt_of_le (by omega : i.val+3 ≤ j.val+2) with eq|lt
      · rw [eq]
      · exact (rootNode_order (by omega) lt (by omega)).le
    exact (located j).2.1.trans_le (step.trans (located i).1.le)
  let negs := (univ : Finset (Fin (n-3))).map (⟨r, sorted.injective⟩ : Fin (n-3) ↪ ℝ)
  have card : negs.card=n-3 := by simp [negs]
  have negative {x : ℝ} (h : x∈negs) : x<0 := by
    obtain ⟨i,_,rfl⟩ := mem_map.mp h
    exact (located i).2.1.trans (nodeAt_negative _)
  have notzero : (0:ℝ)∉negs := fun h ↦ lt_irrefl _ (negative h)
  let all := insert (0:ℝ) negs
  have total : all.card=n-2 := by simp only [all,card_insert_of_notMem notzero,card]; omega
  have nonzero : p≠0 := by
    intro eq
    have h := signs 2 (by omega) (by omega)
    simp [eq] at h
  have eq : p.roots=all.val := by
    apply roots_eq_of_natDegree_le_card_of_ne_zero _ (total ▸ degree) nonzero
    intro x hx
    rcases mem_insert.mp hx with h|h
    · simpa only [h,IsRoot] using zero
    · obtain ⟨i,_,rfl⟩ := mem_map.mp h
      exact (located i).2.2
  have count : p.roots.card=n-2 := eq ▸ total
  have deg := degree.antisymm (count ▸ p.card_roots')
  refine ⟨r,sorted,located,splits_iff_card_roots.mpr (count.trans deg.symm),eq ▸ all.nodup,
    (by rw [eq]; exact (show (0:ℝ) ∈ all from mem_insert_self _ _)),deg,?_⟩
  have filter : all.filter (· < 0)=negs := by
    ext x
    simp only [mem_filter,all,mem_insert]
    exact ⟨fun ⟨h,hx⟩ ↦ h.resolve_left (fun e ↦ (ne_of_lt hx) e),fun h ↦ ⟨Or.inr h,negative h⟩⟩
  rw [eq]
  change (all.filter (· < 0)).card=n-3
  rw [filter,card]

theorem grid_sign_reflect {n i : ℕ} (hi : 2 ≤ i) (hin : i < n) (p : ℝ[X])
    (h : (-1:ℝ)^i * ((rootNode n i)^(n-1)*p.eval (rootNode n i)⁻¹) < 0) :
    (-1:ℝ)^(n+1-i)*p.eval (rootNode n (n+1-i)) < 0 := by
  have neg : rootNode n i < 0 := nodeAt_negative _
  have fact : rootNode n i = (-1)*(-rootNode n i) := by ring
  have powers : (-1:ℝ)^i*(-1)^(n-1)=(-1)^(n+1-i) := by
    rw [← pow_add,show i+(n-1)=(n+1-i)+2*(i-1) by omega,pow_add,pow_mul]
    norm_num
  have hpow := congrArg (fun x : ℝ ↦ x^(n-1)) fact
  simp only [mul_pow] at hpow
  rw [hpow] at h
  have prod : 0 > ((-1:ℝ)^i*(-1)^(n-1)*p.eval (rootNode n i)⁻¹)*(-rootNode n i)^(n-1) := by
    convert h using 1
    ring
  rw [powers] at prod
  rw [rootNode_reflect (by omega)]
  exact neg_of_mul_neg_left prod (pow_pos (neg_pos.mpr neg) _).le

theorem original_grid_roots {n k : ℕ} (hn : 4≤n) (hk : 3≤k)
    (signs : ∀ i, 2 ≤ i → i < n → (-1:ℝ)^i*((row n k).map (Int.castRingHom ℝ)).eval (rootNode n i)<0) :
    let p := (row n k).map (Int.castRingHom ℝ)
    ∃ r : Fin (n-3) → ℝ, StrictAnti r ∧
      (∀ i, rootNode n (i.val+3) < r i ∧ r i < rootNode n (i.val+2) ∧ p.eval (r i)=0) ∧
      p.Splits ∧ p.roots.Nodup ∧ 0 ∈ p.roots ∧ p.natDegree=n-2 ∧
      (p.roots.filter (· < 0)).card=n-3 := by
  apply grid_roots hn _ (row_degree_cap (by omega) hk) signs
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n≠0)
  rw [← coeff_zero_eq_eval_zero,coeff_map,constant_zero _ (by omega),map_zero]

#print axioms original_grid_roots
#print axioms grid_sign_reflect
#print axioms grid_roots
#print axioms row_degree_cap
end LongCycleBounds.DescentMesh
