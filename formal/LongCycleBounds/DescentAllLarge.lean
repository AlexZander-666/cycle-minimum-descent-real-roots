import LongCycleBounds.DescentGridRoots
import LongCycleBounds.DescentActualEnd

/-! Complete location of the roots of every original ordinary-descent row at large sizes. -/
noncomputable section
namespace LongCycleBounds.DescentMesh
open Real Polynomial DescentTwoLetters Finset

private theorem regimes {n i : ℕ} (hn : 128 ≤ n) (half : 2*i≤n+1) :
    (π/(2*sqrt ((n:ℝ)+1)) ≤ gridAngle n i ∧ gridAngle n i ≤ π/2) ∨
    (4*(i:ℝ)^2 ≤ (n:ℝ)+1 ∧ gridAngle n i < π/2) := by
  let N := (n:ℝ)+1
  have np : 0<N := by dsimp [N]; positivity
  have sp : 0<sqrt N := sqrt_pos.mpr np
  have sq := sq_sqrt np.le
  have h2 : 2*(i:ℝ) ≤ N := by dsimp [N]; exact_mod_cast half
  have n128 : 128≤(n:ℝ) := by exact_mod_cast hn
  have fr : sqrt N<N := by dsimp [N] at *; nlinarith
  by_cases h : sqrt N ≤ 2*(i:ℝ)
  · left
    constructor
    · change π/(2*sqrt N) ≤ π*(i:ℝ)/N
      rw [div_le_div_iff₀ (by positivity) np]
      have z := mul_le_mul_of_nonneg_right h sp.le
      nlinarith only [mul_nonneg pi_pos.le (sub_nonneg.mpr z),congrArg (fun x : ℝ ↦ π*x) sq]
    · change π*(i:ℝ)/N ≤ π/2
      rw [div_le_div_iff₀ np (by norm_num)]
      nlinarith only [mul_nonneg pi_pos.le (sub_nonneg.mpr h2)]
  · right
    have h' := lt_of_not_ge h
    constructor
    · change 4*(i:ℝ)^2 ≤ N
      have nn : 0≤(i:ℝ) := by positivity
      nlinarith only [sq,sq_nonneg (sqrt N-2*(i:ℝ)),mul_nonneg (sub_nonneg.mpr h'.le)
        (add_nonneg sp.le (mul_nonneg (by norm_num : (0:ℝ)≤2) nn))]
    · change π*(i:ℝ)/N < π/2
      rw [div_lt_div_iff₀ np (by norm_num)]
      nlinarith only [mul_pos pi_pos (sub_pos.mpr (h'.trans fr))]

private theorem grid_half_both {n k i : ℕ} (hk : 3≤k) (kn : k≤n) (hn : 128≤n) (hi : 2 ≤ i)
    (half : 2*i≤n+1) :
    let p := (row n k).map (Int.castRingHom ℝ)
    let t := rootNode n i
    (-1:ℝ)^i*p.eval t<0 ∧ (-1:ℝ)^i*(t^(n-1)*p.eval t⁻¹)<0 := by
  have angle := (gridAngle_bounds (by omega : 0 < i) (by omega : i < n+1)).1
  have phase := gridAngle_phase n i
  rcases regimes hn half with ⟨lo,hi⟩|⟨small,top⟩
  · exact ⟨central_sign_actual hk kn hn lo hi phase,central_sign_actual_reciprocal hk kn hn lo hi phase⟩
  · exact ⟨end_sign_actual hk kn hn hi angle top phase small,
      end_sign_actual_reciprocal hk kn hn hi angle top phase small⟩

theorem actual_grid_sign {n k i : ℕ} (hk : 3≤k) (kn : k≤n) (hn : 128≤n) (hi : 2 ≤ i)
    (last : i < n) : (-1:ℝ)^i*((row n k).map (Int.castRingHom ℝ)).eval (rootNode n i)<0 := by
  by_cases half : 2*i≤n+1
  · exact (grid_half_both hk kn hn hi half).1
  · have ref := (grid_half_both hk kn hn (i:=n+1-i) (by omega) (by omega)).2
    simpa only [show n+1-(n+1-i)=i by omega] using
      grid_sign_reflect (by omega : 2 ≤ n+1-i) (by omega : n+1-i < n) _ ref

theorem roots_all_large {n k : ℕ} (hk : 3≤k) (kn : k≤n) (hn : 128≤n) :
    let p := (row n k).map (Int.castRingHom ℝ)
    ∃ r : Fin (n-3) → ℝ, StrictAnti r ∧
      (∀ i, rootNode n (i.val+3) < r i ∧ r i < rootNode n (i.val+2) ∧ p.eval (r i)=0) ∧
      p.Splits ∧ p.roots.Nodup ∧ 0 ∈ p.roots ∧ p.natDegree=n-2 ∧
      (p.roots.filter (· < 0)).card=n-3 :=
  original_grid_roots (by omega) hk fun _ hi last ↦ actual_grid_sign hk kn hn hi last

/-- Every nonzero nonnegative mixture shares the same strictly separated intervals. -/
theorem mixtures_all_large {n : ℕ} (hn : 128≤n) (w : ℕ → ℝ)
    (hw : ∀ k ∈ Icc 3 n, 0≤w k) (hwpos : ∃ k ∈ Icc 3 n, 0<w k) :
    let p := ∑ k ∈ Icc 3 n, C (w k)*((row n k).map (Int.castRingHom ℝ))
    ∃ r : Fin (n-3) → ℝ, StrictAnti r ∧
      (∀ i, rootNode n (i.val+3) < r i ∧ r i < rootNode n (i.val+2) ∧ p.eval (r i)=0) ∧
      p.Splits ∧ p.roots.Nodup ∧ 0 ∈ p.roots ∧ p.natDegree=n-2 ∧
      (p.roots.filter (· < 0)).card=n-3 := by
  apply grid_roots (by omega)
  · rw [eval_finsetSum]
    apply sum_eq_zero
    intro k hk
    have h3 := (mem_Icc.mp hk).1
    obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n≠0)
    rw [eval_mul,eval_C,← coeff_zero_eq_eval_zero,coeff_map,constant_zero m (by omega),map_zero,mul_zero]
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro d hd
    rw [finsetSum_coeff]
    apply sum_eq_zero
    intro k hk
    rw [coeff_C_mul,natDegree_le_iff_coeff_eq_zero.mp
      (row_degree_cap (by omega : 3≤n) (mem_Icc.mp hk).1) d hd,mul_zero]
  · intro i hi last
    rw [eval_finsetSum, mul_sum]
    have each (k : ℕ) (hk : k∈Icc 3 n) := actual_grid_sign (mem_Icc.mp hk).1 (mem_Icc.mp hk).2 hn hi last
    simp only [eval_mul,eval_C]
    have eq (k : ℕ) (v : ℝ) : (-1:ℝ)^i*(w k*v)=w k*((-1)^i*v) := by ring
    simp_rw [eq]
    obtain ⟨k,hk,pos⟩ := hwpos
    exact sum_neg' (fun j hj ↦ mul_nonpos_of_nonneg_of_nonpos (hw j hj) (each j hj).le)
      ⟨k,hk,mul_neg_of_pos_of_neg pos (each k hk)⟩

#print axioms mixtures_all_large
#print axioms actual_grid_sign
#print axioms roots_all_large
end LongCycleBounds.DescentMesh
