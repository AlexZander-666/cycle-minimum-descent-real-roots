import LongCycleBounds.OrdinaryEulerianAllVerified

/-! Positive mixtures of the ordinary descent quotients at fixed rank have
the same strict Eulerian interlacer. -/
noncomputable section
namespace LongCycleBounds.OrdinaryEulerianGap
open Polynomial Finset LongCycles LongCycleFinite DescentNecklace DescentTwoLetters

/-- Pair each gap-root with the upper root on the same side of the given node. -/
private theorem nodal_product {d : ℕ} (r : Fin d → ℝ) (s : Fin (d+1) → ℝ)
    (inc : StrictMono s) (gap : ∀ j, s j.castSucc < r j ∧ r j < s j.succ)
    (i : Fin (d+1)) :
    0 < (∏ j, (X-C (r j) : ℝ[X])).eval (s i) *
      (∏ j, (X-C (s j) : ℝ[X])).derivative.eval (s i) := by
  rw [i.prod_univ_succAbove (fun j ↦ X-C (s j) : Fin (d+1) → ℝ[X]), derivative_mul]
  simp only [derivative_X_sub_C, one_mul, eval_add, eval_mul, eval_sub, eval_X, eval_C,
    sub_self, zero_mul, add_zero, eval_prod]
  rw [← prod_mul_distrib]
  apply prod_pos
  intro j _
  by_cases h : j.castSucc < i
  · rw [Fin.succAbove_of_castSucc_lt _ _ h]
    have le : j.succ ≤ i := h
    exact mul_pos (sub_pos.mpr ((gap j).2.trans_le (inc.monotone le))) (sub_pos.mpr (inc h))
  · have le : i ≤ j.castSucc := le_of_not_gt h
    rw [Fin.succAbove_of_le_castSucc _ _ le]
    exact mul_pos_of_neg_of_neg (sub_neg.mpr ((inc.monotone le).trans_lt (gap j).1))
      (sub_neg.mpr (inc (le.trans_lt j.castSucc_lt_succ)))


/-- A positive lower leading coefficient fixes the sign intrinsically at each upper zero. -/
private theorem derivative_pair {p q : ℝ[X]} {d : ℕ} (inter : StrictNegativeInterlacing p q d)
    (hp : 0 < p.leadingCoeff) (hq : q.Monic) {t : ℝ} (ht : q.eval t = 0) :
    0 < p.eval t * q.derivative.eval t := by
  obtain ⟨r,s,_,_,fp,fq,_,inc,_,_,gap⟩ := inter
  have fq' : q = ∏ j, (X-C (s j)) := by simpa only [hq.leadingCoeff,map_one,one_mul] using fq
  have hit := ht
  simp only [fq',eval_prod,eval_sub,eval_X,eval_C,Finset.prod_eq_zero_iff,
    mem_univ,true_and,sub_eq_zero] at hit
  obtain ⟨i,hi⟩ := hit
  rw [hi,fp,fq',eval_mul,eval_C,mul_assoc]
  exact mul_pos hp (nodal_product r s inc gap i)

/-- At least one original permutation contributes to the leading term of a nonzero row. -/
private theorem quotient_leading_positive {n k : ℕ}
    (hn : 6 ≤ n) (hk : 3 ≤ k) (kn : k ≤ n) :
    0 < (EulerianBrackets.originalQuotient n k).leadingCoeff := by
  obtain ⟨_,_,nz,_⟩ := original_all hn hk kn
  apply lt_of_le_of_ne _ (Ne.symm nz)
  let i := (EulerianBrackets.originalQuotient n k).natDegree
  change 0 ≤ (EulerianBrackets.originalQuotient n k).coeff i
  rw [EulerianBrackets.originalQuotient,coeff_divX,coeff_map]
  have h : 0 ≤ (row n k).coeff (i+1) := by
    rw [coeff_row]
    exact sum_nonneg fun _ _ ↦ by split <;> norm_num
  change 0 ≤ ((row n k).coeff (i+1) : ℝ)
  exact_mod_cast h

private theorem strict_of_node_products {d : ℕ} (P : ℝ[X]) (cap : P.natDegree ≤ d)
    (nodes : ∀ t : ℝ, (eulerian (d+1+1)).eval t = 0 →
      0 < P.eval t * (eulerian (d+1+1)).derivative.eval t) :
    StrictNegativeInterlacing P (eulerian (d+1+1)) d := by
  have back : (X*P).divX = P := by ext i; simp [coeff_divX, coeff_X_mul]
  rw [← back]
  apply strict_between_eulerian
  · simp
  · exact natDegree_mul_le.trans (by rw [natDegree_X]; omega)
  · intro t ht hz
    rw [longEulerian_succ (d+1+1)]
    simp only [eval_add,eval_mul,eval_sub,eval_X,eval_one,hz,mul_zero,zero_add]
    have pos := mul_pos (mul_pos (sq_pos_of_ne_zero ht.ne) (by linarith : 0 < 1-t)) (nodes t hz)
    linarith only [show 0 < t^2*(1-t)*(P.eval t*(eulerian (d+1+1)).derivative.eval t) from pos]

/-- Every nonzero nonnegative combination of whole cutoff rows has one simple zero
in every open gap of the preceding Eulerian polynomial after division by X. -/
theorem original_mixture_all {n : ℕ} (hn : 6 ≤ n) (w : ℕ → ℝ)
    (hw : ∀ k ∈ Icc 3 n, 0 ≤ w k) (hp : ∃ k ∈ Icc 3 n, 0 < w k) :
    StrictNegativeInterlacing
      (∑ k ∈ Icc 3 n, C (w k) * EulerianBrackets.originalQuotient n k)
      (eulerian (n-1)) (n-3) := by
  classical
  let P := ∑ k ∈ Icc 3 n, C (w k) * EulerianBrackets.originalQuotient n k
  have cap : P.natDegree ≤ n-3 := by
    apply natDegree_sum_le_of_forall_le
    intro k hk
    apply (natDegree_C_mul_le _ _).trans
    rw [EulerianBrackets.originalQuotient,natDegree_divX_eq_natDegree_tsub_one]
    have := DescentMesh.row_degree_cap (by omega : 3 ≤ n) (mem_Icc.mp hk).1
    omega
  have dim : n-3+1+1 = n-1 := by omega
  rw [← dim]
  apply strict_of_node_products P cap
  rw [dim]
  intro t ht
  have mq : (eulerian (n-1)).Monic := by
    simpa only [show n-2+1=n-1 by omega] using (eulerian_degree_monic (n-2)).2
  have sign k (hk : k ∈ Icc 3 n) := derivative_pair
    (original_all hn (mem_Icc.mp hk).1 (mem_Icc.mp hk).2)
    (quotient_leading_positive hn (mem_Icc.mp hk).1 (mem_Icc.mp hk).2) mq ht
  simp only [P,eval_finsetSum,eval_mul,eval_C,Finset.sum_mul,mul_assoc]
  obtain ⟨j,hj,positive⟩ := hp
  exact sum_pos' (fun k hk ↦ mul_nonneg (hw k hk) (sign k hk).le)
    ⟨j,hj,mul_pos positive (sign j hj)⟩

#print axioms original_mixture_all
end LongCycleBounds.OrdinaryEulerianGap

