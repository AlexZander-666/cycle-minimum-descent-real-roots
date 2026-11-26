import LongCycleBounds.DescentBoundaryDerangementGrid
import LongCycleBounds.DescentBoundaryFiniteBridge
import LongCycleBounds.DescentBoundaryInitialSizes

noncomputable section
namespace LongCycleBounds.DescentBoundary
open Finset Polynomial DescentTwoLetters DescentNecklace DescentDerangement LongCycles FixedCycleCount

theorem row_positive_at_one {n k : ℕ} (lo : 1 ≤ k) (hi : k ≤ n) :
    0 < (realRow n k).eval 1 := by
  classical
  have equal : (realRow n k).eval 1 = (enumerator n k).eval 1 := by
    unfold realRow row enumerator
    rw [Polynomial.map_sum,eval_finsetSum,eval_finsetSum]
    apply sum_congr rfl
    intro σ _
    by_cases h : Allowed k σ <;> simp [h]
  rw [equal]
  by_cases one : k=1
  · subst k
    have all (σ : Equiv.Perm (Fin n)) : Allowed 1 σ := fun _ _ h h' ↦ by omega
    simp [enumerator,all,eval_finsetSum]
    exact Fintype.card_pos
  · have hk : 2 ≤ k := by omega
    have kp : 0 < (k:ℝ) := by positivity
    have pos : 0 < allowedFraction n k := (by positivity : (0:ℝ)<1/(2*(k:ℝ))).trans_le
      (Occupancy.allowedFraction_ge_half hk hi)
    exact (div_pos_iff_of_pos_right (show 0 < (n.factorial:ℝ) by positivity)).mp pos

theorem mixture_ne_zero {n : ℕ} (w : ℕ → ℝ) (hw : ∀ k ∈ Icc 1 n, 0 ≤ w k)
    (pos : ∃ k ∈ Icc 1 n, 0 < w k) : mixture n w ≠ 0 := by
  obtain ⟨j,hj,pj⟩ := pos
  have p : 0 < (mixture n w).eval 1 := by
    simp only [mixture,eval_finsetSum,eval_mul,eval_C]
    exact sum_pos' (fun k hk ↦ mul_nonneg (hw k hk)
      (row_positive_at_one (mem_Icc.mp hk).1 (mem_Icc.mp hk).2).le)
      ⟨j,hj,mul_pos pj (row_positive_at_one (mem_Icc.mp hj).1 (mem_Icc.mp hj).2)⟩
  intro z
  simp [z] at p

/-- Exactly the two supports named in the manuscript create a repeated zero. -/
def ExceptionalSupport (n : ℕ) (w : ℕ → ℝ) : Prop :=
  (n = 4 ∧ w 1 + (w 3+w 4) = 0) ∨ (n = 5 ∧ w 1 + w 2 = 0)

theorem all_cutoffs_from_finite (finite : ∀ m, 6 ≤ m → m ≤ 127 → LowerCutoffMeshCertificate m)
    {n : ℕ} (hn : 1 ≤ n) (w : ℕ → ℝ) (hw : ∀ k ∈ Icc 1 n, 0 ≤ w k)
    (pos : ∃ k ∈ Icc 1 n, 0 < w k) :
    (mixture n w ≠ 0) ∧ (mixture n w).Splits ∧ (∀ x ∈ (mixture n w).roots, x ≤ 0) ∧
      ((mixture n w).roots.Nodup ↔ ¬ExceptionalSupport n w) := by
  refine ⟨mixture_ne_zero w hw pos,?_⟩
  by_cases four : n=4
  · subst n
    obtain ⟨split,roots,simple,_⟩ := four_all_weights w hw pos
    have pp := add_nonneg (hw 1 (by decide)) (add_nonneg (hw 3 (by decide)) (hw 4 (by decide)))
    refine ⟨split,roots,?_⟩
    simpa [ExceptionalSupport,lt_iff_le_and_ne,pp,eq_comm] using simple
  by_cases five : n=5
  · subst n
    obtain ⟨split,roots,simple,_⟩ := five_all_weights w hw pos
    have pp := add_nonneg (hw 1 (by decide)) (hw 2 (by decide))
    refine ⟨split,roots,?_⟩
    simpa [ExceptionalSupport,lt_iff_le_and_ne,pp,eq_comm] using simple
  have regular : (mixture n w).Splits ∧ (mixture n w).roots.Nodup ∧
      ∀ x ∈ (mixture n w).roots, x ≤ 0 := by
    by_cases big : 128 ≤ n
    · exact all_cutoffs_large big w hw pos
    by_cases mid : 6 ≤ n
    · exact all_mixtures_of_certificate (by omega) (finite n mid (by omega)) w hw pos
    have opt : n=1 ∨ n=2 ∨ n=3 := by omega
    rcases opt with rfl|rfl|rfl
    · exact one_all_weights w
    · exact two_all_weights w hw pos
    · exact three_all_weights w hw pos
  exact ⟨regular.1,regular.2.2,by simp [regular.2.1,ExceptionalSupport,four,five]⟩

#print axioms mixture_ne_zero
#print axioms all_cutoffs_from_finite
end LongCycleBounds.DescentBoundary
