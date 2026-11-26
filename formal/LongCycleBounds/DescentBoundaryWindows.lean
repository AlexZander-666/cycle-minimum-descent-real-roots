import LongCycleBounds.DescentBoundarySmallRows
import Mathlib.Analysis.Polynomial.Basic

/-! Count roots from finite windows allowing a root at the right edge, and one outer root. -/
noncomputable section
namespace LongCycleBounds.DescentBoundary
open Finset Polynomial Filter

/-- The sign of the leading term gives a root to the left of a point of opposite sign. -/
theorem root_left_of_leading_sign {p : ℝ[X]} {a : ℝ} (lead : 0 < p.leadingCoeff)
    (sign : (-1:ℝ)^p.natDegree * p.eval a < 0) :
    ∃ x, x < a ∧ p.eval x = 0 := by
  have eventuallyFlip : ∀ᶠ x in atBot, p.eval x * p.eval a < 0 := by
    rcases p.natDegree.even_or_odd with parity | parity
    · rw [parity.neg_one_pow, one_mul] at sign
      have positive := p.isEquivalent_atBot_lead.eventually_pos
        ((eventually_lt_atBot (0:ℝ)).mono fun x hx ↦ mul_pos lead (parity.pow_pos hx.ne))
      exact positive.mono fun _ h ↦ mul_neg_of_pos_of_neg h sign
    · rw [parity.neg_one_pow, neg_one_mul, neg_lt_zero] at sign
      have negative := p.isEquivalent_atBot_lead.eventually_neg
        ((eventually_lt_atBot (0:ℝ)).mono fun x hx ↦ mul_neg_of_pos_of_neg lead (parity.pow_neg hx))
      exact negative.mono fun _ h ↦ mul_neg_of_neg_of_pos h sign
  obtain ⟨z, hza, flip⟩ := ((eventually_lt_atBot a).and eventuallyFlip).exists
  obtain ⟨x, _, hxa, hx⟩ := LongCycleFinite.root_between p hza flip
  exact ⟨x, hxa, hx⟩

theorem simple_nonpositive_of_witnesses {p : ℝ[X]} (hp : p ≠ 0) (s : Finset ℝ)
    (cap : p.natDegree ≤ s.card) (zeros : ∀ x ∈ s, p.eval x = 0)
    (nonpos : ∀ x ∈ s, x ≤ 0) :
    p.Splits ∧ p.roots.Nodup ∧ ∀ x ∈ p.roots, x ≤ 0 := by
  have equal := roots_eq_of_natDegree_le_card_of_ne_zero (S := s) zeros cap hp
  have cards : p.roots.card = s.card := congrArg Multiset.card equal
  exact ⟨splits_iff_card_roots.mpr (le_antisymm p.card_roots' (cap.trans_eq cards.symm)),
    equal ▸ s.nodup, fun x hx ↦ nonpos x (by rwa [equal] at hx)⟩

/-- Intervals (aᵢ,bᵢ] may share endpoints. A zero at the right endpoint counts only once. -/
theorem simple_nonpositive_from_windows {d : ℕ} {p : ℝ[X]} (hp : p ≠ 0)
    (a b : Fin d → ℝ) (lt : ∀ i, a i < b i) (right : ∀ i, b i ≤ 0)
    (sep : ∀ i j, i < j → b i ≤ a j) (leftNZ : ∀ i, p.eval (a i) ≠ 0)
    (flip : ∀ i, p.eval (a i) * p.eval (b i) ≤ 0)
    (degree : p.natDegree ≤ d ∨
      (p.natDegree ≤ d+1 ∧ ∃ x, x ≤ 0 ∧ (∀ i, x ≤ a i) ∧ p.eval x = 0)) :
    p.Splits ∧ p.roots.Nodup ∧ ∀ x ∈ p.roots, x ≤ 0 := by
  classical
  have bracket (i : Fin d) : ∃ x, a i < x ∧ x ≤ b i ∧ p.eval x = 0 := by
    by_cases z : p.eval (b i) = 0
    · exact ⟨b i,lt i,le_rfl,z⟩
    · obtain ⟨x,h,l,e⟩ := LongCycleFinite.root_between p (lt i)
        (lt_of_le_of_ne (flip i) (mul_ne_zero (leftNZ i) z))
      exact ⟨x,h,l.le,e⟩
  choose r located using bracket
  have sorted : StrictMono r := fun i j lt ↦
    ((located i).2.1.trans (sep i j lt)).trans_lt (located j).1
  let s := (univ : Finset (Fin d)).map ⟨r, sorted.injective⟩
  have size : s.card = d := by simp [s]
  have members {x} (h : x ∈ s) : ∃ i, r i = x := by
    obtain ⟨i,_,hi⟩ := mem_map.mp h
    exact ⟨i,hi⟩
  have roots (x) (hx : x ∈ s) : p.eval x = 0 := by
    obtain ⟨i,rfl⟩ := members hx
    exact (located i).2.2
  have nonpos (x) (hx : x ∈ s) : x ≤ 0 := by
    obtain ⟨i,rfl⟩ := members hx
    exact (located i).2.1.trans (right i)
  rcases degree with cap | ⟨cap, x, xn, outer, ex⟩
  · exact simple_nonpositive_of_witnesses hp s (cap.trans_eq size.symm) roots nonpos
  · have newPoint : x ∉ s := by
      intro h
      obtain ⟨i,eq⟩ := members h
      exact (not_lt_of_ge (outer i)) (eq ▸ (located i).1)
    apply simple_nonpositive_of_witnesses hp (insert x s)
    · simpa [newPoint, size] using cap
    · exact (forall_mem_insert _ _ _).mpr ⟨ex, roots⟩
    · exact (forall_mem_insert _ _ _).mpr ⟨xn, nonpos⟩

/-- A zero highest coefficient lowers the degree; a positive one supplies the far-left root. -/
theorem simple_nonpositive_from_leading_window {d : ℕ} {p : ℝ[X]} (a b : Fin d → ℝ)
    (lt : ∀ i, a i < b i) (right : ∀ i, b i ≤ 0) (sep : ∀ i j, i < j → b i ≤ a j)
    (leftNZ : ∀ i, p.eval (a i) ≠ 0) (flip : ∀ i, p.eval (a i) * p.eval (b i) ≤ 0)
    (first : Fin d) (minLeft : ∀ i, a first ≤ a i)
    (farSign : (-1:ℝ)^(d+1) * p.eval (a first) < 0)
    (cap : p.natDegree ≤ d+1) (top : 0 ≤ p.coeff (d+1)) :
    p.Splits ∧ p.roots.Nodup ∧ ∀ x ∈ p.roots, x ≤ 0 := by
  have hp : p ≠ 0 := by intro h; exact leftNZ first (by simp [h])
  apply simple_nonpositive_from_windows hp a b lt right sep leftNZ flip
  by_cases small : p.natDegree ≤ d
  · exact Or.inl small
  · have eq : p.natDegree = d+1 := by omega
    have lead : 0 < p.leadingCoeff := lt_of_le_of_ne (by rwa [leadingCoeff, eq])
      (Ne.symm (leadingCoeff_ne_zero.mpr hp))
    obtain ⟨x, hx, ex⟩ := root_left_of_leading_sign lead (by rwa [eq])
    exact Or.inr ⟨cap, x, (hx.trans (lt first)).le.trans (right first),
      fun i ↦ hx.le.trans (minLeft i), ex⟩

#print axioms simple_nonpositive_from_leading_window
#print axioms root_left_of_leading_sign
#print axioms simple_nonpositive_from_windows
end LongCycleBounds.DescentBoundary

