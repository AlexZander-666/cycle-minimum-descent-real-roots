import LongCycleBounds.DescentBoundarySmallRoots

/-! The only repeated-root mixtures at four and five letters, for arbitrary admissible weights. -/
noncomputable section
namespace LongCycleBounds.DescentBoundary
open Finset Polynomial

private theorem scaled_double {a t : ℝ} (ha : 0 < a) :
    let p : ℝ[X] := C a * (X*(X-C t)^2)
    p.Splits ∧ p.roots = ({0}:Multiset ℝ) + 2 • ({t}:Multiset ℝ) := by
  dsimp only
  refine ⟨(Splits.C _).mul (Splits.X.mul ((Splits.X_sub_C t).pow 2)), ?_⟩
  have nz : (X:ℝ[X])*(X-C t)^2 ≠ 0 := mul_ne_zero X_ne_zero (pow_ne_zero _ (X_sub_C_ne_zero _))
  rw [roots_C_mul _ ha.ne', roots_mul nz, roots_X, roots_pow, roots_X_sub_C]

private theorem exceptional_properties {p : ℝ[X]} {t : ℝ} (ht : t < 0)
    (hr : p.roots = ({0}:Multiset ℝ) + 2 • ({t}:Multiset ℝ)) :
    ¬ p.roots.Nodup ∧ (∀ x ∈ p.roots, x ≤ 0) ∧ p.rootMultiplicity t = 2 := by
  have distinct := ht.ne
  rw [← count_roots, hr]
  constructor
  · simp [two_nsmul]
  constructor
  · intro x hx
    simp [two_nsmul] at hx
    rcases hx with h | h
    · grind
    · grind
  · simp [two_nsmul, distinct, distinct.symm]

theorem four_exception (w : ℕ → ℝ) (hw : ∀ k ∈ Icc 1 4, 0 ≤ w k)
    (pos : ∃ k ∈ Icc 1 4, 0 < w k) (support : w 1 + (w 3+w 4) = 0) :
    (mixture 4 w).Splits ∧ (mixture 4 w).roots = ({0}:Multiset ℝ) + 2 • ({-2}:Multiset ℝ) := by
  have a := hw 1 (by decide)
  have c := hw 3 (by decide)
  have e := hw 4 (by decide)
  have za : w 1 = 0 := by linarith
  have zc : w 3 = 0 := by linarith
  have ze : w 4 = 0 := by linarith
  have hb : 0 < w 2 := by
    obtain ⟨k, hk, positive⟩ := pos
    obtain ⟨lo,hi⟩ := mem_Icc.mp hk
    interval_cases k <;> simp_all
  rw [four_mixture, za, zc, ze]
  simpa using scaled_double (t := -2) hb

theorem five_exception (w : ℕ → ℝ) (hw : ∀ k ∈ Icc 1 5, 0 ≤ w k)
    (pos : ∃ k ∈ Icc 1 5, 0 < w k) (support : w 1+w 2 = 0) :
    (mixture 5 w).Splits ∧ (mixture 5 w).roots = ({0}:Multiset ℝ) + 2 • ({-1}:Multiset ℝ) := by
  have a := hw 1 (by decide)
  have b := hw 2 (by decide)
  have c := hw 3 (by decide)
  have e := hw 4 (by decide)
  have f := hw 5 (by decide)
  have za : w 1 = 0 := by linarith
  have zb : w 2 = 0 := by linarith
  have hc : 0 < w 3+w 4+w 5 := by
    obtain ⟨k, hk, positive⟩ := pos
    obtain ⟨lo,hi⟩ := mem_Icc.mp hk
    interval_cases k <;> linarith
  have eq : mixture 5 w = C (6*(w 3+w 4+w 5)) * (X*(X-C (-1))^2) := by
    rw [five_mixture, za, zb]
    simp [map_mul, C_ofNat]
    ring
  rw [eq]
  exact scaled_double (by positivity)

theorem four_all_weights (w : ℕ → ℝ) (hw : ∀ k ∈ Icc 1 4, 0 ≤ w k)
    (pos : ∃ k ∈ Icc 1 4, 0 < w k) :
    let p := mixture 4 w
    p.Splits ∧ (∀ x ∈ p.roots, x ≤ 0) ∧ (p.roots.Nodup ↔ 0 < w 1 + (w 3+w 4)) ∧
      (w 1 + (w 3+w 4) = 0 → p.rootMultiplicity (-2) = 2) := by
  by_cases good : 0 < w 1 + (w 3+w 4)
  · obtain ⟨splits, simple, roots⟩ := four_simple w hw good
    exact ⟨splits, roots, iff_of_true simple good, fun eq ↦ (good.ne' eq).elim⟩
  · have zero := le_antisymm (le_of_not_gt good)
      (add_nonneg (hw 1 (by decide)) (add_nonneg (hw 3 (by decide)) (hw 4 (by decide))))
    obtain ⟨splits, hr⟩ := four_exception w hw pos zero
    obtain ⟨dup, roots, mult⟩ := exceptional_properties (by norm_num : (-2:ℝ)<0) hr
    exact ⟨splits, roots, iff_of_false dup good, fun _ ↦ mult⟩

theorem five_all_weights (w : ℕ → ℝ) (hw : ∀ k ∈ Icc 1 5, 0 ≤ w k)
    (pos : ∃ k ∈ Icc 1 5, 0 < w k) :
    let p := mixture 5 w
    p.Splits ∧ (∀ x ∈ p.roots, x ≤ 0) ∧ (p.roots.Nodup ↔ 0 < w 1+w 2) ∧
      (w 1+w 2 = 0 → p.rootMultiplicity (-1) = 2) := by
  by_cases good : 0 < w 1+w 2
  · obtain ⟨splits, simple, roots⟩ := five_simple w hw good
    exact ⟨splits, roots, iff_of_true simple good, fun eq ↦ (good.ne' eq).elim⟩
  · have zero := le_antisymm (le_of_not_gt good) (add_nonneg (hw 1 (by decide)) (hw 2 (by decide)))
    obtain ⟨splits, hr⟩ := five_exception w hw pos zero
    obtain ⟨dup, roots, mult⟩ := exceptional_properties (by norm_num : (-1:ℝ)<0) hr
    exact ⟨splits, roots, iff_of_false dup good, fun _ ↦ mult⟩

#print axioms four_all_weights
#print axioms five_all_weights
end LongCycleBounds.DescentBoundary

