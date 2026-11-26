import LongCycleBounds.OccupancyOrbitRemoval

/-! Exact equality between marked label coefficients and the uniform slot experiment. -/
noncomputable section
namespace LongCycleBounds.Occupancy
open Finset PowerSeries CycleProfile Equiv
open scoped Classical

/-- Residual mass with the ball factorial restored, including the empty arrangement. -/
def markedOrbitCount (k : ℕ) (u : ℝ) (n m : ℕ) : ℝ :=
  (n.factorial:ℝ)*coeff n (slotIndexSeries k u m)

theorem markedOrbitCount_seed (k : ℕ) (u : ℝ) (m : ℕ) :
    markedOrbitCount k u 0 m = if m=0 then 1 else 0 := by
  cases m with
  | zero => simp [markedOrbitCount,slotIndexSeries,coeff_one]
  | succ m =>
    unfold markedOrbitCount
    rw [←markedSlot_as_cycleIndex (by omega)]
    have sample (σ : Perm (Fin (m+1))) (b : Fin 0 → Fin (m+1)) : slotWeight k u σ b=0 := by
      unfold slotWeight
      apply prod_eq_zero (mem_univ (tag σ 0))
      simp [counts,loadMark]
    simp [markedSlotProbability,sample]

/-- Deleting the orbit of a distinguished ball gives the anchored finite convolution,
with all its slot orderings and ball assignments counted at their actual weights. -/
theorem markedOrbitCount_remove (n m k : ℕ) (u : ℝ) :
    markedOrbitCount k u (n+1) m =
      ∑ d ∈ range (n+1), if d=0 then 0 else
        (n.choose d:ℝ)*profile k u (d+1)*
          ∑ l ∈ range (m+1), (l:ℝ)^d*markedOrbitCount k u (n-d) (m-l) := by
  have eq := congrArg (coeff n) (remove_marked_orbit k m u)
  rw [coeff_derivative,map_sum] at eq
  simp_rw [coeff_mul,Nat.sum_antidiagonal_eq_sum_range_succ_mk] at eq
  rw [sum_comm] at eq
  unfold markedOrbitCount
  rw [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,
    show ∀ c:ℝ,((n:ℝ)+1)*n.factorial*c=n.factorial*(c*((n:ℝ)+1)) by intro;ring,eq,mul_sum]
  apply sum_congr rfl
  intro d hd
  have le : d ≤ n := by simpa using hd
  simp_rw [coeff_removed_orbit]
  by_cases dz : d=0
  · simp [dz]
  rw [if_neg dz,mul_sum,mul_sum]
  apply sum_congr rfl
  intro l _
  rw [if_neg dz]
  have comb : (n.choose d:ℝ)*d.factorial*(n-d).factorial=n.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial le
  rw [←comb]
  have dn : (d.factorial:ℝ)≠0 := by positivity
  field_simp

/-- For every real common mark, even a signed one, the genuine coefficient is the
orbit-weight expectation multiplied by m^n. -/
theorem original_profile_eq_slot_probability {m : ℕ} (hm : 0 < m) (n k : ℕ) (u : ℝ) :
    anchoredLabel (profile k u) n m = (m:ℝ)^n*markedSlotProbability n k m u := by
  rw [markedSlot_as_cycleIndex hm]
  exact (equals_anchoredLabel_of_split (profile k u) (markedOrbitCount k u)
    (markedOrbitCount_seed k u) (fun n m ↦ markedOrbitCount_remove n m k u) n m).symm

private theorem markedSlot_empty_empty (k : ℕ) (u : ℝ) : markedSlotProbability 0 k 0 u=1 := by
  have hs (σ : Perm (Fin 0)) (b : Fin 0 → Fin 0) : slotWeight k u σ b=1 := by
    have no (t : Tag σ) : False := by
      cases t with
      | inl i => exact Fin.elim0 i.val
      | inr v =>
        rcases v with ⟨v,hv⟩
        rw [Subsingleton.elim σ 1,Perm.cycleFactorsFinset_one] at hv
        exact notMem_empty _ hv
    let _ : IsEmpty (Tag σ) := ⟨no⟩
    simp [slotWeight]
  simp [markedSlotProbability,hs]

/-- The empty sample has weight one, and every nonempty ball set gives label zero at zero slots. -/
theorem original_profile_eq_slot_probability_all (n k m : ℕ) (u : ℝ) :
    anchoredLabel (profile k u) n m = (m:ℝ)^n * markedSlotProbability n k m u := by
  cases m with
  | succ m => exact original_profile_eq_slot_probability (by omega) n k u
  | zero =>
    rw [anchoredLabel_no_slots]
    by_cases hn : n=0
    · simp [hn,markedSlot_empty_empty]
    · simp [hn]

/-- Complete marked positive-label series of the original normalized row. Label zero
vanishes in every nonempty row, so sampling only positive slot counts suffices. -/
theorem normalized_profile_hasSum_slots (n : ℕ) {x : ℝ} (hx : 0 < x) (k : ℕ) (u : ℝ) :
    HasSum (fun m : ℕ ↦ (-Real.exp (-x))^m*((m:ℝ)^n*markedSlotProbability n k m u))
      (normalizedRow (profile k u) n x) := by
  apply (normalized_profile_hasSum hx n k u).congr_fun
  intro m
  rw [original_profile_eq_slot_probability_all]

/-- The forward two-jump law applies directly to normalized coefficients of the true marked rows. -/
theorem original_profile_adjacent_slot_change {m k : ℕ} (hm : 0 < m) (hk : 2 ≤ k)
    (n : ℕ) (u : ℝ) :
    anchoredLabel (profile k u) (n+1) m/(m:ℝ)^(n+1) -
      anchoredLabel (profile k u) n m/(m:ℝ)^n =
        u*landingMass n k m 2 u + (1-u)*landingMass n k m k u := by
  have e := markedSlotProbability_succ_sub hm hk n u
  rw [original_profile_eq_slot_probability hm,original_profile_eq_slot_probability hm]
  have mp : (m:ℝ)≠0 := by exact_mod_cast hm.ne'
  simpa [mul_div_cancel_left₀,mp] using e

#print axioms markedOrbitCount_remove
#print axioms original_profile_eq_slot_probability
#print axioms original_profile_eq_slot_probability_all
#print axioms normalized_profile_hasSum_slots
#print axioms original_profile_adjacent_slot_change
end LongCycleBounds.Occupancy
