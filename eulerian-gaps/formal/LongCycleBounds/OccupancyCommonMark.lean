import LongCycleBounds.OccupancyVerified

/-! One-ball coupling on the literal weighted slot-permutation sample space. -/
noncomputable section
namespace LongCycleBounds.Occupancy
open Equiv Finset FixedCycleCount
open scoped Classical

/-- A slot orbit contributes zero below two balls, the common mark below the cutoff, and one above. -/
def loadMark (k : ℕ) (u : ℝ) (a : ℕ) : ℝ :=
  if a < 2 then 0 else if a < k then u else 1

/-- At cutoff two the two jumps coincide and have total size one. -/
theorem loadMark_succ_sub {k : ℕ} (hk : 2 ≤ k) (u : ℝ) (a : ℕ) :
    loadMark k u (a+1) - loadMark k u a =
      (if a+1=2 then u else 0) + (if a+1=k then 1-u else 0) := by
  unfold loadMark
  split_ifs <;> first | omega | ring

theorem loadMark_nonneg (k : ℕ) {u : ℝ} (hu : 0 ≤ u) (a : ℕ) : 0 ≤ loadMark k u a := by
  unfold loadMark
  split_ifs <;> positivity

/-- Actual sample weight using the complete set of slot orbits, including fixed slots. -/
def slotWeight {m n : ℕ} (k : ℕ) (u : ℝ) (σ : Perm (Fin m)) (b : Fin n → Fin m) : ℝ :=
  ∏ t : Tag σ, loadMark k u (counts (tag σ ∘ b) t)

/-- Contribution of all the other orbits when a slot s receives a new ball. -/
def outsideWeight {m n : ℕ} (k : ℕ) (u : ℝ) (σ : Perm (Fin m)) (b : Fin n → Fin m)
    (s : Fin m) : ℝ := ∏ t ∈ univ.erase (tag σ s), loadMark k u (counts (tag σ ∘ b) t)

private theorem counts_cons {m n : ℕ} (σ : Perm (Fin m)) (b : Fin n → Fin m)
    (s : Fin m) (t : Tag σ) :
    counts (tag σ ∘ Fin.cons s b) t = (if tag σ s=t then 1 else 0) + counts (tag σ ∘ b) t := by
  classical
  unfold counts
  simp only [card_eq_sum_ones,sum_filter]
  rw [Fin.sum_univ_succ]
  simp

/-- Pointwise equality retaining the other orbit factors even when one of them vanishes. -/
theorem slotWeight_cons_sub {m n k : ℕ} (hk : 2 ≤ k) (u : ℝ) (σ : Perm (Fin m))
    (b : Fin n → Fin m) (s : Fin m) :
    let a := counts (tag σ ∘ b) (tag σ s) + 1
    slotWeight k u σ (Fin.cons s b) - slotWeight k u σ b =
      ((if a=2 then u else 0)+(if a=k then 1-u else 0))*outsideWeight k u σ b s := by
  classical
  let z := tag σ s
  let f := fun t ↦ loadMark k u (counts (tag σ ∘ b) t)
  let g := fun t ↦ loadMark k u (counts (tag σ ∘ Fin.cons s b) t)
  have other : (∏ t ∈ univ.erase z, g t) = ∏ t ∈ univ.erase z, f t := by
    apply prod_congr rfl
    intro t ht
    dsimp only [g,f]
    rw [counts_cons,if_neg (Ne.symm (mem_erase.mp ht).1),zero_add]
  have first : g z - f z = (if counts (tag σ ∘ b) z+1=2 then u else 0)+
      (if counts (tag σ ∘ b) z+1=k then 1-u else 0) := by
    dsimp only [g,f]
    rw [counts_cons,if_pos (rfl : tag σ s=z),add_comm (1:ℕ)]
    exact loadMark_succ_sub hk u _
  change (∏ t, g t)-(∏ t, f t)=_*_
  rw [←mul_prod_erase univ g (mem_univ z),←mul_prod_erase univ f (mem_univ z),
    other,←sub_mul,first]
  rfl

theorem slotWeight_cons_mono {m n k : ℕ} (hk : 2 ≤ k) {u : ℝ} (hu : u ∈ Set.Icc (0:ℝ) 1)
    (σ : Perm (Fin m)) (b : Fin n → Fin m) (s : Fin m) :
    slotWeight k u σ b ≤ slotWeight k u σ (Fin.cons s b) := by
  apply sub_nonneg.mp
  rw [slotWeight_cons_sub hk]
  apply mul_nonneg (add_nonneg (by split_ifs <;> linarith [hu.1])
      (by split_ifs <;> linarith [hu.2]))
  exact prod_nonneg fun _ _ ↦ loadMark_nonneg _ hu.1 _

/-- Mean sample weight when the permutation and each ball-to-slot map are independently uniform. -/
def markedSlotProbability (n k m : ℕ) (u : ℝ) : ℝ :=
  (∑ σ : Perm (Fin m), ∑ b : Fin n → Fin m, slotWeight k u σ b) / ((m.factorial:ℝ)*(m:ℝ)^n)

/-- Mean contribution, at a prescribed landing load, among n old balls and one free landing slot. -/
def landingMass (n k m a : ℕ) (u : ℝ) : ℝ :=
  (∑ σ : Perm (Fin m), ∑ s : Fin m, ∑ b : Fin n → Fin m,
    if counts (tag σ ∘ b) (tag σ s)+1=a then outsideWeight k u σ b s else 0) /
    ((m.factorial:ℝ)*(m:ℝ)^(n+1))

theorem landingMass_nonneg (n k m a : ℕ) {u : ℝ} (hu : 0 ≤ u) : 0 ≤ landingMass n k m a u := by
  unfold landingMass
  apply div_nonneg _ (by positivity)
  apply sum_nonneg; intro σ _
  apply sum_nonneg; intro s _
  apply sum_nonneg; intro b _
  split_ifs
  · exact prod_nonneg fun _ _ ↦ loadMark_nonneg _ hu _
  · rfl

/-- The exact adjacent-ball difference of the finite uniform means, for every real mark. -/
theorem markedSlotProbability_succ_sub {m k : ℕ} (hm : 0 < m) (hk : 2 ≤ k) (n : ℕ) (u : ℝ) :
    markedSlotProbability (n+1) k m u - markedSlotProbability n k m u =
      u*landingMass n k m 2 u + (1-u)*landingMass n k m k u := by
  classical
  let F := fun (σ : Perm (Fin m)) (s : Fin m) (b : Fin n → Fin m) ↦ slotWeight k u σ (Fin.cons s b)
  have succ (σ : Perm (Fin m)) : (∑ b : Fin (n+1) → Fin m, slotWeight k u σ b) =
      ∑ s : Fin m, ∑ b : Fin n → Fin m, F σ s b := by
    have h := (Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n+1) ↦ Fin m)) (slotWeight k u σ)).symm
    rw [Fintype.sum_prod_type] at h
    exact h
  have old : markedSlotProbability n k m u =
      (∑ σ : Perm (Fin m), ∑ _ : Fin m, ∑ b : Fin n → Fin m, slotWeight k u σ b) /
        ((m.factorial:ℝ)*(m:ℝ)^(n+1)) := by
    simp only [markedSlotProbability, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
      ←mul_sum, pow_succ]
    have mp : (m:ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    field_simp
  rw [old,markedSlotProbability]
  simp only [succ,landingMass,←sub_div,←mul_div_assoc,←add_div]
  congr 1
  simp only [mul_sum,←sum_add_distrib,←sum_sub_distrib]
  apply sum_congr rfl; intro σ _
  apply sum_congr rfl; intro s _
  apply sum_congr rfl; intro b _
  change slotWeight k u σ (Fin.cons s b) - slotWeight k u σ b = _
  rw [slotWeight_cons_sub hk]
  split_ifs <;> ring

theorem markedSlotProbability_mono {m k : ℕ} (hm : 0 < m) (hk : 2 ≤ k)
    {u : ℝ} (hu : u ∈ Set.Icc (0:ℝ) 1) (n : ℕ) :
    markedSlotProbability n k m u ≤ markedSlotProbability (n+1) k m u := by
  apply sub_nonneg.mp
  rw [markedSlotProbability_succ_sub hm hk]
  exact add_nonneg (mul_nonneg hu.1 (landingMass_nonneg _ _ _ _ hu.1))
    (mul_nonneg (sub_nonneg.mpr hu.2) (landingMass_nonneg _ _ _ _ hu.1))

/-- Group actual assignments by the entire vector of orbit loads, for arbitrary real marks. -/
theorem marked_slot_histogram {m n : ℕ} (k : ℕ) (u : ℝ) (σ : Perm (Fin m)) :
    (∑ b : Fin n → Fin m, slotWeight k u σ b) =
      ∑ a ∈ piAntidiag (univ : Finset (Tag σ)) n,
        ((Nat.multinomial univ a * ∏ t, (counts (tag σ) t)^(a t) : ℕ):ℝ) *
          ∏ t, loadMark k u (a t) := by
  classical
  let f (b : Fin n → Fin m) := counts (tag σ ∘ b)
  have valid (b : Fin n → Fin m) (_ : b ∈ univ) : f b ∈ piAntidiag univ n := by
    apply mem_piAntidiag.mpr
    exact ⟨by simpa only [f,Fintype.card_fin] using sum_counts (tag σ ∘ b), fun _ _ ↦ mem_univ _⟩
  rw [←sum_fiberwise_of_maps_to valid]
  apply sum_congr rfl
  intro a ha
  have eq (b : Fin n → Fin m) (hb : b ∈ univ.filter (fun b ↦ f b=a)) :
      slotWeight k u σ b = ∏ t, loadMark k u (a t) := by
    change (∏ t, loadMark k u (f b t)) = _
    rw [(mem_filter.mp hb).2]
  rw [sum_congr rfl eq,sum_const,nsmul_eq_mul]
  congr 2
  exact card_placements_profile n (tag σ) a (mem_piAntidiag.mp ha).1

private theorem slot_mean_indicator (n k m : ℕ) :
    ((∑ σ : Perm (Fin m), ∑ b : Fin n → Fin m, (if AllHit k σ b then 1 else 0 : ℝ)) /
      ((m.factorial:ℝ)*(m:ℝ)^n)) = (literalProbability n k m:ℝ) := by
  unfold literalProbability jointSuccesses
  push_cast
  rw [card_eq_sum_ones,sum_filter,Fintype.sum_prod_type]
  push_cast
  simp

/-- At zero mark the literal sample average gives the genuine hard-cutoff coefficient. -/
theorem markedSlotProbability_zero {k : ℕ} (hk : 2 ≤ k) (n m : ℕ) :
    markedSlotProbability n k m 0 = (literalProbability n k m:ℝ) := by
  classical
  unfold markedSlotProbability
  convert! slot_mean_indicator n k m using 3 with σ
  apply sum_congr rfl
  intro b _
  have mark (a : ℕ) : loadMark k 0 a = if k≤a then 1 else 0 := by
    unfold loadMark
    split_ifs <;> first | rfl | omega
  simp only [slotWeight,mark,Fintype.prod_boole,allHit_iff]

/-- At unit mark the literal sample average gives the genuine derangement coefficient. -/
theorem markedSlotProbability_one (n k m : ℕ) :
    markedSlotProbability n k m 1 = (literalProbability n 2 m:ℝ) := by
  classical
  unfold markedSlotProbability
  convert! slot_mean_indicator n 2 m using 3 with σ
  apply sum_congr rfl
  intro b _
  have mark (a : ℕ) : loadMark k 1 a = if 2≤a then 1 else 0 := by
    unfold loadMark
    split_ifs <;> first | rfl | omega
  simp only [slotWeight,mark,Fintype.prod_boole,allHit_iff]

theorem original_eq_markedSlot_zero {m k : ℕ} (hk : 2 ≤ k) (hm : 0 < m) (n : ℕ) :
    originalLabelCoeff n k m = (m:ℝ)^n * markedSlotProbability n k m 0 := by
  rw [markedSlotProbability_zero hk,original_eq_slot_probability hk hm]
  push_cast
  rfl

theorem derangement_eq_markedSlot_one {m : ℕ} (hm : 0 < m) (n k : ℕ) :
    originalLabelCoeff n 2 m = (m:ℝ)^n * markedSlotProbability n k m 1 := by
  rw [markedSlotProbability_one,original_eq_slot_probability (by decide : 2≤2) hm]
  push_cast
  rfl

#print axioms slotWeight_cons_sub
#print axioms markedSlotProbability_succ_sub
#print axioms markedSlotProbability_mono
#print axioms marked_slot_histogram
#print axioms original_eq_markedSlot_zero
#print axioms derangement_eq_markedSlot_one
end LongCycleBounds.Occupancy
