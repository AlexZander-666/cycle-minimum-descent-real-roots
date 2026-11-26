import LongCycleBounds.OccupancyMarkedIndex

/-! The ball exponential series for each actual slot cycle, and its ordered cycle index. -/
noncomputable section
namespace LongCycleBounds.Occupancy
open Finset Equiv PowerSeries
open scoped Classical

/-- A complete homogeneous product coefficient indexed by ordinary finite functions. -/
theorem coeff_product_histogram {R I : Type*} [CommSemiring R] [Fintype I] [DecidableEq I]
    (n : ℕ) (f : I → PowerSeries R) :
    coeff n (∏ i, f i) = ∑ a ∈ piAntidiag univ n, ∏ i, coeff (a i) (f i) := by
  classical
  rw [coeff_prod]
  let e : (I →₀ ℕ) ≃ (I → ℕ) := Finsupp.equivFunOnFinite
  refine sum_nbij' e e.symm ?_ ?_ (fun a _ ↦ e.symm_apply_apply a) (fun a _ ↦ e.apply_symm_apply a) ?_
  · intro a ha
    exact mem_piAntidiag.mpr ⟨(mem_finsuppAntidiag.mp ha).1,fun _ _ ↦ mem_univ _⟩
  · intro a ha
    refine mem_finsuppAntidiag.mpr ⟨?_,subset_univ _⟩
    have eq : (⇑(e.symm a))=a := e.apply_symm_apply a
    rw [eq]
    exact (mem_piAntidiag.mp ha).1
  · intros; rfl

/-- Ball EGF on a specified orbit with l distinguishable slots. -/
def orbitBallSeries (k : ℕ) (u : ℝ) (l : ℕ) : PowerSeries ℝ :=
  mk (fun a ↦ loadMark k u a*(l:ℝ)^a/a.factorial)

/-- Literal assignments for a fixed permutation of slots are counted by its orbit series. -/
theorem weightedAssignments_eq_orbitSeries {m : ℕ} (k n : ℕ) (u : ℝ) (σ : Perm (Fin m)) :
    (∑ b : Fin n → Fin m, slotWeight k u σ b) =
      (n.factorial:ℝ)*coeff n (∏ i : Tag σ, orbitBallSeries k u (counts (tag σ) i)) := by
  rw [marked_slot_histogram,coeff_product_histogram,mul_sum]
  apply sum_congr rfl
  intro a ha
  have spec : ((∏ t, ((a t).factorial:ℝ))*(Nat.multinomial univ a:ℝ))=n.factorial := by
    exact_mod_cast (mem_piAntidiag.mp ha).1 ▸ Nat.multinomial_spec univ a
  simp only [orbitBallSeries,coeff_mk,prod_div_distrib,prod_mul_distrib,Nat.cast_mul,Nat.cast_prod,Nat.cast_pow]
  have nz : (∏ t, ((a t).factorial:ℝ))≠0 := (prod_pos fun _ _ ↦ by positivity).ne'
  rw [←spec]
  field_simp

/-- Slot-size ordinary series with power-series-valued coefficients. The zero slot term vanishes. -/
def orbitSeries (k : ℕ) (u : ℝ) : PowerSeries (PowerSeries ℝ) :=
  mk fun l ↦ C (1/(l:ℝ))*orbitBallSeries k u l

/-- Finite exponential at fixed slot total; an admissible slot tuple has at most m parts. -/
def slotIndexSeries (k : ℕ) (u : ℝ) (m : ℕ) : PowerSeries ℝ :=
  ∑ h ∈ range (m+1), C (1/(h.factorial:ℝ))*coeff m ((orbitSeries k u)^h)

theorem coeff_orbitSeries_pow (k m h : ℕ) (u : ℝ) :
    coeff m ((orbitSeries k u)^h) =
      ∑ l ∈ goodLengths h m, C (1/(∏ i, (l i:ℝ)))*∏ i, orbitBallSeries k u (l i) := by
  classical
  have prod (l : Fin h → ℕ) : (∏ i, coeff (l i) (orbitSeries k u)) =
      C (1/(∏ i, (l i:ℝ)))*∏ i, orbitBallSeries k u (l i) := by
    simp only [orbitSeries,coeff_mk,prod_mul_distrib,←map_prod,one_div,prod_inv_distrib]
  have eq := coeff_product_histogram m (fun _ : Fin h ↦ orbitSeries k u)
  simp only [prod_const,card_univ,Fintype.card_fin,prod] at eq
  rw [eq,goodLengths,sum_filter]
  apply sum_congr rfl
  intro l _
  split_ifs with pos
  · rfl
  · obtain ⟨i,hi⟩ := not_forall.mp pos
    have zero : l i=0 := by omega
    rw [prod_eq_zero (mem_univ i) (by simp [zero])]
    simp

/-- The actual normalized slot expectation, with the ball factorial separated for differentiation. -/
theorem markedSlot_as_cycleIndex {m : ℕ} (hm : 0 < m) (n k : ℕ) (u : ℝ) :
    (m:ℝ)^n*markedSlotProbability n k m u =
      (n.factorial:ℝ)*coeff n (slotIndexSeries k u m) := by
  classical
  let V (b : Multiset ℕ) := (n.factorial:ℝ)*coeff n ((b.map (orbitBallSeries k u)).prod)
  have sample (σ : Perm (Fin m)) : (∑ b : Fin n → Fin m, slotWeight k u σ b) = V σ.partition.parts := by
    rw [weightedAssignments_eq_orbitSeries,←bagF_tag σ]
    simp only [V,bagF,Multiset.map_map,Function.comp_def,Finset.prod]
  have mp : (m:ℝ)^n≠0 := by positivity
  rw [markedSlotProbability,show ∀ z:ℝ,(m:ℝ)^n*(z/((m.factorial:ℝ)*m^n))=z/m.factorial by
    intro z; field_simp]
  simp_rw [sample]
  rw [complete_slot_cycle_index hm,slotIndexSeries,map_sum,mul_sum]
  apply sum_congr rfl; intro h _
  rw [coeff_orbitSeries_pow, mul_sum, map_sum, mul_sum]
  apply sum_congr rfl; intro l _
  simp only [coeff_C_mul]
  dsimp only [V,bag]
  simp only [Multiset.map_map,Function.comp_def,Finset.prod]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

#print axioms weightedAssignments_eq_orbitSeries
#print axioms markedSlot_as_cycleIndex
end LongCycleBounds.Occupancy
