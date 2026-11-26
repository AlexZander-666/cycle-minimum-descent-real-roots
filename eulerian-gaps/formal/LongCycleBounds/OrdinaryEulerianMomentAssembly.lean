import LongCycleBounds.OrdinaryEulerianLabelSummable
import LongCycleBounds.OrdinaryEulerianHalfAxis

noncomputable section
namespace LongCycleBounds.OrdinaryEulerianGap
open LongCycleFinite DescentMesh DescentNecklace Real Outer LongCycles

/-- Discharge every original-row input to the exterior moment comparison. -/
theorem original_large_of_alignment {n k : ℕ} (hn : 128≤n) (hk : 3≤k) (kn : k≤n)
    (align : ∀ {p : ℕ}, 72≤p → ∀ {x : ℝ}, 0<x → 5*sqrt p/2≤x → ∀ G : ℕ→ℝ,
      (∀ j : ℕ, 1/2≤G (j+1)-G j ∧ G (j+1)-G j≤3 ∧
        (2≤j → 119/144≤G (j+1)-G j ∧ G (j+1)-G j≤169/144)) →
      (∀ i j : ℕ, |G i-G j|≤3*|(i:ℝ)-j|) →
      Summable (fun i : ℕ ↦ (-1:ℝ)^i*weight p x i*G i) →
      Summable (fun i : ℕ ↦ (-1:ℝ)^i*weight p x i*((i:ℝ)+1)) →
      moment p x=0 →
      0<(∑' i : ℕ,(-1:ℝ)^i*weight p x i*G i)*(∑' i : ℕ,(-1:ℝ)^i*weight p x i*((i:ℝ)+1))) :
    StrictNegativeInterlacing (EulerianBrackets.originalQuotient n k) (eulerian (n-1)) (n-3) := by
  apply original_large_of_exterior hn hk kn
  intro a choice x reg zero
  have n1 : 1≤n := by omega
  have reg' : 5*sqrt ((n-1:ℕ):ℝ)/2≤x := by
    rw [Nat.cast_sub n1,Nat.cast_one]; linarith only [reg]
  have rp : 0 < sqrt ((n-1:ℕ):ℝ) := sqrt_pos.mpr (by exact_mod_cast (by omega : 0<n-1))
  have xp : 0<x := by linarith only [rp,reg']
  obtain ⟨_,_,budget⟩ := actual_label_inputs hn hk kn choice
  have ap : 0<a n := (show 0≤lossNorm n a (4/5) from Finset.sum_nonneg fun _ _ ↦ by positivity).trans_lt budget
  obtain ⟨lip,sm,smQ⟩ := actual_label_exterior_inputs hn hk kn choice xp
  obtain ⟨_,steps⟩ := actual_label_steps hn hk kn choice
  let G := fun i : ℕ ↦ labelG n a (i+1)
  have inc (j : ℕ) : 1/2≤G (j+1)-G j ∧ G (j+1)-G j≤3 ∧
      (2≤j → 119/144≤G (j+1)-G j ∧ G (j+1)-G j≤169/144) := by
    have e := steps (j+1) (by omega)
    exact ⟨e.1,e.2.1,fun jj ↦ e.2.2.2 (by omega)⟩
  have sgn := align (p:=n-1) (by omega) xp reg' G inc lip sm smQ (original_zero_to_cancellation xp zero)
  apply sign_of_weighted_moments n1 a ap xp
  simpa only [weightedMoment,Nat.cast_succ,G] using sgn

#print axioms original_large_of_alignment
end LongCycleBounds.OrdinaryEulerianGap
