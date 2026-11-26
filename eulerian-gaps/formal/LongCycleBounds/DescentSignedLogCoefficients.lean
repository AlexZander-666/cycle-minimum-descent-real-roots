import LongCycleBounds.DescentSignedKernel
import LongCycleBounds.DescentSignedBounds

noncomputable section
namespace LongCycleBounds.DescentMesh
open Finset Polynomial ArithmeticFunction
open scoped Moebius

private theorem atom_facts {k N B : ℕ} (hk : 3 ≤ k) (z : LogAtom k N B) :
    let h := atomLength z-atomLoss z
    0 < h ∧ h ∣ atomLength z ∧ 2*h ≤ atomLength z := by
  have jp : 0<z.1.val := by have := (mem_Icc.mp z.1.prop).1; omega
  have mem : atomDivisor z ∈ z.1.val.divisors := by
    rcases z with ⟨j,d|⟨b,d⟩⟩
    · exact (mem_erase.mp d.prop).2
    · exact d.prop
  have dvd := Nat.dvd_of_mem_divisors mem
  have dp := Nat.pos_of_mem_divisors mem
  have bp : 0<atomRepeat z := by
    rcases z with ⟨j,d|⟨b,d⟩⟩
    · exact Nat.zero_lt_one
    · exact lt_of_lt_of_le (by decide : 0 < 2) (mem_Icc.mp b.prop).1
  have ord : z.1.val/(atomDivisor z) ≤ atomLength z :=
    (Nat.div_le_self ..).trans (Nat.le_mul_of_pos_right _ bp)
  have eq : atomLength z-atomLoss z = z.1.val/(atomDivisor z) := Nat.sub_sub_self ord
  have le := (atom_loss hk z).2
  dsimp only
  refine ⟨eq ▸ Nat.div_pos (Nat.le_of_dvd jp dvd) dp, ?_,by omega⟩
  rw [eq]
  exact dvd_trans (Nat.div_dvd_of_dvd dvd) (dvd_mul_right ..)

private theorem badLog_off_grid {k H i h : ℕ} (hk : 3 ≤ k)
    (off : ¬(0 < h ∧ h∣i ∧ 2*h ≤ i)) :
    (((badLogPolynomial k H H).coeff i).coeff h) = 0 := by
  simp only [badLogPolynomial,finsetSum_coeff,biTerm,coeff_monomial]
  apply sum_eq_zero
  intro z _
  by_cases il : atomLength z=i
  · rw [if_pos il,coeff_monomial]
    apply if_neg
    intro eq
    apply off
    simpa only [←il,←eq] using atom_facts hk z
  · simp [il]

/-- Every positive-length coefficient at or below the horizon, including nondivisors,
the principal diagonal and all alphabet degrees at least k. -/
theorem signed_log_coefficient {k H i h : ℕ} (hk : 3 ≤ k) (hi : 0 < i) (cut : i ≤ H) :
    (((badLogPolynomial k H H).coeff i).coeff h) =
       if h∈i.divisors ∧ h<k ∧ h < i then (SignedBounds.signedSum k h (i/h) : ℝ)/(i:ℝ) else 0 := by
  classical
  by_cases good : 0<h ∧ h∣i ∧ 2*h ≤ i
  · obtain ⟨hh,dv,hl⟩ := good
    have eq := Nat.mul_div_cancel' dv
    have quot : 1 < i/h := by
      by_contra! bad
      have := Nat.mul_le_mul_left h bad
      omega
    have hrow := badLog_collected (k:=k) (H:=H) hk hh quot (by simpa only [eq] using cut)
    rw [eq] at hrow
    by_cases low : h<k
    · rw [if_pos ⟨Nat.mem_divisors.mpr ⟨dv,hi.ne'⟩,low,by omega⟩,eq_div_iff (by positivity)]
      rw [mul_comm]
      simpa [SignedBounds.signedSum] using hrow
    · rw [if_neg (fun a ↦ low a.2.1)]
      have z := rawKernel_cancels (k:=k) (H:=H) (h:=h) (l:=i/h) (by omega) (by omega) quot
        (by simpa only [eq] using cut)
      rw [rawKernel_collected (by omega) hh (by omega) (by simpa only [eq] using cut)] at z
      rw [z] at hrow
      exact (mul_eq_zero.mp hrow).resolve_left (by positivity)
  · rw [badLog_off_grid hk good,if_neg]
    rintro ⟨mem,_,lt⟩
    have dv := Nat.dvd_of_mem_divisors mem
    have hh := Nat.pos_of_mem_divisors mem
    have eq := Nat.mul_div_cancel' dv
    apply good
    refine ⟨hh,dv,?_⟩
    have large : 2 ≤ i/h := by
      by_contra! sm
      have := Nat.mul_le_mul_left h (show i/h ≤ 1 by omega)
      omega
    have lower := Nat.mul_le_mul_left h large
    omega

#print axioms signed_log_coefficient
end LongCycleBounds.DescentMesh
