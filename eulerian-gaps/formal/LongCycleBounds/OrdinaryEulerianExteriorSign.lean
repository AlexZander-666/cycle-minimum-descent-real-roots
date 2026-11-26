import LongCycleBounds.OrdinaryEulerianExteriorTriple
import LongCycleBounds.OrdinaryEulerianExteriorTail
import LongCycleBounds.OuterMoments

/-! A normalized color and the bare first moment have the same sign at a true Eulerian zero. -/
noncomputable section
namespace LongCycleBounds.OrdinaryEulerianExterior
open Outer Real

theorem aligned_moments {p : ℕ} (hp : 72 ≤ p) {x : ℝ} (hx : 0 < x)
    (region : 5 * sqrt p / 2 ≤ x) (G : ℕ → ℝ)
    (steps : ∀ j, 1/2 ≤ G (j+1)-G j ∧ G (j+1)-G j ≤ 3 ∧
      (2 ≤ j → 119/144 ≤ G (j+1)-G j ∧ G (j+1)-G j ≤ 169/144))
    (lip : ∀ i j : ℕ, |G i-G j| ≤ 3*|(i:ℝ)-j|)
    (hsG : Summable (fun j : ℕ ↦ (-1:ℝ)^j*weight p x j*G j))
    (hsQ : Summable (fun j : ℕ ↦ (-1:ℝ)^j*weight p x j*((j:ℝ)+1)))
    (hz : Outer.moment p x = 0) :
    0 < (∑' j : ℕ, (-1:ℝ)^j*weight p x j*G j) *
      (∑' j : ℕ, (-1:ℝ)^j*weight p x j*((j:ℝ)+1)) := by
  let w (j : ℕ) := (-1:ℝ)^j*weight p x j
  let m := mode p x hx
  obtain ⟨s, ε, unit, near, core⟩ := directed_core hp hx region
  have aligned (F : ℕ → ℝ)
      (hF : ∀ j, 1/2 ≤ F (j+1)-F j ∧ F (j+1)-F j ≤ 3 ∧
        (2 ≤ j → 119/144 ≤ F (j+1)-F j ∧ F (j+1)-F j ≤ 169/144))
      (hL : ∀ i j : ℕ, |F i-F j| ≤ 3*|(i:ℝ)-j|)
      (hs : Summable (fun i ↦ w i*F i)) : 0 < ε*(∑' i, w i*F i) := by
    let f (i : ℕ) := w i * (F i-F s)
    have hw : Summable w := summable_signed_weight p x hx
    have zero : (∑' i, w i) = 0 := hz
    have hsub (i : ℕ) : f i = w i*F i - w i*F s := mul_sub .. 
    have hf : Summable f := (hs.sub (hw.mul_right (F s))).congr (fun i ↦ (hsub i).symm)
    have shift : (∑' i, f i) = ∑' i, w i*F i := by
      simp_rw [hsub]
      rw [hs.tsum_sub (hw.mul_right _),tsum_mul_right,zero,zero_mul,sub_zero]
    let C := f m+leftAt f m 1+f (m+1)
    have E : |(∑' i, f i)-C| ≤ 888/2401*weight p x m :=
      centered_tail (by omega) hx region F s hL near hf
    have M : 888/2401*weight p x m < ε*C := core F hF
    have lower := neg_abs_le (ε*((∑' i, f i)-C))
    rw [abs_mul,unit,one_mul] at lower
    rw [←shift]
    nlinarith only [lower,E,M]
  have A := aligned G steps lip hsG
  have B := aligned (fun i ↦ (i:ℝ)+1) (by intro j; push_cast; rw [show (j:ℝ)+1+1-((j:ℝ)+1) = 1 by ring]; norm_num)
    (by intro i j; rw [show (i:ℝ)+1-((j:ℝ)+1)=(i:ℝ)-j by ring]; linarith [abs_nonneg ((i:ℝ)-j)]) hsQ
  have pair := mul_pos A B
  have e2 := sq_abs ε
  rw [unit,one_pow] at e2
  change 0 < (∑' j, w j*G j)*(∑' j : ℕ, w j*((j:ℝ)+1))
  rw [show (ε*(∑' i, w i*G i))*(ε*(∑' i : ℕ, w i*((i:ℝ)+1))) =
      ε^2*((∑' i, w i*G i)*(∑' i : ℕ, w i*((i:ℝ)+1))) by ring, ←e2,one_mul] at pair
  exact pair

#print axioms aligned_moments
end LongCycleBounds.OrdinaryEulerianExterior
