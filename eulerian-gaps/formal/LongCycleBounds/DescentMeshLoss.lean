import LongCycleBounds.DescentMeshMass

/-! Degree and Cauchy scaling for the raw Gessel--Reutenauer logarithmic decorations. -/
namespace LongCycleBounds.DescentMesh
open Finset

/-- A decoration in the necklace logarithm has size jb and alphabet degree j/d. -/
theorem decoration_loss {j b d : ℕ} (hj : 3 ≤ j) (hb : 1 ≤ b) (hd : 1 ≤ d)
    (bad : b ≠ 1 ∨ d ≠ 1) : 2 ≤ j*b-j/d ∧ j*b ≤ 2*(j*b-j/d) := by
  have jbase := Nat.div_le_self j d
  by_cases one : b = 1
  · subst b
    simp only [Nat.mul_one]
    have dt : 2 ≤ d := by omega
    have half : j/d ≤ j/2 := Nat.div_le_div_left dt (by omega)
    omega
  · have bt : 2 ≤ b := by omega
    have mult : j*2 ≤ j*b := Nat.mul_le_mul_left j bt
    omega

/-- Exponentiating the bad log only concatenates decorations; total loss is at least
half the entire decorated length. Repeated equal selections are allowed. -/
theorem decoration_sum_loss {ι : Type*} (s : Finset ι) (j b d : ι → ℕ)
    (valid : ∀ i ∈ s, 3 ≤ j i ∧ 1 ≤ b i ∧ 1 ≤ d i ∧ (b i ≠ 1 ∨ d i ≠ 1)) :
    ∑ i ∈ s, j i*b i ≤ 2 * ∑ i ∈ s, (j i*b i-j i/d i) := by
  rw [mul_sum]
  apply sum_le_sum
  intro i hi
  obtain ⟨hj,hb,hd,hbad⟩ := valid i hi
  exact (decoration_loss hj hb hd hbad).2

/-- The empty-residual coefficients gain a uniform power when their evaluation radius
shrinks, for any finite multiset expansion with signed coefficients. -/
theorem reweight_empty {ι : Type*} (s : Finset ι) (loss : ι → ℕ) (a : ι → ℝ)
    {n : ℕ} (support : ∀ i ∈ s, n ≤ 2 * loss i) {v V : ℝ}
    (hv : 0 ≤ v) (hV : 0 < V) (hcomp : v ≤ V) :
    |∑ i ∈ s, a i * v^(loss i)| ≤
      (v/V)^((n+1)/2) * ∑ i ∈ s, |a i| * V^(loss i) := by
  apply (abs_sum_le_sum_abs _ _).trans
  rw [mul_sum]
  apply sum_le_sum
  intro i hi
  have small : (n+1)/2 ≤ loss i := by have := support i hi; omega
  have u0 := div_nonneg hv hV.le
  have u1 := (div_le_one hV).mpr hcomp
  have pow := pow_le_pow_of_le_one u0 u1 small
  rw [abs_mul, abs_of_nonneg (pow_nonneg hv _)]
  calc
    _ = (v/V)^(loss i) * (|a i| * V^(loss i)) := by rw [div_pow]; field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right pow (by positivity)

#print axioms decoration_sum_loss
#print axioms reweight_empty
end LongCycleBounds.DescentMesh
