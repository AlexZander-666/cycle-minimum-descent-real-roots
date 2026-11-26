import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Tactic

/-! Elementary uniform and upper-half bounds on the factorial ratios of the Eulerian moments. -/
namespace LongCycleBounds.DescentMesh
open Finset Real

theorem scaled_falling_factorial {n d : ℕ} (hd : d ≤ n) :
    n^d * d.factorial ≤ n.descFactorial d * d^d := by
  have each (j : ℕ) : n * (d-j) ≤ (n-j)*d := by
    rw [Nat.mul_sub, Nat.sub_mul]
    exact Nat.sub_le_sub_left (by simpa [Nat.mul_comm] using Nat.mul_le_mul_right j hd) _
  have h := prod_le_prod' (s := range d) (fun j _ ↦ each j)
  simpa [prod_mul_distrib, ← Nat.descFactorial_eq_prod_range, Nat.descFactorial_self] using h

/-- Last d factors of n! have geometric mean at least n/e. -/
theorem falling_ge_exp {n d : ℕ} (hd : d ≤ n) :
    ((n:ℝ)/exp 1)^d ≤ n.descFactorial d := by
  have h₁ : (n:ℝ)^d * d.factorial ≤ (n.descFactorial d:ℝ)*(d:ℝ)^d := by
    exact_mod_cast scaled_falling_factorial hd
  have dpos : 0 < (d.factorial:ℝ) := by positivity
  have h₂ := (div_le_iff₀ dpos).mp (pow_div_factorial_le_exp (d:ℝ) (Nat.cast_nonneg (α := ℝ) d) d)
  have E : exp (d:ℝ) = exp 1 ^ d := by simpa only [mul_one] using exp_nat_mul 1 d
  rw [E] at h₂
  rw [div_pow, div_le_iff₀ (by positivity)]
  apply (mul_le_mul_iff_left₀ dpos).mp
  calc
    _ ≤ _ := h₁
    _ ≤ _ := mul_le_mul_of_nonneg_left h₂ (Nat.cast_nonneg _)
    _ = _ := by ring

/-- If the remaining lower index is at least half the top order, one can replace e by 2. -/
theorem falling_ge_half {n d : ℕ} (hd : 2*d ≤ n) :
    ((n:ℝ)/2)^d ≤ n.descFactorial d := by
  have each (j : ℕ) (hj : j ∈ range d) : (n:ℝ)/2 ≤ (n-j:ℕ) := by
    have jl := mem_range.mp hj
    have := (show n ≤ 2*(n-j) by omega)
    exact (div_le_iff₀ (by norm_num)).mpr (by exact_mod_cast (by omega : n ≤ (n-j)*2))
  have h := prod_le_prod (s := range d) (fun j _ ↦ by positivity : ∀ j ∈ range d, 0 ≤ (n:ℝ)/2) each
  rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
  simpa [div_pow] using h

private theorem factorial_weight {n h : ℕ} (hh : h ≤ n) {r B : ℝ} (hr : 0 ≤ r)
    (hB : 0 < B) (fall : B^(n-h) ≤ n.descFactorial (n-h)) :
    ((h.factorial:ℝ)/n.factorial)*r^(n-h) ≤ (r/B)^(n-h) := by
  have fact : (h.factorial:ℝ)*n.descFactorial (n-h)=n.factorial := by
    exact_mod_cast (by simpa [show n-(n-h)=h by omega] using
      Nat.factorial_mul_descFactorial (Nat.sub_le n h))
  rw [div_pow]
  apply (le_div_iff₀ (pow_pos hB _)).mpr
  have hn : 0 < (n.factorial:ℝ) := by positivity
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
  apply (div_le_iff₀ hn).mpr
  rw [← fact]
  calc
    _ = (h.factorial:ℝ)*r^(n-h)*B^(n-h) := by ring
    _ ≤ (h.factorial:ℝ)*r^(n-h)*n.descFactorial (n-h) :=
      mul_le_mul_of_nonneg_left fall (by positivity)
    _ = _ := by ring

/-- Actual relative factorial weight of a lower-order Eulerian pole contribution. -/
theorem uniform_factorial_weight {n h : ℕ} (hn : 0 < n) (hh : h ≤ n) {r : ℝ} (hr : 0 ≤ r) :
    ((h.factorial:ℝ)/n.factorial)*r^(n-h) ≤ (exp 1*r/n)^(n-h) := by
  have npos : 0 < (n:ℝ) := by exact_mod_cast hn
  convert factorial_weight hh hr (div_pos npos (exp_pos 1)) (falling_ge_exp (Nat.sub_le n h)) using 1
  congr 1
  field_simp

theorem upper_half_factorial_weight {n h : ℕ} (hn : 0 < n) (hh : h ≤ n) (half : n ≤ 2*h)
    {r : ℝ} (hr : 0 ≤ r) :
    ((h.factorial:ℝ)/n.factorial)*r^(n-h) ≤ (2*r/n)^(n-h) := by
  have npos : 0 < (n:ℝ) := by exact_mod_cast hn
  convert factorial_weight hh hr (show 0 < (n:ℝ)/2 by positivity)
    (falling_ge_half (show 2*(n-h) ≤ n by omega)) using 1
  congr 1
  ring

#print axioms uniform_factorial_weight
#print axioms upper_half_factorial_weight
#print axioms falling_ge_exp
#print axioms falling_ge_half
end LongCycleBounds.DescentMesh
