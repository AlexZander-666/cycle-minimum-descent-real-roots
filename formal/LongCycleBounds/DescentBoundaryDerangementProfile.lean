import LongCycleBounds.DescentBoundaryDerangementSeries
import Mathlib.Algebra.Polynomial.Reverse

noncomputable section
namespace LongCycleBounds.DescentNecklace
open Finset Polynomial

private theorem choose_step_rat (q j : ℕ) :
    ((q:ℚ)-j)*q.choose j = ((j:ℚ)+1)*q.choose (j+1) := by
  have e : ((q:ℚ)+1)*q.choose j = ((q+1).choose (j+1):ℚ)*((j:ℚ)+1) := by
    exact_mod_cast Nat.add_one_mul_choose_eq q j
  rw [Nat.choose_succ_succ, Nat.cast_add] at e
  linarith only [e]

/-- Homogenize the falling-factorial recursion at a nonzero alphabet. -/
theorem scaled_atom_eval (a : ℕ → ℚ[X]) (zero : a 0 = 1)
    (step : ∀ j, a (j+1) = C (1/((j:ℚ)+1))*(X*C (j:ℚ)-1)*a j)
    {q : ℕ} (pos : 0 < q) (j : ℕ) :
    (q:ℚ)^j * (a j).eval (q:ℚ)⁻¹ = (-1:ℚ)^j*q.choose j := by
  have nz : (q:ℚ) ≠ 0 := by positivity
  induction j with
  | zero => simp [zero]
  | succ j ih =>
    have jnz : (j:ℚ)+1 ≠ 0 := by positivity
    calc
      _ = ((j:ℚ)-q)/((j:ℚ)+1)*((q:ℚ)^j*(a j).eval (q:ℚ)⁻¹) := by
        rw [step,pow_succ]
        simp only [eval_mul,eval_C,eval_sub,eval_X,eval_one]
        field_simp
      _ = _ := by
        rw [ih,pow_succ]
        field_simp
        linear_combination -choose_step_rat q j

theorem profile_two_eq_reflected {n : ℕ} (hn : 0 < n)
    (a : ℕ → ℚ[X]) (zero : a 0 = 1)
    (step : ∀ j, a (j+1) = C (1/((j:ℚ)+1))*(X*C (j:ℚ)-1)*a j)
    (bound : (∑ j ∈ range (n+1), a j).natDegree ≤ n) :
    profilePolynomial n 2 = reflect n (∑ j ∈ range (n+1), a j) := by
  let t := ∑ j ∈ range (n+1), a j
  apply Polynomial.eq_of_infinite_eval_eq
  have inj : Function.Injective (fun i : ℕ ↦ ((i+1:ℕ):ℚ)) := by
    intro i j h
    exact Nat.succ.inj (Nat.cast_injective h)
  apply (Set.infinite_range_of_injective inj).mono
  rintro _ ⟨i,rfl⟩
  let q := i+1
  have pos : 0 < q := Nat.succ_pos i
  have nz : (q:ℚ) ≠ 0 := by positivity
  have nzi : (q:ℚ)⁻¹ ≠ 0 := inv_ne_zero nz
  let _ : Invertible (q:ℚ)⁻¹ := invertibleOfNonzero nzi
  have eq := eval₂_reflect_mul_pow (RingHom.id ℚ) (q:ℚ)⁻¹ n t bound
  simp only [invOf_eq_inv, inv_inv,eval₂_id,inv_pow] at eq
  have value : (reflect n t).eval (q:ℚ) = (q:ℚ)^n*t.eval (q:ℚ)⁻¹ := by
    rw [← eq]
    field_simp
  change (profilePolynomial n 2).eval (q:ℚ) = (reflect n t).eval (q:ℚ)
  rw [value,eval_profile_nat]
  have orig := letters_eq_necklace_content hn q 2
  rw [letters_eq_positiveCountDP hn] at orig
  have nc : Nat.card (NecklaceContent n q 2) = positiveCountDP n q 2 := by exact_mod_cast orig.symm
  rw [nc,derangement_alphabet_exact]
  simp only [t,eval_finsetSum,mul_sum]
  apply sum_congr rfl
  intro j hj
  have jn := Nat.le_of_lt_succ (mem_range.mp hj)
  have at_q := scaled_atom_eval a zero step pos j
  rw [← at_q,show (q:ℚ)^n=(q:ℚ)^j*(q:ℚ)^(n-j) by rw [← pow_add]; congr 1; omega]
  ring

#print axioms profile_two_eq_reflected
end LongCycleBounds.DescentNecklace
