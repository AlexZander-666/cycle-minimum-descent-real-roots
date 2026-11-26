import LongCycleBounds.DescentMeshExtraction

/-! A finite Taylor exponential solves its Euler logarithmic derivative equation
in degrees through the Taylor cutoff, over any commutative rational algebra. -/
noncomputable section
namespace LongCycleBounds.DescentMesh
open Finset Polynomial

def eulerOp {R : Type*} [CommRing R] (f : R[X]) := X * derivative f

theorem euler_coeff {R : Type*} [CommRing R] (f : R[X]) (n : ℕ) :
    (eulerOp f).coeff n = (n:R)*f.coeff n := by
  cases n with
  | zero => simp [eulerOp]
  | succ n => simp only [eulerOp,coeff_X_mul,coeff_derivative,Nat.cast_succ]; ring

def finiteTaylor {R : Type*} [CommRing R] [Algebra ℚ R] (f : R[X]) (T : ℕ) : R[X] :=
  1+ ∑ h ∈ range T, C (algebraMap ℚ R (((h+1).factorial:ℚ)⁻¹)) * f^(h+1)

theorem finiteTaylor_succ {R : Type*} [CommRing R] [Algebra ℚ R] (f : R[X]) (h : ℕ) :
    finiteTaylor f (h+1) = finiteTaylor f h +
      C (algebraMap ℚ R (((h+1).factorial:ℚ)⁻¹)) * f^(h+1) := by
  simp only [finiteTaylor,sum_range_succ,add_assoc]

private theorem fac_step {R : Type*} [CommRing R] [Algebra ℚ R] (h : ℕ) :
    C (algebraMap ℚ R (((h+1).factorial:ℚ)⁻¹)) * C ((h+1:ℕ):R) =
      (C (algebraMap ℚ R ((h.factorial:ℚ)⁻¹)) : R[X]) := by
  have sq : (((h+1).factorial:ℚ)⁻¹)*((h+1:ℕ):ℚ) = (h.factorial:ℚ)⁻¹ := by
    rw [Nat.factorial_succ,Nat.cast_mul,mul_inv_rev]
    have nz : ((h+1:ℕ):ℚ) ≠ 0 := by positivity
    rw [mul_assoc,inv_mul_cancel₀ nz,mul_one]
  simpa only [map_mul,map_natCast] using congrArg (fun x : ℚ ↦ (C (algebraMap ℚ R x):R[X])) sq

theorem derivative_finiteTaylor_succ {R : Type*} [CommRing R] [Algebra ℚ R] (f : R[X]) (h : ℕ) :
    derivative (finiteTaylor f (h+1)) = derivative f * finiteTaylor f h := by
  induction h with
  | zero => simp only [finiteTaylor,sum_range_one,sum_range_zero,zero_add,Nat.factorial_one,Nat.cast_one, inv_one,map_one,one_mul,pow_one,add_zero,derivative_add,derivative_one,mul_one]
  | succ h ih =>
    rw [finiteTaylor_succ f (h+1),derivative_add,ih,derivative_C_mul,derivative_pow,
      Nat.add_sub_cancel,← mul_assoc,← mul_assoc,fac_step]
    rw [finiteTaylor_succ f h]
    ring

theorem finiteTaylor_discard {R : Type*} [CommRing R] [Algebra ℚ R] {f : R[X]}
    (hx : X ∣ f) (T : ℕ) :
    X^(T+1) ∣ eulerOp f * finiteTaylor f T - eulerOp (finiteTaylor f T) := by
  have zero : eulerOp f * finiteTaylor f 0 - eulerOp (finiteTaylor f 0) = X * derivative f := by
    simp only [finiteTaylor,sum_range_zero,add_zero,eulerOp,derivative_one,mul_zero,mul_one,sub_zero]
  cases T with
  | zero => rw [zero,pow_one]; exact dvd_mul_right ..
  | succ h =>
    have de : eulerOp (finiteTaylor f (h+1)) = eulerOp f*finiteTaylor f h := by
      simp only [eulerOp,derivative_finiteTaylor_succ,mul_assoc]
    rw [de,finiteTaylor_succ f h]
    let a := C (algebraMap ℚ R (((h+1).factorial:ℚ)⁻¹))
    have eq : eulerOp f*(finiteTaylor f h+a*f^(h+1))-eulerOp f*finiteTaylor f h =
        (X*f^(h+1))*(derivative f*a) := by unfold eulerOp; ring
    rw [eq,pow_succ']
    exact dvd_mul_of_dvd_left (mul_dvd_mul_left X (pow_dvd_pow_of_dvd hx (h+1))) _

/-- A coefficientwise truncated Euler logarithmic derivative with no remainder
in any degree at most T. -/
theorem finiteTaylor_euler_coeff {R : Type*} [CommRing R] [Algebra ℚ R] {f : R[X]}
    (hx : X ∣ f) {n T : ℕ} (hn : n≤T) :
    (n:R)*(finiteTaylor f T).coeff n = (eulerOp f * finiteTaylor f T).coeff n := by
  have h := X_pow_dvd_iff.mp (finiteTaylor_discard hx T) n (by omega)
  rw [coeff_sub,euler_coeff] at h
  exact (sub_eq_zero.mp h).symm

theorem X_dvd_badLogPolynomial {k : ℕ} (hk : 3≤k) (N B : ℕ) :
    X ∣ badLogPolynomial k N B := by
  unfold badLogPolynomial
  apply dvd_sum
  intro z _
  apply X_dvd_iff.mpr
  have len : atomLength z ≠ 0 := by
    have loss := atom_loss hk z
    have le : atomLoss z ≤ atomLength z := Nat.sub_le .. 
    omega
  simp [biTerm,coeff_monomial,len]

theorem badTaylor_as_finiteTaylor (k N B T : ℕ) :
    badTaylor k N B T = finiteTaylor (badLogPolynomial k N B) T := by
  unfold badTaylor finiteTaylor
  apply congrArg (fun z : BiPoly ↦ 1+z)
  apply sum_congr rfl
  intro h _
  have ratCast (x : ℚ) : algebraMap ℚ ℝ x = (x:ℝ) := rfl
  simp only [biTerm,monomial_zero_left,Polynomial.algebraMap_apply,ratCast,Rat.cast_inv,
    Rat.cast_natCast]

#print axioms finiteTaylor_euler_coeff
#print axioms badTaylor_as_finiteTaylor
end LongCycleBounds.DescentMesh
