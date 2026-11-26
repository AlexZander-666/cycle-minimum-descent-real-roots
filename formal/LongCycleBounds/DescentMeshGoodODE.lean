import LongCycleBounds.DescentMeshTaylorODE

/-! The admissible-permutation residual and the signed Taylor polynomial satisfy
the logarithmic derivative equation at every index up to the extraction horizon. -/
noncomputable section
namespace LongCycleBounds.DescentMesh
open Finset Polynomial FixedCycleCount

def goodKernel (N k : ℕ) : BiPoly := ∑ j ∈ Icc k N, biTerm j j 1

theorem goodPolynomial_coeff {n N : ℕ} (hn : n≤N) (k : ℕ) :
    (goodPolynomial N k).coeff n = monomial n (allowedFraction n k) := by
  simp only [goodPolynomial,finsetSum_coeff,biTerm,coeff_monomial,sum_ite_eq',
    mem_range,show n<N+1 by omega,ite_true]

private theorem monomial_mul_coeff_any {R : Type*} [CommSemiring R] (p : R[X]) (a : R) (j n : ℕ) :
    ((monomial j a)*p).coeff n = if j≤n then a * p.coeff (n-j) else 0 := by
  rw [← C_mul_X_pow_eq_monomial,mul_assoc,coeff_C_mul,coeff_X_pow_mul']
  split_ifs <;> simp

theorem goodKernel_equation {N k : ℕ} (hk : 2≤k) :
    X^(N+1) ∣ goodKernel N k*goodPolynomial N k - eulerOp (goodPolynomial N k) := by
  apply X_pow_dvd_iff.mpr
  intro n h
  have hn : n≤N := by omega
  rw [coeff_sub,euler_coeff,goodPolynomial_coeff hn]
  apply sub_eq_zero.mpr
  unfold goodKernel
  rw [sum_mul,finsetSum_coeff]
  have term (j : ℕ) : ((biTerm j j 1)*goodPolynomial N k).coeff n =
      if j≤n then monomial n (allowedFraction (n-j) k) else 0 := by
    rw [biTerm,monomial_mul_coeff_any]
    split_ifs with hj
    · rw [goodPolynomial_coeff (by omega),monomial_mul_monomial,one_mul,show j+(n-j)=n by omega]
    · rfl
  simp_rw [term]
  rw [← sum_filter,show (Icc k N).filter (fun j ↦ j≤n)=Icc k n by ext j; simp; omega,
    ← map_sum]
  have eq : (n:ℝ)*allowedFraction n k = ∑ j ∈ Icc k n, allowedFraction (n-j) k := by
    by_cases np : n=0
    · subst n
      simp [show Icc k 0=∅ by exact Icc_eq_empty_of_lt (by omega)]
    · exact allowedFraction_recurrence hk (Nat.pos_of_ne_zero np)
  rw [← eq, ← C_eq_natCast,C_mul_monomial]

theorem euler_product {R : Type*} [CommRing R] (p q : R[X]) :
    eulerOp (p*q) = eulerOp p*q + p*eulerOp q := by
  unfold eulerOp
  rw [derivative_mul]
  ring

/-- Actual ODE for the product whose coefficient is bounded by the absolute-loss
theorems. The omitted high Taylor coefficients disappear modulo z^(N+1). -/
theorem good_bad_log_equation {N k : ℕ} (hk : 3≤k) :
    let B := badLogPolynomial k N N
    let F := goodPolynomial N k * badTaylor k N N N
    X^(N+1) ∣ (goodKernel N k+eulerOp B)*F - eulerOp F := by
  dsimp only
  rw [badTaylor_as_finiteTaylor,euler_product]
  have G := goodKernel_equation (N:=N) (by omega : 2≤k)
  have B := finiteTaylor_discard (X_dvd_badLogPolynomial hk N N) N
  have z := dvd_add (dvd_mul_of_dvd_left G (finiteTaylor (badLogPolynomial k N N) N))
    (dvd_mul_of_dvd_right B (goodPolynomial N k))
  convert z using 1; ring

#print axioms goodKernel_equation
#print axioms good_bad_log_equation
end LongCycleBounds.DescentMesh
