import LongCycleBounds.DescentMeshFullKernel

/-! A fixed-horizon row of the actual signed logarithmic expansion satisfies
the same triangular recurrence as the necklace product. -/
noncomputable section
namespace LongCycleBounds.DescentMesh
open Finset Polynomial ArithmeticFunction
open scoped Moebius

def rawDivisors (j : ℕ) : Polynomial ℝ :=
  ∑ d ∈ j.divisors, monomial (j/d) ((μ d:ℤ):ℝ)

def necklaceStep (k s : ℕ) (row : ℕ→Polynomial ℝ) : Polynomial ℝ :=
  ∑ j ∈ Icc k s, ∑ b ∈ Icc 1 (s/j), rawDivisors j * row (s-j*b)

def expansionRow (k H s : ℕ) : Polynomial ℝ :=
  (goodPolynomial H k*badTaylor k H H H).coeff s

theorem rawDivisors_eq_mobiusPolynomial {j : ℕ} (hj : 0<j) :
    rawDivisors j = (j:Polynomial ℝ) * (DescentNecklace.mobiusPolynomial j).map (Rat.castHom ℝ) := by
  unfold rawDivisors DescentNecklace.mobiusPolynomial
  rw [Polynomial.map_mul,Polynomial.map_C]
  have scalar : (j:Polynomial ℝ)*C ((Rat.castHom ℝ) ((j:ℚ)⁻¹))=1 := by
    rw [← C_eq_natCast, ← C_mul]
    have cast (q : ℚ) : Rat.castHom ℝ q = (q:ℝ) := rfl
    rw [cast,Rat.cast_inv,Rat.cast_natCast,mul_inv_cancel₀ (by exact_mod_cast hj.ne'),C_1]
  rw [← mul_assoc,scalar,one_mul,Polynomial.map_sum]
  apply sum_congr rfl
  intro d _
  rw [Polynomial.map_mul,Polynomial.map_C,Polynomial.map_pow,Polynomial.map_X,
    C_mul_X_pow_eq_monomial]
  congr 1

private theorem kernel_term (P : BiPoly) (s j b : ℕ) :
    (monomial (j*b) (rawDivisors j)*P).coeff s =
      if j*b≤ s then rawDivisors j*P.coeff (s-j*b) else 0 := by
  rw [← C_mul_X_pow_eq_monomial,mul_assoc,coeff_C_mul,coeff_X_pow_mul']
  split_ifs <;> simp

theorem kernel_step {k H s : ℕ} (hk : 1≤k) (hs : s≤H) (P : BiPoly) :
    (rawKernel k H * P).coeff s = necklaceStep k s P.coeff := by
  unfold rawKernel necklaceStep
  rw [sum_mul,finsetSum_coeff]
  simp only [sum_mul,finsetSum_coeff]
  change (∑ j ∈ Icc k H, ∑ b ∈ Icc 1 H, (monomial (j*b) (rawDivisors j)*P).coeff s) = _
  simp_rw [kernel_term]
  have hjset : Icc k s ⊆ Icc k H := fun j h ↦ mem_Icc.mpr ⟨(mem_Icc.mp h).1,(mem_Icc.mp h).2.trans hs⟩
  rw [← sum_subset hjset]
  · apply sum_congr rfl
    intro j hj
    have jp : 0<j := hk.trans (mem_Icc.mp hj).1
    have hsub : Icc 1 (s/j) ⊆ Icc 1 H := fun b hb ↦ mem_Icc.mpr
      ⟨(mem_Icc.mp hb).1,(mem_Icc.mp hb).2.trans ((Nat.div_le_self ..).trans hs)⟩
    rw [← sum_subset hsub]
    · apply sum_congr rfl
      intro b hb
      have yes := (Nat.le_div_iff_mul_le jp).mp (mem_Icc.mp hb).2
      rw [if_pos (by simpa [Nat.mul_comm] using yes)]
    · intro b hb bad
      have hnot : ¬j*b≤ s := fun h ↦ bad (mem_Icc.mpr ⟨(mem_Icc.mp hb).1,
        (Nat.le_div_iff_mul_le jp).mpr (by simpa [Nat.mul_comm] using h)⟩)
      rw [if_neg hnot]
  · intro j hj out
    apply sum_eq_zero
    intro b hb
    have big : s<j := by have := mem_Icc.mp hj; simp_all
    have step := Nat.le_mul_of_pos_right j (mem_Icc.mp hb).1
    simp [show ¬j*b≤ s by omega]

theorem expansionRow_recurrence {k H s : ℕ} (hk : 3≤k) (hH : 1≤H) (hs : s≤H) :
    (s:Polynomial ℝ)*expansionRow k H s = necklaceStep k s (expansionRow k H) := by
  have eq := X_pow_dvd_iff.mp (good_bad_log_equation (N:=H) hk) s (by omega)
  change ((goodKernel H k+eulerOp (badLogPolynomial k H H))*
    (goodPolynomial H k*badTaylor k H H H)-eulerOp (goodPolynomial H k*badTaylor k H H H)).coeff s=0 at eq
  rw [good_add_bad_kernel hk hH,coeff_sub,euler_coeff,kernel_step (by omega) hs] at eq
  exact (sub_eq_zero.mp eq).symm

theorem expansionRow_zero {k : ℕ} (hk : 3≤k) (H : ℕ) : expansionRow k H 0 = 1 := by
  have z := X_dvd_iff.mp (X_dvd_badLogPolynomial hk H H)
  have z' : constantCoeff (badLogPolynomial k H H) = 0 := z
  unfold expansionRow
  rw [mul_coeff_zero,goodPolynomial_coeff (Nat.zero_le _),FixedCycleCount.allowedFraction_zero,
    monomial_zero_left,C_1,one_mul]
  change constantCoeff (badTaylor k H H H) = 1
  simp [badTaylor,map_add,map_sum,map_pow,map_mul,z']

/-- The explicit signed expansion specializes any row solving the actual finite
necklace recurrence. All calls in the step strictly decrease the extraction index. -/
theorem expansionRow_unique {k H : ℕ} (hk : 3≤k) (hH : 1≤H) (f : ℕ→Polynomial ℝ)
    (f0 : f 0=1) (recurrence : ∀ s, 1≤ s → s≤H →
      (s:Polynomial ℝ)*f s = necklaceStep k s f) {n : ℕ} (hn : n≤H) :
    f n = expansionRow k H n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases nz : n=0
    · subst n
      rw [f0,expansionRow_zero hk]
    have np : 0<n := Nat.pos_of_ne_zero nz
    apply mul_left_cancel₀ (show (n:Polynomial ℝ)≠0 by exact_mod_cast nz)
    rw [recurrence n np hn,expansionRow_recurrence hk hH hn]
    unfold necklaceStep
    apply sum_congr rfl
    intro j hj
    apply sum_congr rfl
    intro b hb
    have jp : 0<j := by have h := (mem_Icc.mp hj).1; omega
    have bp := (mem_Icc.mp hb).1
    have lt : n-j*b<n := Nat.sub_lt np (Nat.mul_pos jp bp)
    rw [ih _ lt (by omega)]

#print axioms expansionRow_unique
#print axioms rawDivisors_eq_mobiusPolynomial
#print axioms expansionRow_recurrence
end LongCycleBounds.DescentMesh
