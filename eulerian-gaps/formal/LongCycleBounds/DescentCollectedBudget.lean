import LongCycleBounds.DescentCollectedWords

noncomputable section
namespace LongCycleBounds.DescentMesh.Collected
open Finset Polynomial Real FixedCycleCount DescentNecklace

private theorem coeff_good_term (n k l d : ℕ) (a : ℝ) :
    ((goodPolynomial n k*biTerm l d a).coeff n) =
      if l≤n then monomial (n-l+d) (allowedFraction (n-l) k*a) else 0 := by
  classical
  unfold goodPolynomial
  rw [sum_mul,finsetSum_coeff]
  simp only [biTerm,monomial_mul_monomial,coeff_monomial]
  by_cases hl : l≤n
  · rw [if_pos hl, sum_eq_single (n-l)]
    · simp [Nat.sub_add_cancel hl]
    · intro i _ ine
      simp [show i+l≠n by omega]
    · simp
  · simp [hl,show ∀ i, i+l≠n by omega]


def rowCoeff (n k h : ℕ) : ℝ :=
  (if h=n then allowedFraction n k else 0) +
  ∑ w : Word k n, if WL w ≤ n ∧ h=n-WS w then
     allowedFraction (n-WL w) k * WC w else 0

theorem coeff_actual {k n : ℕ} (hk : 3 ≤ k) (hn : 1 ≤ n) (d : ℕ) :
    ((profilePolynomial n k).coeff d:ℝ) = rowCoeff n k d := by
  have e := congrArg (fun p : ℝ[X] ↦ p.coeff d) (original_row hk hn)
  rw [coeff_map] at e
  apply e.trans
  rw [taylor_words,mul_add,mul_one,mul_sum,coeff_add,coeff_add,finsetSum_coeff,finsetSum_coeff]
  unfold rowCoeff
  congr 1
  · have h := coeff_good_term n k 0 0 1
    simpa [coeff_monomial,eq_comm] using congrArg (fun f : ℝ[X] ↦ f.coeff d) h
  · apply sum_congr rfl
    intro w _
    rw [coeff_good_term]
    by_cases le : WL w ≤ n
    · have sum := wl_eq w
      rw [if_pos le,coeff_monomial,show n-WL w+WD w=n-WS w by omega]
      simp [le,eq_comm]
    · simp [le]
theorem loss_bound (n k : ℕ) {v : ℝ} (hv : 0≤v) :
    lossNorm n (rowCoeff n k) v ≤
    ∑ w : Word k n, if WL w ≤ n then
       allowedFraction (n-WL w) k * (|WC w| * v^(WS w)) else 0 := by
  classical
  have leLoss (w : Word k n) : WS w ≤ WL w := by have := wl_eq w; omega
  let f (h : ℕ) (w : Word k n) : ℝ := if WL w ≤ n ∧ h=n-WS w then
     allowedFraction (n-WL w) k * (|WC w| * v^(WS w)) else 0
  have per (h : ℕ) (hh : h ∈ Ico 1 n) : |rowCoeff n k h| *v^(n-h) ≤ ∑ w, f h w := by
    have ne : h≠n := (mem_Ico.mp hh).2.ne
    simp only [rowCoeff,if_neg ne,zero_add]
    apply (mul_le_mul_of_nonneg_right (abs_sum_le_sum_abs _ _) (pow_nonneg hv _)).trans
    rw [sum_mul]
    apply sum_le_sum
    intro w _
    dsimp only [f]
    split_ifs with e
    · have eq : n-h=WS w := by have := leLoss w; omega
      rw [eq,abs_mul,abs_of_nonneg (allowedFraction_nonneg ..),mul_assoc]
    · simp
  apply (sum_le_sum per).trans
  rw [sum_comm]
  apply sum_le_sum
  intro w _
  dsimp only [f]
  by_cases len : WL w ≤ n
  · simp only [len,true_and,ite_true,sum_ite_eq']
    split_ifs
    · rfl
    · exact mul_nonneg (allowedFraction_nonneg ..) (by positivity)
  · simp [len]


theorem atom_cost (k n : ℕ) (v : ℚ) :
    (∑ z : Atom k n, |scalar z| * (v:ℝ)^(loss z)) =
      ((∑ i∈Icc 1 n,SignedBounds.costQ k i v:ℚ):ℝ) := by
  rw [Fintype.sum_sigma,Rat.cast_sum]
  conv_rhs => rw [←sum_coe_sort]
  apply sum_congr rfl
  intro i _
  simp only [SignedBounds.costQ,Rat.cast_div,Rat.cast_sum,Rat.cast_mul,Rat.cast_natCast,
    Rat.cast_pow,scalar,length,degree,loss,abs_div,Nat.abs_cast]
  conv_rhs => rw [←sum_coe_sort, sum_div]
  apply sum_congr rfl
  intro d _
  push_cast
  ring

private theorem word_cap {k n : ℕ} {v c : ℝ} (hv : 0 ≤ v) (cap :
    (∑ z : Atom k n,|scalar z| * v^(loss z)) ≤ c) :
    (∑ w : Word k n,|WC w| * v^(WS w)) ≤ exp c-1 := by
  classical
  let a := ∑ z : Atom k n, |scalar z| * v^(loss z)
  have ap : 0 ≤ a := sum_nonneg fun _ _ ↦ by positivity
  have h := Real.sum_le_exp_of_nonneg ap (n+1)
  rw [sum_range_succ',pow_zero,Nat.factorial_zero,Nat.cast_one,div_one] at h
  have eq : (∑ w : Word k n,|WC w| * v^(WS w)) = ∑ i∈range n, a^(i+1)/((i+1).factorial:ℝ) := by
    rw [Fintype.sum_sigma,←Fin.sum_univ_eq_sum_range]
    apply sum_congr rfl
    intro i _
    rw [←tupleMass_eq (fun z : Atom k n ↦ |scalar z| * v^(loss z)) (i.val+1)]
    unfold tupleMass
    rw [sum_div]
    apply sum_congr rfl
    intro w _
    simp only [WC,WS,abs_div,abs_prod,Nat.abs_cast,prod_mul_distrib,prod_pow_eq_pow_sum]
    ring
  change a≤c at cap
  rw [eq]
  linarith only [h,exp_le_exp.mpr cap]

theorem word_cost {k : ℕ} (hk : 3 ≤ k) (ku : k ≤ 7) (n : ℕ) :
    (∑ w : Word k n,|WC w| * (4/5:ℝ)^(WS w)) ≤ exp (SignedBounds.cSmall k)-1 ∧
    (∑ w : Word k n,|WC w| * (93/100:ℝ)^(WS w)) ≤ exp (SignedBounds.cLarge k)-1 := by
  have ⟨hs,hl⟩ := SignedBounds.short_atom_budgets hk ku n
  constructor
  · apply word_cap (by norm_num)
    have eq := atom_cost k n (4/5)
    have le := (Rat.cast_le (K:=ℝ)).mpr hs
    push_cast at eq le
    exact eq.le.trans le
  · apply word_cap (by norm_num)
    have eq := atom_cost k n (93/100)
    have le := (Rat.cast_le (K:=ℝ)).mpr hl
    push_cast at eq le
    exact eq.le.trans le

#print axioms coeff_actual
#print axioms word_cost
end LongCycleBounds.DescentMesh.Collected
