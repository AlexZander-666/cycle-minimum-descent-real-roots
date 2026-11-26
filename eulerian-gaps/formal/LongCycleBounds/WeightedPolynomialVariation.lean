import LongCycleBounds.FiniteConvolutionTail

/-! The weighted coefficient ℓ¹ norm and propagation of strict dominance
under a differentiated polynomial convolution. -/
noncomputable section
namespace WeightedPolynomialVariation
open Polynomial Finset

def absolutePoly (p : ℝ[X]) : ℝ[X] := ∑ i ∈ p.support, monomial i |p.coeff i|

@[simp] theorem coeff_absolute (p : ℝ[X]) (i : ℕ) : (absolutePoly p).coeff i = |p.coeff i| := by
  classical
  by_cases hi : i ∈ p.support
  · simp [absolutePoly,finsetSum_coeff,coeff_monomial,hi]
  · have zero : p.coeff i=0 := by simpa using hi
    simp [absolutePoly,finsetSum_coeff,coeff_monomial,hi,zero]

def mass (r : ℝ) (p : ℝ[X]) : ℝ := (absolutePoly p).eval r

theorem mass_range (r : ℝ) (p : ℝ[X]) {N : ℕ} (h : p.natDegree<N) :
    mass r p = ∑ i ∈ range N, |p.coeff i| *r^i := by
  have bound : (absolutePoly p).natDegree<N := by
    apply lt_of_le_of_lt _ h
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    simp [coeff_eq_zero_of_natDegree_lt hi]
  simp only [mass,eval_eq_sum_range' bound,coeff_absolute]

private theorem eval_order {p q : ℝ[X]} {r : ℝ} (hr : 0 ≤ r)
    (ordered : ∀ i, p.coeff i ≤ q.coeff i) : p.eval r ≤ q.eval r := by
  let N := max p.natDegree q.natDegree + 1
  rw [eval_eq_sum_range' (show p.natDegree<N by dsimp [N];omega),
      eval_eq_sum_range' (show q.natDegree<N by dsimp [N];omega)]
  exact sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_right (ordered i) (pow_nonneg hr _)

theorem mass_nonneg {r : ℝ} (hr : 0 ≤ r) (p : ℝ[X]) : 0 ≤ mass r p := by
  rw [mass_range r p (Nat.lt_succ_self _)]
  exact sum_nonneg fun i _ ↦ mul_nonneg (abs_nonneg _) (pow_nonneg hr i)

theorem mass_mul {r : ℝ} (hr : 0 ≤ r) (p q : ℝ[X]) : mass r (p*q) ≤ mass r p*mass r q := by
  unfold mass
  rw [←eval_mul]
  apply eval_order hr
  intro i
  simp only [coeff_absolute,coeff_mul]
  simpa only [abs_mul] using abs_sum_le_sum_abs (fun a : ℕ × ℕ ↦ p.coeff a.1*q.coeff a.2)
    (antidiagonal i)

theorem mass_sum {ι : Type*} {r : ℝ} (hr : 0 ≤ r) (s : Finset ι) (f : ι → ℝ[X]) :
    mass r (∑ i ∈ s,f i) ≤ ∑ i ∈ s,mass r (f i) := by
  unfold mass
  rw [←eval_finsetSum]
  apply eval_order hr
  intro i
  simpa only [coeff_absolute,finsetSum_coeff] using abs_sum_le_sum_abs (fun a ↦ (f a).coeff i) s

theorem mass_neg (r : ℝ) (p : ℝ[X]) : mass r (-p)=mass r p := by
  unfold mass
  congr 1
  ext
  simp

theorem mass_const_mul (r a : ℝ) (p : ℝ[X]) : mass r (C a*p)=|a| *mass r p := by
  have eq : absolutePoly (C a*p)= C |a| *absolutePoly p := by ext; simp [abs_mul]
  simp only [mass,eq,eval_mul,eval_C]

theorem mass_add {r : ℝ} (hr : 0 ≤ r) (p q : ℝ[X]) :
    mass r (p+q) ≤ mass r p+mass r q := by
  unfold mass
  rw [←eval_add]
  apply eval_order hr
  intro i
  simpa only [coeff_absolute,coeff_add] using abs_add_le (p.coeff i) (q.coeff i)

theorem mass_split (r : ℝ) (p : ℝ[X]) :
    mass r p = |p.coeff 0| + r*mass r p.divX := by
  have eq : absolutePoly p = C |p.coeff 0| + X*absolutePoly p.divX := by
    ext i
    cases i <;> simp [coeff_X_mul,coeff_divX]
  simp only [mass,eq,eval_add,eval_C,eval_mul,eval_X]

/-- Signed constant coefficient less the weighted mass in all positive degrees. -/
def margin (r : ℝ) (p : ℝ[X]) : ℝ := p.coeff 0 - r*mass r p.divX

theorem margin_fall {r : ℝ} (hr : 0 ≤ r) (p q : ℝ[X]) :
    margin r p-margin r q ≤ mass r (q-p) := by
  have h := mass_add hr p.divX (q-p).divX
  rw [←divX_add,add_sub_cancel] at h
  rw [mass_split r (q-p),coeff_sub]
  unfold margin
  linarith only [mul_le_mul_of_nonneg_left h hr,neg_abs_le (q.coeff 0-p.coeff 0)]

/-- ℓ¹ propagation from an exact identity of polynomial sequences, with the coefficient
convolution checked before any scalar norm inequality is applied. -/
theorem margin_of_recurrence (G E T : ℕ → ℝ[X]) {r : ℝ} (hr : 0 ≤ r)
    (B : ℕ) (Bp : 1 ≤ B) (S : ℕ → ℝ) (sp : ∀ i, 1 ≤ i → 0 ≤ S i)
    (tail : ∀ i,1 ≤ i → mass r (T i)+S (i+1) ≤ S i) (gap : S 1 < B)
    (identity : ∀ n,B ≤ n → C (n:ℝ)*E n = -(∑ j ∈ range n, E j*T (n-j)))
    (diff : ∀ n,B ≤ n → E n = G n-G (n-1))
    (init : FiniteConvolutionTail.potential (fun j ↦ mass r (E j)) S B <
      ((B:ℝ)-S 1)*margin r (G (B-1))) :
    ∀ n,B-1 ≤ n → 0 < margin r (G n) := by
  apply FiniteConvolutionTail.margin_persists (e:=fun j ↦ mass r (E j))
    (t:=fun i ↦ mass r (T i)) (S:=S) (Δ:=fun n ↦ margin r (G n)) (fun _ ↦ mass_nonneg hr _)
    sp tail B Bp gap _ _ init
  · intro n hn
    have h := congrArg (mass r) (identity n hn)
    rw [mass_const_mul,abs_of_nonneg (Nat.cast_nonneg n),mass_neg] at h
    rw [h]
    exact (mass_sum hr _ _).trans (sum_le_sum fun _ _ ↦ mass_mul hr _ _)
  · intro n hn
    rw [diff n hn]
    exact margin_fall hr _ _

#print axioms mass_mul
#print axioms margin_fall
#print axioms margin_of_recurrence
end WeightedPolynomialVariation
