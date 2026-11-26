import LongCycleBounds.GeneralCycleSupports
import LongCycleBounds.OrderedLabelSum

/-! Absolute Cauchy products of ordered cycle moments. -/

noncomputable section

namespace LongCycleBounds.FixedCycleCount

open Finset CycleCount
open scoped Classical

private theorem piAntidiag_fin (h d : ℕ) :
    piAntidiag (univ : Finset (Fin h)) d = finAntidiagonal h d := by
  ext f
  simp

private theorem sum_piAntidiag_succ {R : Type*} [AddCommMonoid R] (h d : ℕ)
    (f : (Fin (h+1) → ℕ) → R) :
    (∑ g ∈ piAntidiag (univ : Finset (Fin (h+1))) d, f g) =
      ∑ b ∈ range (d+1), ∑ u ∈ piAntidiag (univ : Finset (Fin h)) (d-b), f (Fin.cons b u) := by
  simp only [piAntidiag_fin]
  rw [←Nat.sum_antidiagonal_eq_sum_range_succ
    (fun b e ↦ ∑ u ∈ finAntidiagonal h e, f (Fin.cons b u))]
  simp only [finAntidiagonal, finAntidiagonal.aux, sum_disjiUnion, sum_map, Function.Embedding.coeFn_mk]

private theorem multinomial_fin_cons {h : ℕ} (a : ℕ) (f : Fin h → ℕ) :
    Nat.multinomial univ (Fin.cons a f) =
      (a+∑ i, f i).choose a * Nat.multinomial univ f := by
  have aSpec := Nat.multinomial_spec univ (Fin.cons a f)
  have fSpec := Nat.multinomial_spec univ f
  simp only [Fin.prod_univ_succ, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ] at aSpec
  apply Nat.eq_of_mul_eq_mul_left (show 0 < a.factorial * ∏ i, (f i).factorial by positivity)
  calc
    _ = (a+∑ i, f i).factorial := aSpec
    _ = (a+∑ i, f i).choose a * a.factorial * (∑ i, f i).factorial := by
      simpa only [Nat.add_sub_cancel_left] using
        (Nat.choose_mul_factorial_mul_factorial (n := a+∑ i, f i) (k := a) (by omega)).symm
    _ = _ := by rw [←fSpec]; ring

/-- The recursive ordered-support expression is exactly the multinomial
sum over all ordered admissible length tuples. -/
theorem orderedMomentRow_multinomial (M : ℕ → ℝ) (n k h : ℕ) :
    orderedMomentRow M n k h =
      ∑ f ∈ (piAntidiag (univ : Finset (Fin h)) n).filter (fun f ↦ ∀ i, k ≤ f i),
        (Nat.multinomial univ f : ℝ) * ∏ i, M (f i) := by
  induction h generalizing n with
  | zero =>
    by_cases hn : n=0 <;> simp [orderedMomentRow, hn]
  | succ h ih =>
    rw [orderedMomentRow, sum_filter, sum_piAntidiag_succ]
    let put (a : ℕ) (f : Fin h → ℕ) : Fin (h+1) → ℕ := Fin.cons a f
    have sumF (a : ℕ) (high : a ≤ n) :
        (∑ f ∈ piAntidiag (univ : Finset (Fin h)) (n-a),
          if ∀ i, k ≤ put a f i then
            (Nat.multinomial univ (put a f):ℝ) * ∏ i, M (put a f i) else 0) =
          if k ≤ a then (n.choose a:ℝ) * M a * orderedMomentRow M (n-a) k h else 0 := by
      dsimp only [put]
      by_cases low : k ≤ a
      · rw [if_pos low, ih, sum_filter, mul_sum]
        apply sum_congr rfl
        intro f hf
        have total := (mem_piAntidiag.mp hf).1
        change (∑ i, f i) = n-a at total
        have nsum : a + ∑ i, f i = n := by omega
        rw [multinomial_fin_cons, nsum, Nat.cast_mul, Fin.prod_univ_succ]
        simp only [Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ, low, true_and]
        split_ifs with valid
        · ring
        · simp
      · simp [Fin.forall_fin_succ, low]
    have replace : (∑ a ∈ range (n+1), ∑ f ∈ piAntidiag (univ : Finset (Fin h)) (n-a),
          if ∀ i, k ≤ put a f i then
            (Nat.multinomial univ (put a f):ℝ) * ∏ i, M (put a f i) else 0) =
        ∑ a ∈ range (n+1), if k ≤ a then
          (n.choose a:ℝ)*M a*orderedMomentRow M (n-a) k h else 0 := by
      apply sum_congr rfl
      intro a ha
      have := mem_range.mp ha
      exact sumF a (by omega)
    dsimp only [put] at replace
    rw [replace, ←sum_filter]
    congr 1
    ext a
    simp only [mem_Icc, mem_filter, mem_range]
    omega

private theorem sum_length_offsets {R : Type*} [AddCommMonoid R]
    (h m k : ℕ) (hk : 1 ≤ k) (F : (Fin (h+1) → ℕ) → R) :
    (∑ a ∈ (piAntidiag (univ : Finset (Fin (h+1))) (m+h+1)).filter (fun a ↦ ∀ i, k ≤ a i), F a) =
      ∑ f ∈ (piAntidiag (univ : Finset (Fin (h+1))) m).filter (fun f ↦ ∀ i, k ≤ f i+1),
        F (fun i ↦ f i+1) := by
  symm
  apply sum_nbij' (fun f i ↦ f i+1) (fun a i ↦ a i-1)
  case hi =>
    intro f hf
    simp only [mem_filter,mem_piAntidiag,mem_univ,implies_true,and_true] at hf ⊢
    refine ⟨?_,hf.2⟩
    rw [sum_add_distrib]
    simp [hf.1,add_assoc]
  case hj =>
    intro a ha
    simp only [mem_filter,mem_piAntidiag,mem_univ,implies_true,and_true] at ha ⊢
    have sub (i : Fin (h+1)) : a i - 1 + 1 = a i := Nat.sub_add_cancel (hk.trans (ha.2 i))
    have calc_sum : (∑ i, ((a i-1) + 1)) = m+h+1 := by
      calc
        _ = ∑ i, a i := sum_congr rfl (fun i _ ↦ sub i)
        _ = _ := ha.1
    rw [sum_add_distrib] at calc_sum
    simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id,mul_one] at calc_sum
    exact ⟨by omega,fun i ↦ (sub i).symm ▸ ha.2 i⟩
  case left_neg =>
    intro f _
    funext i
    simp
  case right_neg =>
    intro a ha
    funext i
    exact Nat.sub_add_cancel (hk.trans ((mem_filter.mp ha).2 i))
  case h => exact fun _ _ ↦ rfl

private def momentOffset (t : ℝ) (a d : ℕ) : ℝ := ((d+1:ℕ):ℝ)^(a-1)*t^(d+1)

private theorem momentOffset_hasSum {a : ℕ} (ha : 2 ≤ a) {t : ℝ} (ht : ‖t‖ < 1) :
    HasSum (momentOffset t a) (Band.moment a t) := by
  have h : HasSum (fun l : ℕ ↦ (l:ℝ)^(a-1)*t^l) (Band.moment a t) := by
    have e := eulerian_eq_powerSeries (a-1) (by omega) t ht
    rw [show a-1+1=a by omega] at e
    rw [Band.moment,e]
    exact (summable_pow_mul_geometric_of_norm_lt_one (a-1) ht).hasSum
  have rest := (hasSum_nat_add_iff' 1).mpr h
  unfold momentOffset
  simpa [zero_pow (by omega : a-1≠0)] using rest

/-- For each ordered tuple of lengths, the coefficient of the product is the
sum over weak label offsets. The degree shift is one for each positive label. -/
theorem hasSum_product_moment_offsets {h : ℕ} (a : Fin h → ℕ) (ha : ∀ i, 2 ≤ a i)
    {t : ℝ} (ht : ‖t‖ < 1) :
    HasSum (fun d : ℕ ↦ t^(d+h) * ∑ g ∈ piAntidiag (univ : Finset (Fin h)) d,
      ∏ i, ((g i+1:ℕ):ℝ)^(a i-1)) (∏ i, Band.moment (a i) t) := by
  induction h with
  | zero =>
    let F (d : ℕ) := t^(d+0) * ∑ g ∈ piAntidiag (univ : Finset (Fin 0)) d,
      ∏ i, ((g i+1:ℕ):ℝ)^(a i-1)
    have zero : F 0 = 1 := by simp [F]
    have rest (d : ℕ) (hd : d ≠ 0) : F d = 0 := by simp [F,hd]
    change HasSum F _
    rw [Fin.prod_univ_zero,←zero]
    exact hasSum_single (f := F) 0 rest
  | succ h ih =>
    let f := momentOffset t (a 0)
    let g (d : ℕ) := t^(d+h) * ∑ u ∈ piAntidiag (univ : Finset (Fin h)) d,
      ∏ i, ((u i+1:ℕ):ℝ)^(a i.succ-1)
    have hf : HasSum f (Band.moment (a 0) t) := momentOffset_hasSum (ha 0) ht
    have hg : HasSum g (∏ i : Fin h, Band.moment (a i.succ) t) :=
      ih (fun i ↦ a i.succ) (fun i ↦ ha i.succ)
    have conv := hasSum_sum_range_mul_of_summable_norm hf.summable.norm hg.summable.norm
    rw [hf.tsum_eq,hg.tsum_eq] at conv
    rw [Fin.prod_univ_succ]
    apply conv.congr_fun
    intro d
    rw [sum_piAntidiag_succ,mul_sum]
    apply sum_congr rfl
    intro b hb
    have bl := mem_range.mp hb
    simp only [Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ,←mul_sum]
    dsimp [f,g,momentOffset]
    rw [show d+(h+1)=b+1+(d-b+h) by omega, pow_add]
    ring

private theorem sum_labelPieces {R : Type*} [AddCommMonoid R] (h d : ℕ)
    (F : (Fin (h+1) → ℕ) → R) :
    (∑ g ∈ labelPieces h d, F g) = ∑ g ∈ piAntidiag (univ : Finset (Fin (h+1))) d, F g := by
  let e : (Fin (h+1) →₀ ℕ) ≃ (Fin (h+1) → ℕ) := Finsupp.equivFunOnFinite
  apply sum_nbij' e e.symm
  · intro g hg
    exact mem_piAntidiag.mpr ⟨(mem_finsuppAntidiag.mp hg).1,fun _ _ ↦ mem_univ _⟩
  · intro f hf
    have hsum := (mem_piAntidiag.mp hf).1
    apply mem_finsuppAntidiag.mpr
    refine ⟨?_, subset_univ _⟩
    have eq : (⇑(e.symm f)) = f := e.apply_symm_apply f
    rwa [eq]
  · exact fun g _ ↦ e.symm_apply_apply g
  · exact fun f _ ↦ e.apply_symm_apply f
  · exact fun _ _ ↦ rfl

/-- The exact ordered label coefficient, before dividing by the factorial of
the cycle count. Label d+h+1 and row m+h+1 use the offsets in OrderedLabelSum. -/
theorem orderedMomentRow_hasSum_shifted (h m k : ℕ) (hk : 2 ≤ k) {t : ℝ} (ht : ‖t‖ < 1) :
    HasSum (fun d : ℕ ↦ t^(d+(h+1))*(orderedLabelSum h m k d:ℝ))
      (orderedMomentRow (fun a ↦ Band.moment a t) (m+h+1) k (h+1)) := by
  let A := (piAntidiag (univ : Finset (Fin (h+1))) m).filter (fun f ↦ ∀ i, k ≤ f i+1)
  let P (f : Fin (h+1) → ℕ) : ℝ := (Nat.multinomial univ (fun i ↦ f i+1):ℝ)
  have each (f : Fin (h+1) → ℕ) (hf : f ∈ A) :
      HasSum (fun d : ℕ ↦ P f*(t^(d+(h+1)) * ∑ g ∈ labelPieces h d,
        ∏ i, ((g i+1:ℕ):ℝ)^(f i))) (P f*∏ i, Band.moment (f i+1) t) := by
    have low (i : Fin (h+1)) : 2 ≤ f i+1 := hk.trans ((mem_filter.mp hf).2 i)
    have product := hasSum_product_moment_offsets (fun i ↦ f i+1) low ht
    apply (product.mul_left (P f)).congr_fun
    intro d
    rw [sum_labelPieces h d (fun g ↦ ∏ i, ((g i+1:ℕ):ℝ)^(f i))]
    simp only [Nat.add_sub_cancel]
  have result := hasSum_sum each
  rw [orderedMomentRow_multinomial, sum_length_offsets h m k (by omega)]
  apply result.congr_fun
  intro d
  simp only [orderedLabelSum,Nat.cast_sum,Nat.cast_mul,Nat.cast_prod,Nat.cast_pow,mul_sum]
  conv_lhs => rw [sum_comm]
  apply sum_congr rfl
  intro f _
  apply sum_congr rfl
  intro g _
  unfold P
  ring

/-- Unshifted label coefficient for h+1 cycles. Positive pieces force the
coefficient to vanish below label h+1. -/
def orderedLabelCoeff (n k h l : ℕ) : ℕ :=
  if h+1 ≤ l then orderedLabelSum h (n-(h+1)) k (l-(h+1)) else 0

theorem orderedLabelCoeff_below {n k h l : ℕ} (hl : l < h+1) :
    orderedLabelCoeff n k h l = 0 := by
  simp [orderedLabelCoeff, not_le.mpr hl]

theorem orderedMomentRow_hasSum_labels {n k h : ℕ} (hk : 2 ≤ k) (hn : h+1 ≤ n)
    {t : ℝ} (ht : ‖t‖ < 1) :
    HasSum (fun l : ℕ ↦ t^l * (orderedLabelCoeff n k h l:ℝ))
      (orderedMomentRow (fun a ↦ Band.moment a t) n k (h+1)) := by
  have shifted := orderedMomentRow_hasSum_shifted h (n-(h+1)) k hk ht
  rw [show n-(h+1)+h+1=n by omega] at shifted
  have pre : (∑ l ∈ range (h+1), t^l * (orderedLabelCoeff n k h l:ℝ)) = 0 := by
    apply sum_eq_zero
    intro l hl
    simp [orderedLabelCoeff_below (mem_range.mp hl)]
  apply (hasSum_nat_add_iff' (h+1)).mp
  rw [pre,sub_zero]
  apply shifted.congr_fun
  intro d
  simp [orderedLabelCoeff]

/-- Total coefficient of label l in a nonempty original row, incorporating
the factorial symmetry divisor of every possible positive cycle count. -/
def originalLabelCoeff (n k l : ℕ) : ℝ :=
  ∑ h ∈ range (n/k), (1/((h+1).factorial:ℝ)) * (orderedLabelCoeff n k h l:ℝ)

@[simp] theorem originalLabelCoeff_zero (n k : ℕ) : originalLabelCoeff n k 0 = 0 := by
  unfold originalLabelCoeff
  apply sum_eq_zero
  intro h _
  simp [orderedLabelCoeff_below (by omega : 0 < h+1)]

/-- Positive-label Cauchy expansion for the original normalized permutation
row, without a bound on the number of admissible cycles. -/
theorem normalizedEnumerator_hasSum_orderedLabels {n k : ℕ} (hk : 2 ≤ k) (hn : 0 < n)
    (x : ℝ) (hx : 0 < x) :
    HasSum (fun l : ℕ ↦ (-Real.exp (-x))^l * originalLabelCoeff n k l)
      (Band.normalizedEnumerator n k x) := by
  let t := -Real.exp (-x)
  have ht : ‖t‖ < 1 := by
    change ‖-Real.exp (-x)‖ < 1
    rw [norm_neg, Real.norm_of_nonneg (Real.exp_nonneg _), Real.exp_lt_one_iff]
    linarith
  have term (h : ℕ) (hh : h ∈ range (n/k)) :
      HasSum (fun l : ℕ ↦ (1/((h+1).factorial:ℝ))*(t^l * (orderedLabelCoeff n k h l:ℝ)))
        ((1/((h+1).factorial:ℝ))*orderedMomentRow (fun a ↦ Band.moment a t) n k (h+1)) := by
    have le : h+1 ≤ n := (Nat.lt_iff_add_one_le.mp (mem_range.mp hh)).trans (Nat.div_le_self ..)
    exact (orderedMomentRow_hasSum_labels hk le ht).mul_left _
  have result := hasSum_sum term
  rw [normalizedEnumerator_ordered_cycle_rows hk x, sum_range_succ']
  simp only [orderedMomentRow.eq_1, if_neg hn.ne',mul_zero,add_zero]
  apply result.congr_fun
  intro l
  unfold originalLabelCoeff
  rw [mul_sum]
  apply sum_congr rfl
  intro h _
  change t^l * (1/((h+1).factorial:ℝ) * (orderedLabelCoeff n k h l:ℝ)) = _
  ring

#print axioms orderedMomentRow_multinomial
#print axioms hasSum_product_moment_offsets
#print axioms orderedMomentRow_hasSum_shifted
#print axioms orderedLabelCoeff_below
#print axioms orderedMomentRow_hasSum_labels
#print axioms originalLabelCoeff_zero
#print axioms normalizedEnumerator_hasSum_orderedLabels

end LongCycleBounds.FixedCycleCount
