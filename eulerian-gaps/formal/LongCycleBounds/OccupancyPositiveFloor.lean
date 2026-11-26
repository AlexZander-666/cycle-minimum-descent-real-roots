import LongCycleBounds.OccupancyBoundedLoadJump
import LongCycleBounds.CycleProbability

/-! Compare survival to the event of long slot cycles and sufficient occupancy on each slot. -/
noncomputable section
namespace LongCycleBounds.Occupancy
open Finset Equiv LongCycles FixedCycleCount Polynomial
open scoped Classical

/-- A lower counterpart to the usual 1/B bound for permutations excluding short cycles. -/
theorem allowedFraction_ge_half {m B : ℕ} (hB : 2 ≤ B) (bm : B ≤ m) :
    1/(2*(B:ℝ)) ≤ allowedFraction m B := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    have mp : 0<(m:ℝ) := by exact_mod_cast (by omega : 0 < m)
    have bp : 0<(B:ℝ) := by exact_mod_cast (by omega : 0 < B)
    have recu := allowedFraction_recurrence (n:=m) hB (by omega)
    have last := mem_Icc.mpr ⟨bm,le_refl m⟩
    rw [←sum_erase_add _ _ last,Nat.sub_self,allowedFraction_zero] at recu
    let I := Icc B (m-B)
    have lower : (I.card:ℝ)*(1/(2*(B:ℝ))) ≤ ∑ a ∈ (Icc B m).erase m, allowedFraction (m-a) B := by
      calc
        _ = ∑ _ ∈ I, 1/(2*(B:ℝ)) := by simp
        _ ≤ ∑ a ∈ I, allowedFraction (m-a) B := by
          apply sum_le_sum
          intro a ha
          have ⟨lo,hi⟩ := mem_Icc.mp ha
          exact ih (m-a) (by omega) (by omega)
        _ ≤ _ := by
          apply sum_le_sum_of_subset_of_nonneg _ (fun a _ _ ↦ allowedFraction_nonneg _ _)
          intro a ha
          have ⟨lo,hi⟩ := mem_Icc.mp ha
          exact mem_erase.mpr ⟨by omega,mem_Icc.mpr ⟨lo,by omega⟩⟩
    have count : m ≤ I.card + 2*B := by dsimp [I];rw [Nat.card_Icc];omega
    have countR : (m:ℝ) ≤ I.card+2*(B:ℝ) := by exact_mod_cast count
    apply (div_le_iff₀ (show 0<2*(B:ℝ) by positivity)).mpr
    apply le_of_mul_le_mul_left (a:=(m:ℝ)) _ mp
    have loR := mul_le_mul_of_nonneg_right lower (show 0≤2*(B:ℝ) by positivity)
    field_simp at loR
    linear_combination (norm := ring_nf) countR + loR - 2*(B:ℝ)*recu
    exact le_rfl 

private theorem slot_cycle_load {n m B q : ℕ} (hB : 2 ≤ B)
    (σ : Perm (Fin m)) (ok : Allowed B σ) (b : Fin n → Fin m)
    (full : ∀ s, q ≤ counts b s) (t : Tag σ) : B*q ≤ counts (tag σ ∘ b) t := by
  have long : B ≤ counts (tag σ) t := by
    cases t with
    | inl i => exact False.elim ((ne_fixed_of_allowed ok (by omega) i.val) i.property)
    | inr c =>
      rw [counts_tag_cycle]
      exact le_of_mem_cycleType ok (Multiset.mem_map.mpr ⟨c.val,c.property,rfl⟩)
  let S := univ.filter (fun s : Fin m ↦ tag σ s=t)
  have sumEq : ∑ s ∈ S, counts b s = counts (tag σ ∘ b) t := by
    unfold counts
    rw [sum_card_fiberwise_eq_card_filter]
    simp [S]
  calc
    _ ≤ S.card*q := Nat.mul_le_mul_right _ long
    _ = ∑ _ ∈ S, q := by simp
    _ ≤ ∑ s ∈ S, counts b s := sum_le_sum (fun s _ ↦ full s)
    _ = _ := sumEq

private theorem sample_survival_lower {n m k B q : ℕ} (hB : 2 ≤ B) (cut : 2 ≤ k) (enough : k ≤ B*q)
    {u : ℝ} (hu : 0 ≤ u) (σ : Perm (Fin m)) (b : Fin n → Fin m) :
    (if Allowed B σ then (1:ℝ) else 0)-slotWeight k u σ b ≤ ∑ s : Fin m, (2:ℝ)^q*slotDiscount s b := by
  have pos (s : Fin m) : 0≤(2:ℝ)^q*slotDiscount s b := by
    unfold slotDiscount
    positivity
  have wp : 0 ≤ slotWeight k u σ b := prod_nonneg fun _ _ ↦ loadMark_nonneg _ hu _
  by_cases ok : Allowed B σ
  · rw [if_pos ok]
    by_cases full : ∀ s, q≤counts b s
    · have one : slotWeight k u σ b = 1 := by
        apply prod_eq_one
        intro t _
        have hit := enough.trans (slot_cycle_load hB σ ok b full t)
        simp [loadMark,show ¬counts (tag σ ∘ b) t<2 by omega,not_lt.mpr hit]
      rw [one,sub_self]
      exact sum_nonneg (fun s _ ↦ pos s)
    · obtain ⟨s,bad⟩ := not_forall.mp full
      apply (by linarith : 1-slotWeight k u σ b ≤ 1).trans
      apply le_trans _ (single_le_sum (fun s (_:s∈univ) ↦ pos s) (mem_univ s))
      have eq : slotDiscount s b=(1/2:ℝ)^(counts b s) := by simp [slotDiscount,counts,prod_ite]
      rw [eq,div_pow,one_pow,←div_eq_mul_one_div,le_div_iff₀ (by positivity),one_mul]
      exact pow_le_pow_right₀ (by norm_num) (by omega)
  · rw [if_neg ok]
    exact (by linarith : 0-slotWeight k u σ b ≤ 0).trans (sum_nonneg fun s _ ↦ pos s)

/-- Uniform lower bound for all finite positive labels, with explicit union-bound loss. -/
theorem slotProbability_lower_block {n m k B q : ℕ} (hB : 2 ≤ B) (bm : B ≤ m)
    (hk : 2 ≤ k) (enough : k ≤ B*q) {u : ℝ} (hu : 0 ≤ u) :
    1/(2*(B:ℝ)) - (m:ℝ)*(2:ℝ)^q*(1-1/(2*(m:ℝ)))^n ≤ markedSlotProbability n k m u := by
  let D := (m.factorial:ℝ)*(m:ℝ)^n
  have hm : 0 < m := by omega
  have mp : 0<(m:ℝ) := by exact_mod_cast hm
  have dp : 0<D := by dsimp [D]; positivity
  have row : ∑ σ : Perm (Fin m), ∑ _ : Fin n → Fin m, (if Allowed B σ then (1:ℝ) else 0) =
      (m:ℝ)^n*(enumerator m B).eval 1 := by
    simp only [sum_const,card_univ,Fintype.card_fun,Fintype.card_fin,nsmul_eq_mul,mul_sum,
      enumerator,eval_finsetSum,apply_ite,eval_pow,eval_X,one_pow,eval_zero]
    simp only [Nat.cast_pow]
  have per : (∑ b : Fin n → Fin m, ∑ s : Fin m,(2:ℝ)^q*slotDiscount s b) =
      (m:ℝ)*((2:ℝ)^q*((m:ℝ)-1/2)^n) := by
    rw [sum_comm]
    simp only [←mul_sum,discount_sum,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
    ring
  have low := allowedFraction_ge_half hB bm
  unfold allowedFraction at low
  have lp := (le_div_iff₀ (show (0:ℝ) < m.factorial by positivity)).mp low
  have qpos : 0≤(m:ℝ)^n := by positivity
  have helper : (1-1/(2*(m:ℝ)))*m=(m:ℝ)-1/2 := by field_simp
  have rescale : (1-1/(2*(m:ℝ)))^n*(m:ℝ)^n=((m:ℝ)-1/2)^n := by rw [←mul_pow,helper]
  change _ ≤ _ /D
  apply (le_div_iff₀ dp).mpr
  dsimp only [D]
  have first := mul_le_mul_of_nonneg_left lp qpos
  have total' := sum_le_sum (s:=univ) fun (σ : Perm (Fin m)) _ ↦
    sum_le_sum (s:=univ) fun (b : Fin n → Fin m) _ ↦ sample_survival_lower hB hk enough hu σ b
  simp_rw [sum_sub_distrib] at total'
  rw [row] at total'
  simp only [per,sum_const,card_univ,Fintype.card_perm,Fintype.card_fin,nsmul_eq_mul] at total'
  linear_combination (norm := ring_nf) first + total' - (m.factorial:ℝ)*m*(2:ℝ)^q*rescale
  exact le_rfl

private theorem discount_tail_exponential {n m k : ℕ} (hm : 0 < m) (size : 4*m*k ≤ n) :
    (2:ℝ)^k*(1-1/(2*(m:ℝ)))^n ≤ Real.exp (-(n:ℝ)/(4*m)) := by
  have mp : 0<(m:ℝ) := by exact_mod_cast hm
  have ms : 1≤(m:ℝ) := by exact_mod_cast hm
  have two : (2:ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1:ℝ)]
  have laplace : 1-1/(2*(m:ℝ)) ≤ Real.exp (-(1/(2*(m:ℝ)))) :=
    (by linarith [Real.add_one_le_exp (-(1/(2*(m:ℝ))))] : _)
  have low : 0 ≤ 1-1/(2*(m:ℝ)) := by
    apply sub_nonneg.mpr ((div_le_one (by positivity)).mpr (by linarith))
  have bound := mul_le_mul (pow_le_pow_left₀ (by norm_num) two k) (pow_le_pow_left₀ low laplace n)
    (pow_nonneg low n) (pow_nonneg (Real.exp_pos _).le k)
  apply bound.trans
  rw [←Real.exp_nat_mul,←Real.exp_nat_mul,←Real.exp_add]
  apply Real.exp_le_exp.mpr
  have nbound : 4*(m:ℝ)*k ≤ n := by exact_mod_cast size
  field_simp
  nlinarith



/-- Relative source-row increment with a positive denominator supplied by long slot cycles.
The parameter q only witnesses a finite integer rounding of the target cutoff. -/
theorem labelFraction_relative_bounded_load {n m k B q : ℕ} (hB : 2 ≤ B) (bm : B ≤ m)
    (hk : 2 ≤ k) (half : 2*k ≤ n) (enough : k ≤ B*q) (size : 4*m*q ≤ n)
    (small : (m:ℝ)*Real.exp (-(n:ℝ)/(4*m)) ≤ 1/(4*(B:ℝ)))
    {u : ℝ} (hu : u ∈ Set.Icc (0:ℝ) 1) :
    1/(4*(B:ℝ)) ≤ labelFraction n k m u ∧
    0 ≤ (m:ℝ)*(labelFraction (n+1) k m u-labelFraction n k m u)/labelFraction n k m u ∧
    (m:ℝ)*(labelFraction (n+1) k m u-labelFraction n k m u)/labelFraction n k m u ≤
      4*(B:ℝ)*(B/Real.sqrt ((k-1:ℕ):ℝ)+((m:ℝ)+1)*Real.exp (-(n:ℝ)/(4*m))) := by
  have hm : 0 < m := by omega
  have mp : 0<(m:ℝ) := by exact_mod_cast hm
  have bp : 0<(B:ℝ) := by exact_mod_cast (by omega : 0<B)
  have qp : 0<q := by by_contra! h; simp [show q=0 by omega] at enough;omega
  have sparse : 4*m ≤ n := (Nat.le_mul_of_pos_right _ qp).trans size
  have window : 4*m*k ≤ n*B := calc
    _ ≤ 4*m*(B*q) := Nat.mul_le_mul_left _ enough
    _ = 4*m*q*B := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ size
  have floor := slotProbability_lower_block (n:=n) hB bm hk enough hu.1
  have norm : labelFraction n k m u = markedSlotProbability n k m u := by
    simp only [labelFraction,original_profile_eq_slot_probability hm,mul_div_cancel_left₀ _ (pow_ne_zero _ mp.ne')]
  have tail := mul_le_mul_of_nonneg_left (discount_tail_exponential hm size) mp.le
  have inv : 1/(2*(B:ℝ))=2*(1/(4*(B:ℝ))) := by field_simp;ring
  have den : 1/(4*(B:ℝ)) ≤ labelFraction n k m u := by
    rw [norm]
    rw [inv] at floor
    linarith only [floor,tail,small]
  have pos : 0<labelFraction n k m u := (by positivity : 0<1/(4*(B:ℝ))).trans_le den
  obtain ⟨nn,upper⟩ := labelFraction_increment_bounded_load hm hk half sparse window hu
  refine ⟨den,div_nonneg nn pos.le,(div_le_iff₀ pos).mpr (upper.trans ?_)⟩
  have factor := (div_le_iff₀ (show 0<4*(B:ℝ) by positivity)).mp den
  have cap : 0≤B/Real.sqrt ((k-1:ℕ):ℝ)+((m:ℝ)+1)*Real.exp (-(n:ℝ)/(4*m)) := by positivity
  linarith only [mul_le_mul_of_nonneg_left factor cap]

#print axioms labelFraction_relative_bounded_load

#print axioms allowedFraction_ge_half
#print axioms slotProbability_lower_block
end LongCycleBounds.Occupancy
