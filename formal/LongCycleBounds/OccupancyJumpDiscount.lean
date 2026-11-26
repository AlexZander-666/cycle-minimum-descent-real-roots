import LongCycleBounds.OccupancyMarkedVerified

/-! A positive-label error bound obtained by discounting every ball on the landing slot. -/
noncomputable section
namespace LongCycleBounds.Occupancy
open Finset Equiv CycleProfile

private theorem slotWeight_mem {n m k : ℕ} {u : ℝ} (hu : u ∈ Set.Icc (0:ℝ) 1)
    (σ : Perm (Fin m)) (b : Fin n → Fin m) : slotWeight k u σ b ∈ Set.Icc (0:ℝ) 1 := by
  refine ⟨prod_nonneg (fun _ _ ↦ loadMark_nonneg _ hu.1 _),?_⟩
  apply prod_le_one (fun _ _ ↦ loadMark_nonneg _ hu.1 _)
  intro i _
  unfold loadMark
  split_ifs <;> linarith [hu.2]

/-- A Laplace weight for the number of old balls on the destination slot itself. -/
def slotDiscount {n m : ℕ} (s : Fin m) (b : Fin n → Fin m) : ℝ :=
  ∏ i, if b i=s then (1/2:ℝ) else 1

private theorem discount_eq {n m : ℕ} (s : Fin m) (b : Fin n → Fin m) :
    slotDiscount s b = (1/2:ℝ)^(counts b s) := by
  classical
  simp [slotDiscount,counts,prod_ite]

/-- Exact Laplace sum over independently placed labelled balls. -/
theorem discount_sum {n m : ℕ} (s : Fin m) :
    (∑ b : Fin n → Fin m, slotDiscount s b) = ((m:ℝ)-1/2)^n := by
  classical
  have one : (∑ i : Fin m, if i=s then (1/2:ℝ) else 1) = (m:ℝ)-1/2 := by
    have outside : ∑ i ∈ univ.erase s, (if i=s then (1/2:ℝ) else 1) =
        ∑ _ ∈ (univ : Finset (Fin m)).erase s, (1:ℝ) := by
      apply sum_congr rfl
      intro i hi
      simp [(mem_erase.mp hi).1]
    have h := sum_erase_add (f:=fun i : Fin m ↦ if i=s then (1/2:ℝ) else 1) _ (mem_univ s)
    rw [←h,outside, sum_const,card_erase_of_mem (mem_univ s), card_univ,Fintype.card_fin]
    simp only [if_true,nsmul_eq_mul,mul_one]
    rw [Nat.cast_sub (by have := s.isLt; omega : 1 ≤ m)]
    push_cast
    ring
  rw [show (∑ b : Fin n → Fin m, slotDiscount s b) =
      ∏ _ : Fin n, ∑ i : Fin m, if i=s then (1/2:ℝ) else 1 from
    (Fintype.prod_sum (fun (_:Fin n) (i:Fin m) ↦ if i=s then (1/2:ℝ) else 1)).symm]
  simp only [one,prod_const,card_univ,Fintype.card_fin]

private theorem counts_le_orbit {m n : ℕ} (σ : Perm (Fin m)) (s : Fin m) (b : Fin n → Fin m) :
    counts b s ≤ counts (tag σ ∘ b) (tag σ s) := by
  apply card_le_card
  intro i hi
  exact mem_filter.mpr ⟨mem_univ _,congrArg (tag σ) (mem_filter.mp hi).2⟩

/-- Independent of the slot permutation: if k balls already occupy this slot, landing here changes nothing. -/
theorem landing_change_discount {n m k : ℕ} (hk : 2 ≤ k) {u : ℝ} (hu : u ∈ Set.Icc (0:ℝ) 1)
    (σ : Perm (Fin m)) (s : Fin m) (b : Fin n → Fin m) :
    slotWeight k u σ (Fin.cons s b)-slotWeight k u σ b ≤ (2:ℝ)^k*slotDiscount s b := by
  by_cases hit : k ≤ counts b s
  · have enough := hit.trans (counts_le_orbit σ s b)
    rw [slotWeight_cons_sub hk]
    rw [if_neg (by omega),if_neg (by omega),zero_add,zero_mul,discount_eq]
    positivity
  · have w := (slotWeight_mem (k:=k) hu σ (Fin.cons s b)).2
    have p := (slotWeight_mem (k:=k) hu σ b).1
    apply (show slotWeight k u σ (Fin.cons s b)-slotWeight k u σ b ≤ 1 by linarith).trans
    rw [discount_eq,div_pow,one_pow,←div_eq_mul_one_div,le_div_iff₀ (by positivity),one_mul]
    exact pow_le_pow_right₀ (by norm_num) (by omega)

/-- Uniform exponential moment bound, before simplifying the degree-to-slot ratio. -/
theorem slot_probability_increment_discount {n m k : ℕ} (hm : 0 < m) (hk : 2 ≤ k)
    {u : ℝ} (hu : u ∈ Set.Icc (0:ℝ) 1) :
    markedSlotProbability (n+1) k m u - markedSlotProbability n k m u ≤
      (2:ℝ)^k*(1-1/(2*(m:ℝ)))^n := by
  classical
  have mp : 0<(m:ℝ) := by exact_mod_cast hm
  have nf : 0<(m.factorial:ℝ) := by positivity
  have inj (σ : Perm (Fin m)) : (∑ b : Fin (n+1) → Fin m, slotWeight k u σ b) =
      ∑ s : Fin m, ∑ b : Fin n → Fin m, slotWeight k u σ (Fin.cons s b) := by
    have h := (Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n+1) ↦ Fin m)) (slotWeight k u σ)).symm
    rw [Fintype.sum_prod_type] at h
    exact h
  have base : markedSlotProbability n k m u =
      (∑ σ : Perm (Fin m), ∑ _ : Fin m, ∑ b : Fin n → Fin m, slotWeight k u σ b) /
        ((m.factorial:ℝ)*(m:ℝ)^(n+1)) := by
    simp only [markedSlotProbability, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
      ←mul_sum,pow_succ]
    field_simp
  rw [base,markedSlotProbability,←sub_div]
  simp only [inj,←sum_sub_distrib]
  apply (div_le_div_of_nonneg_right (sum_le_sum fun σ _ ↦ sum_le_sum fun s _ ↦
    sum_le_sum fun b _ ↦ landing_change_discount hk hu σ s b) (by positivity)).trans
  simp only [←mul_sum,discount_sum,sum_const,card_univ,Fintype.card_fin,Fintype.card_perm,
    nsmul_eq_mul]
  have helper : (1-1/(2*(m:ℝ)))*m = (m:ℝ)-1/2 := by field_simp
  rw [←helper,mul_pow,pow_succ (m:ℝ) n]
  apply le_of_eq
  field_simp

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

/-- When mean load per slot is at least four times the cutoff, the actual normalized
adjacent-label increment is bounded by exp(-n/(4m)) uniformly on the common path. -/
theorem original_increment_small_load_ratio {n m k : ℕ} (hm : 0 < m) (hk : 2 ≤ k)
    (size : 4*m*k ≤ n) {u : ℝ} (hu : u ∈ Set.Icc (0:ℝ) 1) :
    let P := fun j ↦ anchoredLabel (profile k u) j m/(m:ℝ)^j
    0 ≤ P (n+1)-P n ∧ P (n+1)-P n ≤ Real.exp (-(n:ℝ)/(4*m)) := by
  dsimp only
  rw [original_profile_eq_slot_probability hm,original_profile_eq_slot_probability hm]
  have mp : 0<(m:ℝ) := by exact_mod_cast hm
  simp only [mul_div_cancel_left₀ _ (pow_ne_zero _ mp.ne')]
  refine ⟨sub_nonneg.mpr (markedSlotProbability_mono hm hk hu n),
    (slot_probability_increment_discount hm hk hu).trans ?_⟩
  exact discount_tail_exponential hm size

private theorem anchoredLabel_nonneg (k : ℕ) {u : ℝ} (hu : 0 ≤ u) (j m : ℕ) :
    0 ≤ anchoredLabel (profile k u) j m := by
  rw [original_profile_eq_slot_probability_all]
  apply mul_nonneg (by positivity)
  unfold markedSlotProbability
  apply div_nonneg _ (by positivity)
  exact sum_nonneg fun σ _ ↦ sum_nonneg fun b _ ↦ prod_nonneg fun _ _ ↦ loadMark_nonneg _ hu _

/-- A single full ball cycle furnishes this uniform lower bound, even when the mark vanishes. -/
theorem full_cycle_label_lower {n k m : ℕ} (hk : 2 ≤ k) (hn : k ≤ n)
    {u : ℝ} (hu : 0 ≤ u) : (m:ℝ)^(n-1) ≤ anchoredLabel (profile k u) n m := by
  obtain ⟨p,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
  have pp : p ≠ 0 := by omega
  rw [anchoredLabel]
  have pos (j : ℕ) : 0 ≤ profile k u j := by unfold profile; split_ifs <;> positivity
  have nonnegative (d : ℕ) :
      0 ≤ (p.choose d:ℝ)*profile k u (d+1)*
        ∑ l ∈ range (m+1), (l:ℝ)^d*anchoredLabel (profile k u) (p-d) (m-l) :=
    mul_nonneg (mul_nonneg (by positivity) (pos _)) (sum_nonneg fun _ _ ↦
      mul_nonneg (by positivity) (anchoredLabel_nonneg k hu _ _))
  apply le_trans _ (single_le_sum (fun d (_:d∈range (p+1)) ↦
    show (0:ℝ) ≤ (if d=0 then 0 else _) by split_ifs <;> first | rfl | exact nonnegative d)
    (mem_range.mpr (Nat.lt_succ_self p)))
  simp only [if_neg pp,Nat.choose_self,Nat.cast_one,profile,if_neg (not_lt.mpr hn),
    one_mul,Nat.sub_self,anchoredLabel]
  apply le_trans _ (single_le_sum (s:=range (m+1)) (a:=m) (fun l _ ↦
    show 0 ≤ (l:ℝ)^p*(if m-l=0 then (1:ℝ) else 0) by split_ifs <;> positivity) (mem_range.mpr (Nat.lt_succ_self m)))
  simp

theorem slot_probability_single_cycle_lower {n k m : ℕ} (hk : 2 ≤ k) (hn : k ≤ n) (hm : 0 < m)
    {u : ℝ} (hu : 0 ≤ u) : 1/(m:ℝ) ≤ markedSlotProbability n k m u := by
  have lo := full_cycle_label_lower (m:=m) hk hn hu
  rw [original_profile_eq_slot_probability hm] at lo
  have pos : 0 < (m:ℝ) := by exact_mod_cast hm
  apply (le_of_mul_le_mul_left (a:=(m:ℝ)^n) _ (pow_pos pos n))
  rw [show (m:ℝ)^n*(1/m)=(m:ℝ)^(n-1) by
    obtain ⟨p,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n≠0 by omega)
    simp [pow_succ,pos.ne']]
  exact lo

/-- Relative increment for the actual label coefficients, uniform in the common mark. -/
theorem original_relative_increment_small_load_ratio {n m k : ℕ} (hm : 0 < m) (hk : 2 ≤ k)
    (size : 4*m*k ≤ n) {u : ℝ} (hu : u ∈ Set.Icc (0:ℝ) 1) :
    let P := fun j ↦ anchoredLabel (profile k u) j m/(m:ℝ)^j
    0 ≤ P (n+1)-P n ∧ P (n+1)-P n ≤ (m:ℝ)*Real.exp (-(n:ℝ)/(4*m))*P n := by
  obtain ⟨pos,cap⟩ := original_increment_small_load_ratio hm hk size hu
  refine ⟨pos,cap.trans ?_⟩
  dsimp only
  have mp : 0<(m:ℝ) := by exact_mod_cast hm
  have kn : k ≤ n := (Nat.le_mul_of_pos_left k (by positivity : 0 < 4*m)).trans size
  have one := (div_le_iff₀ mp).mp (slot_probability_single_cycle_lower (m:=m) hk kn hm hu.1)
  rw [original_profile_eq_slot_probability hm,mul_div_cancel_left₀ _ (pow_ne_zero _ mp.ne')]
  calc
    _ ≤ Real.exp (-(n:ℝ)/(4*m))*(markedSlotProbability n k m u*m) :=
      le_mul_of_one_le_right (Real.exp_pos _).le one
    _ = _ := by ring

private theorem sample_deficit_union {m n k : ℕ} (hk : 2 ≤ k) {u : ℝ} (hu : u ∈ Set.Icc (0:ℝ) 1)
    (σ : Perm (Fin m)) (b : Fin n → Fin m) :
    1-slotWeight k u σ b ≤ ∑ s : Fin m, (2:ℝ)^k*slotDiscount s b := by
  classical
  have termP (s : Fin m) : 0 ≤ (2:ℝ)^k*slotDiscount s b := by rw [discount_eq];positivity
  by_cases all : ∀ s : Fin m, k ≤ counts b s
  · have hit : AllHit k σ b := by
      intro s
      apply (all s).trans (card_le_card ?_)
      intro j hj
      have v : b j=s := (mem_filter.mp hj).2
      exact mem_filter.mpr ⟨mem_univ _,by rw [v]⟩
    have eq : slotWeight k u σ b=1 := by
      apply prod_eq_one
      intro t _
      have kt := (allHit_iff σ b).mp hit t
      simp [loadMark,show ¬counts (tag σ ∘ b) t<2 by omega,not_lt.mpr kt]
    rw [eq,sub_self]
    exact sum_nonneg fun s _ ↦ termP s
  · obtain ⟨s,bad⟩ := not_forall.mp all
    have p := (slotWeight_mem (k:=k) hu σ b).1
    apply (by linarith : 1-slotWeight k u σ b ≤ 1).trans
    apply le_trans _ (single_le_sum (fun s (_ : s ∈ univ) ↦ termP s) (mem_univ s))
    rw [discount_eq,div_pow,one_pow,←div_eq_mul_one_div,le_div_iff₀ (by positivity),one_mul]
    exact pow_le_pow_right₀ (by norm_num) (by omega)

theorem slot_probability_le_one {m n k : ℕ} (hm : 0 < m) {u : ℝ} (hu : u ∈ Set.Icc (0:ℝ) 1) :
    markedSlotProbability n k m u ≤ 1 := by
  unfold markedSlotProbability
  apply (div_le_one (by positivity)).mpr
  have bound := sum_le_sum (s:=univ) fun (σ : Perm (Fin m)) _ ↦
    sum_le_sum (s:=univ) fun (b : Fin n → Fin m) _ ↦ (slotWeight_mem (k:=k) hu σ b).2
  simpa [Fintype.card_perm,nsmul_eq_mul] using bound

/-- The entire genuine coefficient is close to full occupancy in the low-load-ratio part of the transition. -/
theorem original_coefficient_near_full {m n k : ℕ} (hm : 0 < m) (hk : 2 ≤ k) (size : 4*m*k ≤ n)
    {u : ℝ} (hu : u ∈ Set.Icc (0:ℝ) 1) :
    |anchoredLabel (profile k u) n m/(m:ℝ)^n-1| ≤ (m:ℝ)*Real.exp (-(n:ℝ)/(4*m)) := by
  have mp : 0<(m:ℝ) := by exact_mod_cast hm
  rw [original_profile_eq_slot_probability hm,mul_div_cancel_left₀ _ (pow_ne_zero _ mp.ne'),
    abs_of_nonpos (sub_nonpos.mpr (slot_probability_le_one hm hu)),neg_sub]
  let D : ℝ := (m.factorial:ℝ)*(m:ℝ)^n
  have norm : (∑ _ : Perm (Fin m), ∑ _ : Fin n → Fin m, (1:ℝ))=D := by
    simp [D,Fintype.card_perm,nsmul_eq_mul]
  have dpos : 0<D := by dsimp [D];positivity
  change 1-_/D ≤ _
  rw [show (1:ℝ) = D/D from (div_self dpos.ne').symm,←sub_div]
  conv_lhs => lhs; lhs; rw [←norm]
  simp only [←sum_sub_distrib]
  apply (div_le_div_of_nonneg_right (sum_le_sum fun σ _ ↦ sum_le_sum fun b _ ↦ sample_deficit_union hk hu σ b) dpos.le).trans
  have per : (∑ b : Fin n → Fin m, ∑ s : Fin m, (2:ℝ)^k*slotDiscount s b) =
      (m:ℝ)*((2:ℝ)^k*((m:ℝ)-1/2)^n) := by
    rw [sum_comm]
    simp only [←mul_sum,discount_sum,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
    ring
  simp only [per,sum_const,card_univ,Fintype.card_perm,Fintype.card_fin,nsmul_eq_mul,D]
  have helper : (1-1/(2*(m:ℝ)))*m=(m:ℝ)-1/2 := by field_simp
  rw [←helper,mul_pow]
  calc
    _ = (m:ℝ)*((2:ℝ)^k*(1-1/(2*(m:ℝ)))^n) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left (discount_tail_exponential hm size) mp.le

#print axioms original_coefficient_near_full
#print axioms full_cycle_label_lower
#print axioms original_relative_increment_small_load_ratio
#print axioms discount_sum
#print axioms slot_probability_increment_discount
#print axioms original_increment_small_load_ratio
end LongCycleBounds.Occupancy
