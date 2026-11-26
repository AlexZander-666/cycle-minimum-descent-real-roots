import LongCycleBounds.OccupancyCommonMark
import LongCycleBounds.CycleProfileEGF
import LongCycleBounds.CycleProfileNormalization

/-! An anchored positive-label recursion for the original weighted permutation row. -/
noncomputable section
namespace LongCycleBounds.Occupancy
open Finset CycleProfile

/-- The cycle containing a distinguished ball has d other balls and consumes l positive labels. -/
def anchoredLabel (w : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, m => if m=0 then 1 else 0
  | n+1, m => ∑ d ∈ range (n+1), if d=0 then 0 else
      (n.choose d:ℝ)*w (d+1)*
        ∑ l ∈ range (m+1), (l:ℝ)^d*anchoredLabel w (n-d) (m-l)
termination_by n _ => n
decreasing_by omega

/-- The recursion gives the actual power-series coefficients for arbitrary signed cycle weights. -/
theorem weightedRow_hasSum_anchoredLabel (w : ℕ → ℝ) (n : ℕ) {t : ℝ} (ht : ‖t‖ < 1) :
    HasSum (fun m ↦ t^m*anchoredLabel w n m) ((row n w).eval t/(1-t)^n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero =>
      have eq := egf_constant w t
      simp only [egf, PowerSeries.coeff_mk,Nat.factorial_zero,Nat.cast_one,div_one] at eq
      rw [eq,pow_zero,div_one]
      have base := hasSum_single 0 (f:=fun m ↦ t^m*anchoredLabel w 0 m) (fun m hm ↦ by simp [anchoredLabel,hm])
      simpa only [pow_zero,one_mul,anchoredLabel,if_true] using base
    | succ n =>
      let F (d m : ℕ) : ℝ := if d=0 then 0 else (n.choose d:ℝ)*w (d+1)*
          ∑ l ∈ range (m+1), (l:ℝ)^d*anchoredLabel w (n-d) (m-l)
      have per (d : ℕ) (hd : d ∈ range (n+1)) : HasSum (fun m ↦ t^m*F d m)
          ((n.choose d:ℝ)*cycleDerivativeCoeff w t d*(row (n-d) w).eval t/(1-t)^(n+1)) := by
        by_cases dz : d=0
        · simp [F,cycleDerivativeCoeff,dz]
        have ds : 1 ≤ d := by omega
        have dn : d ≤ n := by simpa using hd
        have pre := ih (n-d) (by omega)
        have single := (summable_pow_mul_geometric_of_norm_lt_one d ht).hasSum
        rw [←eulerian_eq_powerSeries d ds t ht] at single
        have conv := hasSum_sum_range_mul_of_summable_norm single.summable.norm pre.summable.norm
        rw [single.tsum_eq,pre.tsum_eq] at conv
        have joined := conv.mul_left ((n.choose d:ℝ)*w (d+1))
        have den : (1-t)^(n+1)=(1-t)^(d+1)*(1-t)^(n-d) := by
          rw [←pow_add];congr 1;omega
        rw [cycleDerivativeCoeff,if_neg dz,den]
        convert! joined.congr_fun (g:=fun m ↦ t^m*F d m) ?_ using 1
        · simp only [div_eq_mul_inv,mul_inv_rev]; ring
        · intro m
          simp only [F,if_neg dz]
          rw [mul_left_comm, mul_sum]
          congr 1
          apply sum_congr rfl
          intro l hl
          have power : t^m=t^l*t^(m-l) := by
            rw [←pow_add, Nat.add_sub_of_le (by have := mem_range.mp hl;omega)]
          rw [power]
          ring
      have res := hasSum_sum per
      rw [row_succ_eval,sum_div]
      apply res.congr_fun
      intro m
      rw [anchoredLabel,mul_sum]

/-- Empty-slot residual needed when the distinguished orbit exhausts the slots. -/
theorem anchoredLabel_no_slots (w : ℕ → ℝ) (n : ℕ) :
    anchoredLabel w n 0 = if n=0 then 1 else 0 := by
  cases n with
  | zero => simp [anchoredLabel]
  | succ n =>
    rw [anchoredLabel]
    simp only [zero_add, sum_range_one, Nat.cast_zero, Nat.reduceSub, Nat.succ_ne_zero,if_false]
    apply sum_eq_zero
    intro d _
    split_ifs with dz
    · rfl
    · simp [zero_pow dz]

theorem anchoredLabel_single_slot (w : ℕ → ℝ) {n : ℕ} (hn : 2 ≤ n) :
    anchoredLabel w n 1 = w n := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n≠0 by omega)
  have jnz : j ≠ 0 := by omega
  rw [anchoredLabel,sum_eq_single_of_mem j (mem_range.mpr (Nat.lt_succ_self j))]
  · simp [jnz,sum_range_succ,anchoredLabel]
  · intro d hd dn
    by_cases dz : d=0
    · simp [dz]
    · have diff : j-d ≠ 0 := by have := mem_range.mp hd;omega
      simp [dz,sum_range_succ,anchoredLabel_no_slots,diff]

/-- When there is one slot there is one orbit and all balls land on it. -/
theorem markedSlotProbability_single_slot (n k : ℕ) (u : ℝ) :
    markedSlotProbability n k 1 u = loadMark k u n := by
  classical
  let σ : Equiv.Perm (Fin 1) := 1
  let τ : Tag σ := tag σ 0
  have single (t : Tag σ) : t=τ := by
    cases t with
    | inl i =>
      have ti : (i:Fin 1)=0 := Subsingleton.elim _ _
      change Sum.inl i = tag σ 0
      rw [tag,dif_pos (show σ 0=0 from rfl)]
      exact congrArg Sum.inl (Subtype.ext ti)
    | inr v =>
      have bad := v.property
      simp [σ] at bad
  let _ : Unique (Tag σ) := ⟨⟨τ⟩,single⟩
  have each (b : Fin n → Fin 1) : slotWeight k u σ b = loadMark k u n := by
    rw [slotWeight,Fintype.prod_unique]
    congr 1
    have eq (i : Fin n) : tag σ (b i) = default := single _
    simp [counts,eq]
  have all (p : Equiv.Perm (Fin 1)) (b : Fin n → Fin 1) : slotWeight k u p b = loadMark k u n := by
    rw [Subsingleton.elim p σ]
    exact each b
  simp [markedSlotProbability,all]

/-- A direct check of a genuine non-endpoint coefficient, uniformly in the real mark. -/
theorem original_profile_one_label {n k : ℕ} (hn : 2 ≤ n) (u : ℝ) :
    anchoredLabel (profile k u) n 1 = markedSlotProbability n k 1 u := by
  rw [anchoredLabel_single_slot _ hn,markedSlotProbability_single_slot]
  simp [profile,loadMark,not_lt.mpr hn]

/-- The series of actual marked rows in the same analytic coordinate as the central and exterior proofs. -/
theorem normalized_profile_hasSum {x : ℝ} (hx : 0 < x) (n k : ℕ) (u : ℝ) :
    HasSum (fun m ↦ (-Real.exp (-x))^m * anchoredLabel (profile k u) n m)
      (normalizedRow (profile k u) n x) := by
  apply weightedRow_hasSum_anchoredLabel
  rw [norm_neg,Real.norm_of_nonneg (Real.exp_nonneg _),Real.exp_lt_one_iff]
  linarith

/-- Any finite counting model satisfying the anchored cycle split gives the genuine label
coefficients in every size. Both the zero-ball seed and the zero-slot residual are included. -/
theorem equals_anchoredLabel_of_split (w : ℕ → ℝ) (Z : ℕ → ℕ → ℝ)
    (seed : ∀ m, Z 0 m = if m=0 then 1 else 0)
    (split : ∀ n m, Z (n+1) m =
      ∑ d ∈ range (n+1), if d=0 then 0 else (n.choose d:ℝ)*w (d+1)*
        ∑ l ∈ range (m+1), (l:ℝ)^d*Z (n-d) (m-l)) :
    ∀ n m, Z n m = anchoredLabel w n m := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simpa only [anchoredLabel] using seed
    | succ n =>
      intro m
      rw [split,anchoredLabel]
      apply sum_congr rfl
      intro d _
      simp_rw [ih (n-d) (by omega)]

/-- The slot choice and cycle symmetry reduce the contribution of a length l orbit
carrying d+1 balls to the d-th power of l after division by all m! slot permutations. -/
theorem anchor_slot_factor {m l : ℕ} (hl : 0 < l) (hm : l ≤ m) (d : ℕ) :
    (m.choose l:ℝ)*((l-1).factorial:ℝ)*((m-l).factorial:ℝ)*(l:ℝ)^(d+1)/m.factorial =
      (l:ℝ)^d := by
  have natEq := Nat.choose_mul_factorial_mul_factorial hm
  rw [←Nat.mul_factorial_pred hl.ne'] at natEq
  have eq : (m.choose l:ℝ)*((l:ℝ)*(l-1).factorial)*(m-l).factorial=m.factorial := by exact_mod_cast natEq
  apply (div_eq_iff (by positivity : (m.factorial:ℝ)≠0)).mpr
  rw [pow_succ,←eq]
  ring

#print axioms anchor_slot_factor
#print axioms normalized_profile_hasSum
#print axioms equals_anchoredLabel_of_split
#print axioms weightedRow_hasSum_anchoredLabel
#print axioms anchoredLabel_no_slots
#print axioms original_profile_one_label
end LongCycleBounds.Occupancy
