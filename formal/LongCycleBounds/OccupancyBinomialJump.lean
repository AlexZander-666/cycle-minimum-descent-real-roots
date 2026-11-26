import LongCycleBounds.OccupancyMarkedVerified

/-! A binomial-grid decomposition of the adjacent true marked label coefficients. -/
noncomputable section
namespace LongCycleBounds.Occupancy
open Finset PowerSeries CycleProfile
open scoped Classical

/-- Ordinary Euler operator in the slot variable, leaving ball weights untouched. -/
def markSlot (F : SlotBallSeries) : SlotBallSeries := mk fun m ↦ (m:PowerSeries ℝ)*coeff m F

@[simp] theorem coeff_markSlot (F : SlotBallSeries) (m : ℕ) :
    coeff m (markSlot F)=(m:PowerSeries ℝ)*coeff m F := coeff_mk ..

private theorem markSlot_mul (F G : SlotBallSeries) :
    markSlot (F*G)=markSlot F*G+F*markSlot G := by
  ext1 m
  simp only [coeff_markSlot,map_add,coeff_mul,Nat.sum_antidiagonal_eq_sum_range_succ_mk,mul_sum,←sum_add_distrib]
  apply sum_congr rfl
  intro i hi
  have le : i ≤ m := by simpa using hi
  have eq : (m:PowerSeries ℝ)=i+((m-i:ℕ):PowerSeries ℝ) := by
    rw [←Nat.cast_add, Nat.add_sub_of_le le]
  rw [eq]
  ring

private theorem markSlot_pow_succ (F : SlotBallSeries) (h : ℕ) :
    markSlot (F^(h+1)) = (h+1:ℕ)*markSlot F*F^h := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [pow_succ F (h+1),markSlot_mul,ih,pow_succ F h]
    push_cast
    ring

private theorem orbit_power_high {m h : ℕ} (too : m < h) (k : ℕ) (u : ℝ) :
    coeff m ((orbitSeries k u)^h)=0 := by
  rw [coeff_orbitSeries_pow]
  apply sum_eq_zero
  intro l hl
  obtain ⟨ha,pos⟩ := mem_filter.mp hl
  have total : (∑ i, l i)=m := (mem_piAntidiag.mp ha).1
  have small : h ≤ m := by simpa using (calc
    (∑ _ : Fin h, (1:ℕ)) ≤ ∑ i, l i := sum_le_sum fun i _ ↦ pos i
    _ = m := total)
  exact (Nat.not_le.mpr too small).elim

private theorem padded_slotIndex {m N : ℕ} (bound : m ≤ N) (k : ℕ) (u : ℝ) :
    (∑ h ∈ range (N+1), C (1/(h.factorial:ℝ))*coeff m ((orbitSeries k u)^h)) =
      slotIndexSeries k u m := by
  unfold slotIndexSeries
  symm
  apply sum_subset (range_subset_range.mpr (by omega))
  intro h _ hh
  rw [orbit_power_high (by have := not_lt.mp (fun low ↦ hh (mem_range.mpr low));omega),mul_zero]

private theorem slot_level (k m h : ℕ) (u : ℝ) :
    (m:PowerSeries ℝ)*(C (1/((h+1).factorial:ℝ))*coeff m ((orbitSeries k u)^(h+1))) =
      ∑ l ∈ range (m+1), coeff l (markSlot (orbitSeries k u))*
        (C (1/(h.factorial:ℝ))*coeff (m-l) ((orbitSeries k u)^h)) := by
  rw [mul_left_comm,←coeff_markSlot,markSlot_pow_succ]
  rw [mul_assoc,←nsmul_eq_mul,map_nsmul,nsmul_eq_mul,coeff_mul,Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have scalar : C (1/((h+1).factorial:ℝ))*((h+1:ℕ):PowerSeries ℝ) = C (1/(h.factorial:ℝ)) := by
    rw [←map_natCast (C (R:=ℝ)),←map_mul]
    congr 1
    rw [Nat.factorial_succ,Nat.cast_mul]
    have : ((h+1:ℕ):ℝ)≠0 := by positivity
    field_simp
  rw [←mul_assoc,scalar,mul_sum]
  apply sum_congr rfl
  intro l _
  ring

/-- Distinguishing an arbitrary slot marks its unique orbit, with size l multiplicity. -/
theorem remove_selected_slot (k m : ℕ) (u : ℝ) :
    (m:PowerSeries ℝ)*slotIndexSeries k u m =
      ∑ l ∈ range (m+1), coeff l (markSlot (orbitSeries k u))*slotIndexSeries k u (m-l) := by
  have ext := padded_slotIndex (m:=m) (N:=m+1) (by omega) k u
  rw [←ext,mul_sum,sum_range_succ']
  have z : (m:PowerSeries ℝ)*(C (1/((0:ℕ).factorial:ℝ))*coeff m (orbitSeries k u^0))=0 := by
    by_cases hm : m=0 <;> simp [coeff_one,hm]
  rw [z,add_zero]
  simp_rw [slot_level]
  rw [sum_comm]
  apply sum_congr rfl
  intro l _
  rw [←mul_sum,padded_slotIndex (Nat.sub_le m l)]

private theorem pointedSlot_coeff (k d l : ℕ) (u : ℝ) :
    coeff d (coeff l (markSlot (orbitSeries k u))) = loadMark k u d*(l:ℝ)^d/d.factorial := by
  simp only [coeff_markSlot,orbitSeries,coeff_mk,←mul_assoc]
  rw [←map_natCast (C (R:=ℝ)) l,←map_mul,coeff_C_mul]
  by_cases hl : l=0
  · subst l
    by_cases hd : d=0 <;> simp [hd,loadMark]
  · have lp : (l:ℝ)≠0 := by exact_mod_cast hl
    simp [lp,orbitBallSeries]

/-- The difference of the distinguished-ball and distinguished-slot kernels at old load d. -/
theorem orbit_jump_coeff {k : ℕ} (hk : 2 ≤ k) (d l : ℕ) (u : ℝ) :
    coeff d (coeff l (markBall (orbitSeries k u))-coeff l (markSlot (orbitSeries k u))) =
      ((if d+1=2 then u else 0)+(if d+1=k then 1-u else 0))*(l:ℝ)^d/d.factorial := by
  rw [map_sub,coeff_removed_orbit,pointedSlot_coeff,←loadMark_succ_sub hk]
  by_cases hz : d=0
  · simp [hz,loadMark]
  · rw [if_neg hz]
    have e : loadMark k u (d+1) = profile k u (d+1) := by simp [loadMark,profile,show ¬d+1<2 by omega]
    rw [e]
    ring

/-- Source-level marked orbit deletion retaining the residual array at exactly n-d balls and m-l slots. -/
theorem weighted_label_jump_convolution {k : ℕ} (hk : 2 ≤ k) (n m : ℕ) (u : ℝ) :
    markedOrbitCount k u (n+1) m - m*markedOrbitCount k u n m =
      ∑ d ∈ range (n+1), ((if d+1=2 then u else 0)+(if d+1=k then 1-u else 0))*(n.choose d:ℝ)*
        ∑ l ∈ range (m+1), (l:ℝ)^d*markedOrbitCount k u (n-d) (m-l) := by
  have delta := congrArg₂ (·-·) (remove_marked_orbit k m u) (remove_selected_slot k m u)
  rw [←sum_sub_distrib] at delta
  simp_rw [←sub_mul] at delta
  have eq := congrArg (coeff n) delta
  simp only [map_sub,coeff_derivative,map_sum] at eq
  rw [←map_natCast (C (R:=ℝ)) m,coeff_C_mul] at eq
  simp_rw [coeff_mul,Nat.sum_antidiagonal_eq_sum_range_succ_mk,orbit_jump_coeff hk] at eq
  rw [sum_comm] at eq
  unfold markedOrbitCount
  rw [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,
    show ∀ a b:ℝ,((n:ℝ)+1)*n.factorial*a-m*(n.factorial*b)=n.factorial*(a*((n:ℝ)+1)-m*b) by intros;ring,eq,mul_sum]
  apply sum_congr rfl
  intro d hd
  rw [mul_sum,mul_sum]
  apply sum_congr rfl
  intro l _
  have le : d≤n := by simpa using hd
  have cs : (n.choose d:ℝ)*d.factorial*(n-d).factorial=n.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial le
  rw [←cs]
  have dn : (d.factorial:ℝ)≠0 := by positivity
  field_simp

/-- A binomial point mass on the finite grid of slot fractions, with natural residual slot count. -/
def gridBinomial (n d m l : ℕ) : ℝ :=
  (n.choose d:ℝ)*((l:ℝ)/m)^d*(((m-l:ℕ):ℝ)/m)^(n-d)

/-- Normalized exact two-jump convolution including the whole-cycle and zero-ball boundaries. -/
theorem marked_probability_binomial_jump {m k : ℕ} (hm : 0 < m) (hk : 2 ≤ k) (n : ℕ) (u : ℝ) :
    markedSlotProbability (n+1) k m u-markedSlotProbability n k m u =
      (1/(m:ℝ))*∑ d ∈ range (n+1),
        ((if d+1=2 then u else 0)+(if d+1=k then 1-u else 0))*
          ∑ l ∈ range (m+1), gridBinomial n d m l*markedSlotProbability (n-d) k (m-l) u := by
  have count (j l : ℕ) : markedOrbitCount k u j l=(l:ℝ)^j*markedSlotProbability j k l u :=
    (equals_anchoredLabel_of_split (profile k u) (markedOrbitCount k u)
      (markedOrbitCount_seed k u) (fun n l ↦ markedOrbitCount_remove n l k u) j l).trans
      (original_profile_eq_slot_probability_all j k l u)
  have raw := weighted_label_jump_convolution hk n m u
  simp_rw [count] at raw
  have mp : (m:ℝ)≠0 := by exact_mod_cast hm.ne'
  apply mul_left_cancel₀ (pow_ne_zero (n+1) mp)
  rw [mul_sub,show (m:ℝ)^(n+1)*markedSlotProbability n k m u =
    m*((m:ℝ)^n*markedSlotProbability n k m u) by rw [pow_succ];ring,raw,
    ←mul_assoc ((m:ℝ)^(n+1)),show (m:ℝ)^(n+1)*(1/m)=m^n by rw [pow_succ];field_simp,mul_sum]
  apply sum_congr rfl
  intro d hd
  rw [mul_assoc]
  conv_rhs => rw [mul_left_comm]
  congr 1
  rw [mul_sum,mul_sum]
  apply sum_congr rfl
  intro l _
  have split : (m:ℝ)^n=(m:ℝ)^d*(m:ℝ)^(n-d) := by
    rw [←pow_add,Nat.add_sub_of_le (by simpa using hd)]
  unfold gridBinomial
  rw [split,div_pow,div_pow]
  field_simp

#print axioms marked_probability_binomial_jump
#print axioms orbit_jump_coeff
#print axioms weighted_label_jump_convolution
end LongCycleBounds.Occupancy
