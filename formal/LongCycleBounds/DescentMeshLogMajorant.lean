import LongCycleBounds.DescentMeshDivisors
import LongCycleBounds.DescentMeshConstants

/-! Absolute logarithmic cost at a finite rectangular truncation of the necklace product. -/
noncomputable section
namespace LongCycleBounds.DescentMesh
open Finset ArithmeticFunction
open scoped Moebius

def repeatedCost (j b : ℕ) (v : ℝ) : ℝ :=
  (∑ d ∈ j.divisors, |(μ d : ℝ)| * v^(j*b-j/d)) / ((j:ℝ)*b)

theorem repeatedCost_le {j b : ℕ} (hj : 0 < j) (hb : 2 ≤ b) {v : ℝ}
    (hv : 0 ≤ v) (h1 : v ≤ 1) : repeatedCost j b v ≤ (1/2:ℝ)*(v^j)^(b-1) := by
  have jp : 0 < (j:ℝ) := by exact_mod_cast hj
  have bp : (2:ℝ) ≤ b := by exact_mod_cast hb
  have cc : j.divisors.card ≤ j := by
    have hs : j.divisors ⊆ Icc 1 j := fun d hd ↦ mem_Icc.mpr
      ⟨Nat.pos_of_mem_divisors hd, Nat.le_of_dvd hj (Nat.dvd_of_mem_divisors hd)⟩
    simpa using card_le_card hs
  have cr : (j.divisors.card:ℝ) ≤ j := by exact_mod_cast cc
  have hx : 0 ≤ (v^j)^(b-1) := pow_nonneg (pow_nonneg hv _) _
  have hh (d : ℕ) (_ : d ∈ j.divisors) :
      |(μ d:ℝ)| * v^(j*b-j/d) ≤ (v^j)^(b-1) := by
    have sm : j*(b-1) ≤ j*b-j/d := by
      rw [Nat.mul_sub, Nat.mul_one]
      exact Nat.sub_le_sub_left (Nat.div_le_self _ _) _
    have am : |(μ d:ℝ)| ≤ 1 := by exact_mod_cast (abs_moebius_le_one (n:=d))
    rw [← pow_mul]
    calc
      _ ≤ 1 * v^(j*b-j/d) := mul_le_mul_of_nonneg_right am (pow_nonneg hv _)
      _ ≤ _ := by simpa using pow_le_pow_of_le_one hv h1 sm
  have sm := sum_le_sum hh
  simp only [sum_const, nsmul_eq_mul] at sm
  apply (div_le_iff₀ (mul_pos jp (by linarith : 0<(b:ℝ)))).mpr
  have h' := sm.trans (mul_le_mul_of_nonneg_right cr hx)
  nlinarith only [h',mul_nonneg (mul_nonneg jp.le hx) (sub_nonneg.mpr bp)]

private def primitiveReserve (v : ℝ) (m : ℕ) : ℝ :=
  (v^((8+m)/2)+v^((9+m)/2))/(2*(1-v))

private theorem primitive_step {v : ℝ} (hv : 0≤v) (h1 : v<1) (m : ℕ) :
    primitiveCost (m+8) v + primitiveReserve v (m+1) ≤ primitiveReserve v m := by
  have h := primitiveCost_le (j:=m+8) (by omega) hv h1.le
  have e := pow_le_pow_of_le_one hv h1.le (show (8+m)/2 ≤ (m+8+1)/2 by omega)
  have a : primitiveCost (m+8) v ≤ (1/2:ℝ)*v^((8+m)/2) :=
    h.trans (mul_le_mul_of_nonneg_left e (by norm_num))
  have eq : primitiveReserve v m - primitiveReserve v (m+1) = (1/2:ℝ)*v^((8+m)/2) := by
    unfold primitiveReserve
    rw [show (8+(m+1))/2=(9+m)/2 by omega, show (9+(m+1))/2=(8+m)/2+1 by omega, pow_succ]
    field_simp [sub_ne_zero.mpr h1.ne']
    ring
  linarith

theorem primitive_tail_bound (M : ℕ) {v : ℝ} (hv : 0≤v) (h1 : v<1) :
    (∑ m ∈ range M, primitiveCost (m+8) v) ≤ v^4/(1-v) := by
  have h (N : ℕ) : (∑ m ∈ range N, primitiveCost (m+8) v) + primitiveReserve v N
      ≤ primitiveReserve v 0 := by
    induction N with
    | zero => simp
    | succ N ih =>
      rw [sum_range_succ]
      linarith only [ih,primitive_step hv h1 N]
  have nonneg : 0 ≤ primitiveReserve v M := by unfold primitiveReserve; positivity
  have base : primitiveReserve v 0 = v^4/(1-v) := by
    change (v^4+v^4)/(2*(1-v)) = v^4/(1-v)
    field_simp [sub_ne_zero.mpr h1.ne']
    ring
  linarith only [h M,nonneg,base]

private theorem geometric_sum_bound {a : ℝ} (ha : 0 ≤ a) (h1 : a < 1) (N : ℕ) :
    (∑ i ∈ range N, a^i) ≤ 1/(1-a) := by
  have z : (∑ i ∈ range N, a^i)*(1-a) = 1-a^N := geom_sum_mul_neg a N
  apply (le_div_iff₀ (sub_pos.mpr h1)).mpr
  linarith only [z, pow_nonneg ha N]

theorem repeat_truncation_bound (M B : ℕ) {v : ℝ} (hv : 0 ≤ v) (h1 : v < 1) :
    (∑ i ∈ range M, ∑ t ∈ range B, repeatedCost (i+3) (t+2) v) ≤
      v^3/(2*(1-v)*(1-v^3)) := by
  have h3 : v^3 < 1 := pow_lt_one₀ hv h1 (by decide)
  have single (i : ℕ) : (∑ t ∈ range B, repeatedCost (i+3) (t+2) v) ≤
      (v^3/(2*(1-v^3))) * v^i := by
    let a := v^(i+3)
    have a0 : 0 ≤ a := pow_nonneg hv _
    have a3 : a ≤ v^3 := pow_le_pow_of_le_one hv h1.le (by omega)
    have bnd (t : ℕ) (_ : t ∈ range B) : repeatedCost (i+3) (t+2) v ≤ (a/2)*a^t := by
      have h := repeatedCost_le (j:=i+3) (b:=t+2) (by omega) (by omega) hv h1.le
      simpa [show t+2-1=t+1 by omega,pow_succ,a,div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using h
    have h := sum_le_sum bnd
    rw [← mul_sum] at h
    have hh := mul_le_mul_of_nonneg_left (geometric_sum_bound a0 (a3.trans_lt h3) B)
      (show 0≤a/2 by positivity)
    have hi : (1:ℝ)/(1-a) ≤ 1/(1-v^3) :=
      one_div_le_one_div_of_le (by linarith) (by linarith)
    calc
      _ ≤ (a/2)*(1/(1-v^3)) := (h.trans hh).trans (mul_le_mul_of_nonneg_left hi (by positivity))
      _ = _ := by dsimp [a]; rw [pow_add]; field_simp [sub_ne_zero.mpr h3.ne']
  have h := sum_le_sum (fun i (_ : i ∈ range M) ↦ single i)
  rw [← mul_sum] at h
  have fin := geometric_sum_bound hv h1 M
  have hh := mul_le_mul_of_nonneg_left fin (show 0≤v^3/(2*(1-v^3)) by positivity)
  calc
    _ ≤ _ := h.trans hh
    _ = _ := by field_simp [sub_ne_zero.mpr h1.ne',sub_ne_zero.mpr h3.ne']

private theorem primitive_nonneg (j : ℕ) {v : ℝ} (hv : 0 ≤ v) : 0 ≤ primitiveCost j v := by
  unfold primitiveCost
  positivity

private theorem repeat_nonneg (j b : ℕ) {v : ℝ} (hv : 0 ≤ v) : 0 ≤ repeatedCost j b v := by
  unfold repeatedCost
  positivity

/-- Every cutoff and finite primitive/repetition box of the actual Möbius logarithm.
The larger box may include repetitions of length exceeding the target degree. -/
theorem bad_log_majorant {k : ℕ} (hk : 3 ≤ k) (N B : ℕ) {v : ℝ}
    (hv : 0 ≤ v) (h1 : v < 1) :
    (∑ j ∈ Icc k N, (primitiveCost j v + ∑ b ∈ Icc 2 B, repeatedCost j b v)) ≤
      badEnvelope v := by
  let costs (j : ℕ) := primitiveCost j v + ∑ b ∈ Icc 2 B, repeatedCost j b v
  have cp (j : ℕ) : 0 ≤ costs j := add_nonneg (primitive_nonneg j hv)
    (sum_nonneg (fun b _ ↦ repeat_nonneg j b hv))
  have sub : Icc k N ⊆ Ico 3 (N+8) := by
    intro j hj
    obtain ⟨_,_⟩ := mem_Icc.mp hj
    exact mem_Ico.mpr ⟨by omega,by omega⟩
  have h := @sum_le_sum_of_subset_of_nonneg ℕ ℝ _ _ costs _ _ _ sub (fun j _ _ ↦ cp j)
  rw [sum_Ico_eq_sum_range, show N+8-3=5+N by omega] at h
  change (∑ j ∈ Icc k N, costs j) ≤ _
  apply h.trans
  dsimp only [costs]
  rw [sum_add_distrib, sum_range_add (fun i ↦ primitiveCost (3+i) v) 5 N]
  have ta : (∑ i ∈ range N, primitiveCost (3+(5+i)) v) ≤ v^4/(1-v) := by
    simpa only [show ∀ i:ℕ, 3+(5+i)=i+8 by omega] using primitive_tail_bound N hv h1
  have rep (j : ℕ) :
      (∑ b ∈ Icc 2 B, repeatedCost j b v) = ∑ b ∈ range (B+1-2), repeatedCost j (b+2) v := by
    rw [show Icc 2 B=Ico 2 (B+1) by ext b; simp, sum_Ico_eq_sum_range]
    simp [Nat.add_comm]
  simp_rw [rep]
  have tt : (∑ i ∈ range (5+N), ∑ b ∈ range (B+1-2), repeatedCost (3+i) (b+2) v) ≤
        v^3/(2*(1-v)*(1-v^3)) := by
    simpa only [show ∀ i:ℕ, 3+i=i+3 by omega] using repeat_truncation_bound (5+N) (B+1-2) hv h1
  obtain ⟨s3,s4,s5,s6,s7⟩ := primitiveCost_small v
  norm_num [sum_range_succ,s3,s4,s5,s6,s7,badEnvelope] at ⊢
  linarith only [ta,tt]

#print axioms repeatedCost_le
#print axioms primitive_tail_bound
#print axioms repeat_truncation_bound
#print axioms bad_log_majorant
end LongCycleBounds.DescentMesh
