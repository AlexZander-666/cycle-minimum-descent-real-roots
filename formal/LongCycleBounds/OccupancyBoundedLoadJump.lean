import LongCycleBounds.OccupancyBinomialJump
import LongCycleBounds.OccupancyLowLoadTransfer
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.Real.Pi.Bounds

/-! A bounds check for the actual two-jump coefficients at bounded km/n.
The Stirling comparison below is the local argument of BandBinomial; its public
shifted balanced result loses uniformity for the unbalanced exponents here. -/
noncomputable section
namespace LongCycleBounds.Occupancy
open Finset Real CycleProfile
private def correction (n : ℕ) : ℝ := Stirling.stirlingSeq n * √2

private theorem correction_lower {n : ℕ} (hn : 0<n) : 2 ≤ correction n := by
  have h := mul_le_mul_of_nonneg_right (Stirling.sqrt_pi_le_stirlingSeq hn.ne') (sqrt_nonneg 2)
  change 2 ≤ Stirling.stirlingSeq n * √2
  apply le_trans _ h
  rw [← sqrt_mul (le_of_lt Real.pi_pos),Real.le_sqrt (by norm_num) (by positivity)]
  linarith [pi_gt_three]

private theorem correction_anti {a n : ℕ} (ha : 0<a) (han : a≤n) :
    correction n ≤ correction a := by
  obtain ⟨b,rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha.ne'
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n≠0 by omega)
  exact mul_le_mul_of_nonneg_right (Stirling.stirlingSeq'_antitone (show b ≤ m by omega)) (sqrt_nonneg 2)

private theorem factorial_unscaled {n : ℕ} (hn : 0<n) :
    (n.factorial:ℝ)*(exp 1)^n = correction n * √(n:ℝ)*(n:ℝ)^n := by
  unfold correction Stirling.stirlingSeq
  rw [sqrt_mul (by norm_num : 0≤(2:ℝ)),div_pow]
  field_simp

private theorem binomial_modal {A B M : ℕ} (hA : 0<A) (hB : 0<B) (hM : A+B=M) :
    2*√(A:ℝ)*√(B:ℝ)*(M.choose A:ℝ)*(A:ℝ)^A*(B:ℝ)^B ≤ √(M:ℝ)*(M:ℝ)^M := by
  have hc : (M.choose A:ℝ)*A.factorial*B.factorial = M.factorial := by
    exact_mod_cast (show M.choose A*A.factorial*B.factorial = M.factorial by
      simpa [show M-A=B by omega] using Nat.choose_mul_factorial_mul_factorial (show A≤M by omega))
  have id : (M.choose A:ℝ)*(correction A*√(A:ℝ)*(A:ℝ)^A)*(correction B*√(B:ℝ)*(B:ℝ)^B) =
      correction M*√(M:ℝ)*(M:ℝ)^M := by
    rw [← factorial_unscaled hA,← factorial_unscaled hB,← factorial_unscaled (show 0<M by omega),
      ← hM,pow_add]
    rw [hM]
    linear_combination ((exp 1)^A*(exp 1)^B)*hc
  have hleft := mul_le_mul_of_nonneg_right (correction_lower hB)
    (show 0 ≤ (M.choose A:ℝ)*√(A:ℝ)*(A:ℝ)^A*√(B:ℝ)*(B:ℝ)^B by positivity)
  have hright := mul_le_mul_of_nonneg_right (correction_anti hA (show A≤M by omega))
    (show 0 ≤ √(M:ℝ)*(M:ℝ)^M by positivity)
  have hcan : 0<correction A := lt_of_lt_of_le (by norm_num) (correction_lower hA)
  apply (mul_le_mul_iff_right₀ hcan).mp
  calc
    _ ≤ (M.choose A:ℝ)*(correction A*√(A:ℝ)*(A:ℝ)^A)*(correction B*√(B:ℝ)*(B:ℝ)^B) := by
      nlinarith only [mul_le_mul_of_nonneg_left hleft hcan.le]
    _ = _ := id
    _ ≤ _ := by linarith only [hright]

/-- Comparing the weighted product at u,v with its optimum at A:B. -/
private theorem weighted_product {A B M : ℕ} (hA : 0<A) (hB : 0<B) (hM : A+B=M)
    {u v : ℝ} (hu : 0<u) (hv : 0<v) :
    u^A*v^B*(M:ℝ)^M ≤ (A:ℝ)^A*(B:ℝ)^B*(u+v)^M := by
  have hMr : (A:ℝ)+B=M := by exact_mod_cast hM
  have hMp : 0<(M:ℝ) := by exact_mod_cast (show 0<M by omega)
  let z := ((M:ℝ)*u)/((A:ℝ)*(u+v))
  let w := ((M:ℝ)*v)/((B:ℝ)*(u+v))
  have hz : 0<z := by dsimp [z]; positivity
  have hw : 0<w := by dsimp [w]; positivity
  have hlin : (A:ℝ)*(z-1)+(B:ℝ)*(w-1)=0 := by dsimp [z,w]; field_simp; nlinarith [hMr]
  have hlog : log (z^A*w^B) ≤ log 1 := by
    rw [log_mul (by positivity) (by positivity),log_pow,log_pow,log_one]
    linarith [mul_le_mul_of_nonneg_left (log_le_sub_one_of_pos hz) (Nat.cast_nonneg A : 0≤(A:ℝ)),
      mul_le_mul_of_nonneg_left (log_le_sub_one_of_pos hw) (Nat.cast_nonneg B : 0≤(B:ℝ))]
  have hzw := (log_le_log_iff (by positivity) zero_lt_one).mp hlog
  dsimp [z,w] at hzw
  rw [div_pow,div_pow,mul_pow,mul_pow,mul_pow,mul_pow] at hzw
  field_simp at hzw
  rw [show (M:ℝ)^M=(M:ℝ)^A*(M:ℝ)^B by rw [← pow_add,hM],
    show (u+v)^M=(u+v)^A*(u+v)^B by rw [← pow_add,hM]]
  linarith only [hzw]

theorem unshifted_binomial_atom {A B M : ℕ} (hA : 0<A) (hB : 0<B) (hM : A+B=M)
    {u v : ℝ} (hu : 0<u) (hv : 0<v) :
    2*√(A:ℝ)*√(B:ℝ)*(M.choose A:ℝ)*(u^A*v^B) ≤ √(M:ℝ)*(u+v)^M := by
  have hMp : (0:ℝ)<M := by exact_mod_cast (show 0<M by omega)
  have h1 := mul_le_mul_of_nonneg_left (weighted_product hA hB hM hu hv)
    (show 0 ≤ 2*√(A:ℝ)*√(B:ℝ)*(M.choose A:ℝ) by positivity)
  have h2 := mul_le_mul_of_nonneg_right (binomial_modal hA hB hM)
    (show 0 ≤ (u+v)^M by positivity)
  apply (mul_le_mul_iff_left₀ (pow_pos hMp M)).mp
  linarith only [h1,h2]


theorem gridBinomial_nonneg (n d m l : ℕ) : 0 ≤ gridBinomial n d m l := by
  unfold gridBinomial
  positivity

/-- A grid point on either boundary contributes zero for interior d. -/
theorem gridBinomial_atom {n d m l : ℕ} (hd : 0 < d) (half : 2*d ≤ n)
    (hm : 0 < m) (hl : l ≤ m) : gridBinomial n d m l ≤ 1/√(d:ℝ) := by
  have bv : 0 < n-d := by omega
  by_cases h0 : l=0
  · simp [gridBinomial,h0,zero_pow hd.ne',(sqrt_pos.mpr (Nat.cast_pos.mpr hd)).le]
  by_cases h1 : l=m
  · simp [gridBinomial,h1,zero_pow bv.ne',(sqrt_pos.mpr (Nat.cast_pos.mpr hd)).le]
  have b := unshifted_binomial_atom hd bv (M:=n) (by omega)
    (u:=(l:ℝ)/m) (v:=((m-l:ℕ):ℝ)/m) (div_pos (by exact_mod_cast (by omega : 0<l)) (by positivity))
    (div_pos (by exact_mod_cast (by omega : 0<(m-l:ℕ))) (by positivity))
  have unit : (l:ℝ)/m+((m-l:ℕ):ℝ)/m=1 := by rw [Nat.cast_sub hl];field_simp;ring
  rw [unit,one_pow,mul_one] at b
  have rad := sqrt_le_sqrt (show (n:ℝ)≤4*((n-d:ℕ):ℝ) by rw [Nat.cast_sub (by omega)]; linarith [show (2:ℝ)*d≤n by exact_mod_cast half])
  rw [sqrt_mul (by norm_num : 0 ≤ (4:ℝ)),show √(4:ℝ)=2 by norm_num] at rad
  apply (le_div_iff₀ (sqrt_pos.mpr (by positivity))).mpr
  apply (mul_le_mul_iff_left₀ (show 0<2*√((n-d:ℕ):ℝ) by positivity)).mp
  unfold gridBinomial
  linarith only [b,rad]

/-- Exponentially small grid mass when the mean is at least four times the specified load. -/
theorem gridBinomial_lower_tail {n m d l : ℕ} (hm : 0 < m) (hl : l ≤ m) (hd : d ≤ n)
    (mean : 4*m*d ≤ n*l) :
    gridBinomial n d m l ≤ exp (-(n:ℝ)*l/(4*m)) := by
  let u : ℝ := (l:ℝ)/m
  let v : ℝ := ((m-l:ℕ):ℝ)/m
  have up : 0≤u := by dsimp [u];positivity
  have vp : 0≤v := by dsimp [v];positivity
  have unit : u+v=1 := by dsimp [u,v]; rw [Nat.cast_sub hl];field_simp;ring
  have term := single_le_sum (s:=range (n+1)) (a:=d)
    (f:=fun i : ℕ ↦ (u/2)^i*v^(n-i)*(n.choose i:ℝ))
    (fun i _ ↦ mul_nonneg (mul_nonneg (pow_nonneg (by positivity) _) (pow_nonneg vp _)) (by positivity))
    (mem_range.mpr (by omega))
  rw [←add_pow] at term
  have gen : gridBinomial n d m l ≤ 2^d*(u/2+v)^n := by
    apply le_trans _ (mul_le_mul_of_nonneg_left term (by positivity : 0≤(2:ℝ)^d))
    change _ ≤ (2:ℝ)^d*((u/2)^d*v^(n-d)*(n.choose d:ℝ))
    change (n.choose d:ℝ)*u^d*v^(n-d) ≤ _
    rw [div_pow u 2 d]
    field_simp
    ring_nf
    exact le_rfl
  have e := Real.add_one_le_exp (-u/2)
  have g : u/2+v ≤ exp (-u/2) := by linarith
  have bound := mul_le_mul (pow_le_pow_left₀ (by norm_num) (show (2:ℝ)≤exp 1 by linarith [Real.add_one_le_exp (1:ℝ)]) d)
    (pow_le_pow_left₀ (by positivity : 0≤u/2+v) g n) (by positivity) (by positivity)
  apply gen.trans (bound.trans ?_)
  rw [←Real.exp_nat_mul,←Real.exp_nat_mul,←Real.exp_add]
  apply Real.exp_le_exp.mpr
  dsimp [u]
  have mp : 0<(m:ℝ) := by exact_mod_cast hm
  have realMean : 4*(m:ℝ)*d≤n*l := by exact_mod_cast mean
  field_simp
  linarith

private theorem residual_cap {v q k : ℕ} {u : ℝ} (hq : 0<q) (hu : u ∈ Set.Icc (0:ℝ) 1) :
    markedSlotProbability q k v u ≤ 1 := by
  cases v with
  | zero => simp [markedSlotProbability,zero_pow hq.ne']
  | succ v => exact slot_probability_le_one (by omega) hu

/-- The tilted, source-normalized coefficient has a uniformly small scaled one-ball
increment in every bounded load-ratio window, for every common mark simultaneously. -/
theorem labelFraction_increment_bounded_load {n m k B : ℕ} (hm : 0 < m) (hk : 2≤k)
    (half : 2*k≤n) (sparse : 4*m≤n) (window : 4*m*k≤n*B)
    {u : ℝ} (hu : u ∈ Set.Icc (0:ℝ) 1) :
    0 ≤ (m:ℝ)*(labelFraction (n+1) k m u-labelFraction n k m u) ∧
    (m:ℝ)*(labelFraction (n+1) k m u-labelFraction n k m u) ≤
      B/√((k-1:ℕ):ℝ)+((m:ℝ)+1)*exp (-(n:ℝ)/(4*m)) := by
  have mp : 0<(m:ℝ) := by exact_mod_cast hm
  simp only [labelFraction,original_profile_eq_slot_probability hm,
    mul_div_cancel_left₀ _ (pow_ne_zero _ mp.ne')]
  refine ⟨mul_nonneg mp.le (sub_nonneg.mpr (markedSlotProbability_mono hm hk hu n)),?_⟩
  let K := k-1
  have kp : 0<K := by dsimp [K];omega
  let e := exp (-(n:ℝ)/(4*m))
  let M := 1/√(K:ℝ)
  have ep : 0≤e := (exp_pos _).le
  have Mpos : 0≤M := by dsimp [M];positivity
  let S := fun d ↦ ∑ l ∈ range (m+1), gridBinomial n d m l*markedSlotProbability (n-d) k (m-l) u
  have each {d l : ℕ} (dn : d < n) :
      gridBinomial n d m l*markedSlotProbability (n-d) k (m-l) u ≤ gridBinomial n d m l :=
    mul_le_of_le_one_right (gridBinomial_nonneg ..) (residual_cap (by omega) hu)
  have tail {d l : ℕ} (dn : d≤n) (lp : 0<l) (lm : l≤ m) (mean : 4*m*d≤n*l) :
      gridBinomial n d m l ≤ e := by
    apply (gridBinomial_lower_tail hm lm dn mean).trans
    apply exp_le_exp.mpr
    apply div_le_div_of_nonneg_right _ (by positivity)
    have lr : 1≤(l:ℝ) := by exact_mod_cast lp
    nlinarith only [mul_le_mul_of_nonneg_left lr (Nat.cast_nonneg n : 0≤(n:ℝ))]
  have one : S 1 ≤ ((m:ℝ)+1)*e := by
    have cap : ∀ l ∈ range (m+1), gridBinomial n 1 m l ≤ e := by
      intro l hl
      by_cases z : l=0
      · simpa [z,gridBinomial] using ep
      apply tail (by omega) (by omega) (by simpa using hl)
      exact (by simpa using sparse : 4*m*1≤n).trans (Nat.le_mul_of_pos_right _ (by omega))
    exact (sum_le_sum (fun l hl ↦ (each (d:=1) (l:=l) (by omega)).trans (cap l hl))).trans_eq (by simp)
  have smallK : S K ≤ (B:ℝ)*M+((m:ℝ)+1)*e := by
    have cap : ∀ l ∈ range (m+1), gridBinomial n K m l ≤ (if l<B then M else 0)+e := by
      intro l hl
      have lm : l≤ m := by simpa using hl
      by_cases inside : l<B
      · rw [if_pos inside]
        exact (gridBinomial_atom kp (by dsimp [K];omega) hm lm).trans (le_add_of_nonneg_right ep)
      · rw [if_neg inside,zero_add]
        have bl := Nat.le_of_not_gt inside
        have bp : 0<B := by by_contra! h; simp [show B=0 by omega] at window;omega
        apply tail (by dsimp [K];omega) (by omega) lm
        exact (Nat.mul_le_mul_left _ (Nat.sub_le k 1)).trans (window.trans (Nat.mul_le_mul_left _ bl))
    have prefixBound : (∑ l ∈ range (m+1), if l<B then M else 0) ≤ (B:ℝ)*M := by
      rw [←sum_filter]
      apply (sum_le_sum_of_subset_of_nonneg (t:=range B) (fun l hl ↦ mem_range.mpr (mem_filter.mp hl).2)
        (fun _ _ _ ↦ Mpos)).trans_eq
      simp
    apply (sum_le_sum fun l hl ↦ (each (d:=K) (l:=l) (by dsimp [K];omega)).trans (cap l hl)).trans
    rw [sum_add_distrib]
    simpa using add_le_add prefixBound (le_refl (((m:ℝ)+1)*e))
  have exactJump := marked_probability_binomial_jump hm hk n u
  rw [exactJump,←mul_assoc,mul_one_div_cancel mp.ne',one_mul]
  change (∑ d ∈ range (n+1), ((if d+1=2 then u else 0)+(if d+1=k then 1-u else 0))*S d) ≤ _
  have fst (d : ℕ) : (d+1=2) ↔ d=1 := by omega
  have snd (d : ℕ) : (d+1=k) ↔ d=K := by dsimp [K];omega
  simp_rw [add_mul,fst,snd,ite_mul,zero_mul]
  rw [sum_add_distrib]
  simp only [sum_ite_eq',mem_range,if_pos (by omega : 1<n+1),if_pos (by dsimp [K];omega : K<n+1)]
  have convex := add_le_add (mul_le_mul_of_nonneg_left one hu.1)
    (mul_le_mul_of_nonneg_left smallK (sub_nonneg.mpr hu.2))
  have nonneg := mul_nonneg hu.1 (mul_nonneg (Nat.cast_nonneg B) Mpos)
  change _ ≤ (B:ℝ)/√(K:ℝ)+((m:ℝ)*e+1*e)
  rw [div_eq_mul_one_div]
  dsimp only [M] at convex nonneg
  linarith only [convex,nonneg]

#print axioms gridBinomial_atom
#print axioms gridBinomial_lower_tail
#print axioms labelFraction_increment_bounded_load
end LongCycleBounds.Occupancy
