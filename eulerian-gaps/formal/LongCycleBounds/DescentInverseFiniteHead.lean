import LongCycleBounds.DescentInverseTwoRadii

namespace LongCycleBounds.DescentMesh.InverseHead
open Finset ArithmeticFunction Real
open scoped Moebius

/-- Zero Möbius mass at multiples of 4 or 9 is enough for this majorant. -/
def ds (j : ℕ) := (range (j+1)).filter (fun d ↦ d ≠ 0 ∧ j % d = 0 ∧ d % 4 ≠ 0 ∧ d % 9 ≠ 0)

def headQ (v : ℚ) (j : ℕ) : ℚ :=
  (∑ d ∈ (ds j).erase 1, v^(j-j/d))/(j:ℚ) +
  (∑ d ∈ ds j, v^(2*j-j/d))/(2*(j:ℚ)*(1-v^8))

private theorem ds_of_ne {j d : ℕ} (hj : 0<j) (hd : d ∈ j.divisors) (hμ : μ d ≠ 0) : d∈ds j := by
  have sf : Squarefree d := by
    by_contra hn
    exact hμ (moebius_eq_zero_of_not_squarefree hn)
  have h := Nat.squarefree_iff_prime_squarefree.mp sf
  simpa only [ds,mem_filter,mem_range] using
    (show d<j+1 ∧ d≠0 ∧ j%d=0 ∧ d%4≠0 ∧ d%9≠0 from
    ⟨Nat.lt_succ_of_le (Nat.le_of_dvd hj (Nat.dvd_of_mem_divisors hd)),
     (Nat.pos_of_mem_divisors hd).ne',Nat.dvd_iff_mod_eq_zero.mp (Nat.dvd_of_mem_divisors hd),
     fun x ↦ h 2 (by decide) (Nat.dvd_iff_mod_eq_zero.mpr x),
     fun x ↦ h 3 (by decide) (Nat.dvd_iff_mod_eq_zero.mpr x)⟩)

private theorem sum_le_clean (S T : Finset ℕ) (f : ℕ→ℝ) (hpos : ∀ d,0≤f d)
    (hmem : ∀ d∈S,μ d ≠ 0 → d∈T) :
    (∑ d ∈ S, |(μ d : ℝ)| * f d) ≤ ∑ d ∈ T, f d := by
  classical
  let q := fun d : ℕ ↦ |(μ d:ℝ)| * f d
  have nonzero (d : ℕ) (hd : d∈S) (hq : q d ≠ 0) : d∈T := by
    apply hmem d hd
    intro hz
    exact hq (by simp [q,hz])
  change (∑ d ∈ S,q d) ≤ _
  rw [←sum_filter_of_ne nonzero]
  refine (sum_le_sum fun d _ ↦ mul_le_of_le_one_left (hpos d) ?_).trans ?_
  · exact_mod_cast abs_moebius_le_one (n:=d)
  · exact sum_le_sum_of_subset_of_nonneg (fun d hd ↦ (mem_filter.mp hd).2) (fun d _ _ ↦ hpos d)

private theorem geom {v : ℝ} (v0 : 0≤v) (v1 : v<1) (N : ℕ) :
    (∑ i∈range N,v^i) ≤ 1/(1-v) := by
  apply (le_div_iff₀ (sub_pos.mpr v1)).mpr
  rw [geom_sum_mul_neg]
  linarith only [pow_nonneg v0 N]

theorem cost_le_head {v : ℚ} (hv : 0≤v) (h1 : v<1) {j : ℕ} (hj : 8≤j) (B : ℕ) :
    primitiveCost j v + (∑ b∈Icc 2 B,repeatedCost j b v) ≤ (headQ v j:ℝ) := by
  have v0 : 0≤(v:ℝ) := by exact_mod_cast hv
  have v1 : (v:ℝ)<1 := by exact_mod_cast h1
  have jp : 0<(j:ℝ) := by exact_mod_cast (by omega : 0<j)
  let S : ℝ := ∑ d∈ds j,(v:ℝ)^(2*j-j/d)
  have S0 : 0≤S := sum_nonneg fun _ _ ↦ pow_nonneg v0 _
  have a0 : 0≤(v:ℝ)^j := pow_nonneg v0 _
  have a8 : (v:ℝ)^j ≤ (v:ℝ)^8 := pow_le_pow_of_le_one v0 v1.le hj
  have a1 : (v:ℝ)^8<1 := pow_lt_one₀ v0 v1 (by decide)
  have prim := sum_le_clean (j.divisors.erase 1) ((ds j).erase 1)
    (fun d ↦ (v:ℝ)^(j-j/d)) (fun _ ↦ pow_nonneg v0 _) (fun d hd hm ↦
      mem_erase.mpr ⟨(mem_erase.mp hd).1,ds_of_ne (by omega) (mem_erase.mp hd).2 hm⟩)
  have rep (t : ℕ) : repeatedCost j (2+t) v ≤ S/(2*(j:ℝ))*((v:ℝ)^j)^t := by
    have ex (d : ℕ) : j*(2+t)-j/d = (2*j-j/d)+j*t := by
      rw [Nat.mul_add,Nat.mul_comm j 2]
      have := Nat.div_le_self j d
      omega
    have cl := sum_le_clean j.divisors (ds j) (fun d ↦ (v:ℝ)^(2*j-j/d))
      (fun _ ↦ pow_nonneg v0 _) (fun _ hd hm ↦ ds_of_ne (by omega) hd hm)
    unfold repeatedCost
    simp only [ex,pow_add,pow_mul,←mul_assoc,←sum_mul]
    rw [div_le_iff₀ (by positivity)]
    have ht : (2:ℝ) ≤ ((2+t:ℕ):ℝ) := by exact_mod_cast (by omega : 2≤2+t)
    have main := mul_le_mul_of_nonneg_right cl (pow_nonneg a0 t)
    change _ ≤ S*_ at main
    have non := div_nonneg S0 (by positivity : 0≤2*(j:ℝ))
    apply main.trans
    calc
      _ = S/(2*(j:ℝ))*((v:ℝ)^j)^t*((j:ℝ)*2) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ht jp.le)
        (mul_nonneg non (pow_nonneg a0 t))
  have reps : (∑ b∈Icc 2 B,repeatedCost j b v) ≤ S/(2*(j:ℝ)*(1-(v:ℝ)^8)) := by
    rw [show Icc 2 B=Ico 2 (B+1) by ext i;simp,sum_Ico_eq_sum_range]
    refine (sum_le_sum fun i _ ↦ rep i).trans ?_
    rw [←mul_sum]
    have H := (geom a0 (a8.trans_lt a1) (B+1-2)).trans
      (one_div_le_one_div_of_le (sub_pos.mpr a1) (sub_le_sub_left a8 1))
    simpa [div_eq_mul_inv,mul_inv_rev,mul_assoc,mul_left_comm,mul_comm] using mul_le_mul_of_nonneg_left H (div_nonneg S0 (by positivity : 0≤2*(j:ℝ)))
  unfold headQ primitiveCost
  push_cast
  exact add_le_add (div_le_div_of_nonneg_right prim jp.le) reps

private theorem large_cost {v s : ℝ} (v0 : 0≤v) (v1 : v≤1) (s0 : 0≤ s) (s1 : s≤1)
    (vs : v≤ s^2) (sm : v^200 ≤ 1/2) {j : ℕ} (hj : 200≤j) (B : ℕ) :
    primitiveCost j v + (∑ b∈Icc 2 B,repeatedCost j b v) ≤ (3/2:ℝ)*s^j := by
  have prim := primitiveCost_le (j:=j) (by omega) v0 v1
  have pq := pow_le_pow_left₀ v0 vs ((j+1)/2)
  rw [←pow_mul] at pq
  have eq : v^((j+1)/2) ≤ s^j := pq.trans
    (pow_le_pow_of_le_one s0 s1 (by omega : j≤2*((j+1)/2)))
  let a := v^j
  have a0 : 0≤a := pow_nonneg v0 _
  have a2 : a≤1/2 := (pow_le_pow_of_le_one v0 v1 hj).trans sm
  have aS : a≤ s^j := pow_le_pow_left₀ v0 (vs.trans (by nlinarith)) _
  have step (t : ℕ) : repeatedCost j (2+t) v ≤ (a/2)*a^t := by
    have h := repeatedCost_le (j:=j) (b:=2+t) (by omega) (by omega) v0 v1
    simpa only [show 2+t-1=t+1 by omega,pow_succ,a,div_eq_mul_inv,mul_assoc,mul_comm,
      mul_left_comm,one_mul] using h
  rw [show Icc 2 B=Ico 2 (B+1) by ext i;simp,sum_Ico_eq_sum_range]
  have sumB : (∑ t∈range (B+1-2),repeatedCost j (2+t) v) ≤ a := by
    refine (sum_le_sum fun i _ ↦ step i).trans ?_
    rw [←mul_sum]
    apply (mul_le_mul_of_nonneg_left (geom a0 (by linarith) _) (by positivity)).trans
    rw [mul_one_div,div_le_iff₀ (by linarith : 0<1-a)]
    nlinarith only [mul_nonneg a0 (show 0 ≤ 1/2-a by linarith)]
  linarith only [prim,eq,aS,sumB]

theorem atom_head_tail {k : ℕ} (hk : 8≤k) (N B : ℕ) {v s : ℚ} (hv : 0≤v) (h1 : v<1)
    (s0 : 0≤ s) (s1 : s<1) (vs : v≤ s^2) (sm : v^200≤1/2) :
    (∑ z : LogAtom k N B, |atomCoefficient z| * (v:ℝ)^(atomLoss z)) ≤
      ((∑ j∈Icc 8 199, headQ v j : ℚ):ℝ) + (3/2:ℝ)*(s:ℝ)^200/(1-s) := by
  let F := fun j ↦ primitiveCost j v + (∑ b∈Icc 2 B,repeatedCost j b v)
  have v0 : 0≤(v:ℝ) := by exact_mod_cast hv
  have F0 (j : ℕ) : 0≤F j := by unfold F primitiveCost repeatedCost; positivity
  have incl : Icc k N ⊆ Ico 8 (200+N) := by intro j hj; have h := mem_Icc.mp hj; exact mem_Ico.mpr ⟨by omega,by omega⟩
  rw [atom_mass]
  change (∑ j∈Icc k N,F j) ≤ _
  apply (sum_le_sum_of_subset_of_nonneg incl (fun j _ _ ↦ F0 j)).trans
  rw [←sum_Ico_consecutive F (show 8≤200 by decide) (by omega : 200≤200+N)]
  apply add_le_add
  · rw [show Ico 8 200 = Icc 8 199 by ext j;simp;omega,Rat.cast_sum]
    exact sum_le_sum fun j hj ↦ cost_le_head hv h1 (mem_Icc.mp hj).1 B
  · rw [sum_Ico_eq_sum_range]
    have ss : 0≤(s:ℝ) := by exact_mod_cast s0
    have sl : (s:ℝ)<1 := by exact_mod_cast s1
    apply (sum_le_sum (g:=fun i : ℕ ↦ (3/2:ℝ)*(s:ℝ)^(200+i))
      (fun i _ ↦ large_cost v0 (by exact_mod_cast h1.le) ss sl.le (by exact_mod_cast vs)
        (by simpa using (Rat.cast_le (K:=ℝ)).mpr sm) (by omega : 200≤200+i) B)).trans
    simp_rw [pow_add,←mul_assoc]
    rw [←mul_sum]
    simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left (geom ss sl _) (by positivity : 0≤(3/2:ℝ)*(s:ℝ)^200)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem head_small : (∑ j∈Icc 8 199, headQ (4/5) j) < 363/1000 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem head_large : (∑ j∈Icc 8 199, headQ (93/100) j) < 248/100 := by decide +kernel

theorem atom_small {k : ℕ} (hk : 8≤k) (N B : ℕ) :
    (∑ z : LogAtom k N B, |atomCoefficient z| * (4/5:ℝ)^(atomLoss z)) ≤ 365/1000 := by
  have h := atom_head_tail (v:=4/5) (s:=179/200) hk N B (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  push_cast at h
  have hhd : (∑ j∈Icc 8 199,(headQ (4/5) j:ℝ)) < 363/1000 := by simpa using (Rat.cast_lt (K:=ℝ)).mpr head_small
  linarith only [h,hhd]

theorem atom_large {k : ℕ} (hk : 8≤k) (N B : ℕ) :
    (∑ z : LogAtom k N B, |atomCoefficient z| * (93/100:ℝ)^(atomLoss z)) ≤ 255/100 := by
  have h := atom_head_tail (v:=93/100) (s:=193/200) hk N B (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  push_cast at h
  have hhd : (∑ j∈Icc 8 199,(headQ (93/100) j:ℝ)) < 248/100 := by simpa using (Rat.cast_lt (K:=ℝ)).mpr head_large
  linarith only [h,hhd]

#print axioms atom_small
#print axioms atom_large
end LongCycleBounds.DescentMesh.InverseHead
