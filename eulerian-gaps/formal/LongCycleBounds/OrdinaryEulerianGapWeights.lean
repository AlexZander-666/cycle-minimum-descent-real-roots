import LongCycleBounds.OrdinaryEulerianCentralRoot
import LongCycleBounds.DescentMeshTransform

noncomputable section
namespace LongCycleBounds.OrdinaryEulerianGap
open Finset DescentMesh Band PoleBridge PoleTails Bulk Real LongCycles

/-- Angular upper bound at a single full pole order, including the first odd pole. -/
theorem full_order_mass {q : ℕ} {x : ℝ} (hx : 0 ≤ x) (hq : 8 ≤ (q:ℝ))
    (angular : 1 ≤ (q:ℝ)*s x^2) :
    |scaledMoment (radius x) (-exp (-x)) q| ≤ 10/9 := by
  let z := pole (c x) (s x)
  let l (j : ℕ) : ℝ := 2*(j:ℝ)+5
  have hl (j : ℕ) : 3 ≤ l j := by dsimp [l]; linarith [show 0 ≤ (j:ℝ) by positivity]
  have mass (a : ℝ) (ha : 1 ≤ a) : ‖z a^q‖ ≤ envelope a^4 := by
    unfold z
    rw [norm_pole_pow _ _ _ (circle x) ha]
    exact decay_p _ _ _ ha hq angular
  have partsum (N : ℕ) : ∑ j ∈ range N, ‖z (l j)^q‖ ≤ 2/81 := by
    calc _ ≤ ∑ j ∈ range N, (1/3:ℝ)*(l j*envelope (l j)^4) := sum_le_sum (fun i _ ↦
            (mass _ (by linarith [hl i])).trans (by
              nlinarith only [mul_nonneg (sub_nonneg.mpr (hl i)) (show 0 ≤ envelope (l i)^4 by positivity)]))
         _ ≤ _ := by rw [←mul_sum]; linarith only [(two_tails N).1]
  have sm := summable_of_sum_range_le (fun i ↦ norm_nonneg (z (l i)^q)) partsum
  have ts := (norm_tsum_le_tsum_norm sm).trans (Real.tsum_le_of_sum_range_le (fun i ↦ norm_nonneg (z (l i)^q)) partsum)
  have m1 := mass 1 le_rfl
  have m3 := mass 3 (by norm_num)
  norm_num [envelope] at m1 m3
  rw [←norm_pow] at m1 m3
  have totalBound : ‖total (c x) (s x) q‖ ≤ 10/9 := by
    change ‖z 1^q+(z 3^q+∑' i,z (l i)^q)‖ ≤ _
    linarith only [norm_add_le (z 1^q) (z 3^q+∑' i,z (l i)^q),
      norm_add_le (z 3^q) (∑' i,z (l i)^q),m1,m3,ts]
  have hqNat : 8 ≤ q := by exact_mod_cast hq
  rw [scaledMoment_poles _ (by omega) _ _ hx]
  have he := congrArg Complex.re (complete_normalization x q q hq angular (by linarith))
  have eq : radius x^q*(oddPoleSum q x).re=2*(total (c x) (s x) q).re := by
    simpa [Complex.mul_re,←Complex.ofReal_pow] using he
  rw [eq]
  rw [show 2*(total (c x) (s x) q).re/2=(total (c x) (s x) q).re by ring]
  exact (Complex.abs_re_le_norm _).trans totalBound

private theorem lower_degree_budget {n h : ℕ} (hn : 128≤n) (half : 2*h<n)
    {R : ℝ} (R0 : 0≤R) (cap : R≤63/20*sqrt n) :
    sqrt n * (((h.factorial:ℝ)/n.factorial)*R^(n-h)) * n ≤ 1 := by
  let z := sqrt (n:ℝ)
  have N : (128:ℝ)≤n := by exact_mod_cast hn
  have np : 0<(n:ℝ) := by linarith
  have zp : 0<z := sqrt_pos.mpr np
  have zz : z^2=(n:ℝ) := sq_sqrt np.le
  have zlow : (45/4:ℝ) ≤ z := by nlinarith only [zz,N,zp]
  have er : exp 1 * R / (n:ℝ) ≤ 9/z := by
    rw [div_le_div_iff₀ np zp]
    have em := mul_le_mul_of_nonneg_right (show exp 1≤11/4 by linarith [exp_one_lt_d9]) R0
    change R≤63/20*z at cap
    nlinarith only [mul_le_mul_of_nonneg_right em zp.le,mul_le_mul_of_nonneg_right cap zp.le,zz,np]
  have e := (uniform_factorial_weight (by omega) (by omega : h≤n) R0).trans
    (pow_le_pow_left₀ (by positivity) er (n-h))
  have base : 9/z ≤ 4/5 := (div_le_iff₀ zp).mpr (by linarith)
  have bpos : 0≤9/z := by positivity
  have small := (pow_le_pow_left₀ bpos base (n-h-3)).trans
    (pow_le_pow_of_le_one (by norm_num) (by norm_num : (4/5:ℝ)≤1) (by omega : 61≤n-h-3))
  have split : (9/z)^(n-h)=(9/z)^3*(9/z)^(n-h-3) := by rw [←pow_add]; congr 1; omega
  rw [split] at e
  calc
    _ ≤ z*((9/z)^3*(4/5:ℝ)^61)*n := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (e.trans (mul_le_mul_of_nonneg_left small (by positivity))) zp.le) np.le
    _ = 729*(4/5:ℝ)^61 := by rw [←zz]; field_simp; ring
    _ ≤ 1 := by norm_num

private theorem high_base_budget {n : ℕ} (hn : 128≤n) {R : ℝ}
    (R0 : 0≤R) (cap : R≤63/20*sqrt n) :
    sqrt n * (((n-2).factorial:ℝ)/n.factorial)*R^2*(10/9) ≤ 1 := by
  let z := sqrt (n:ℝ)
  have N : (128:ℝ)≤n := by exact_mod_cast hn
  have np : 0<(n:ℝ) := by linarith
  have zp : 0<z := sqrt_pos.mpr np
  have zz : z^2=(n:ℝ) := sq_sqrt np.le
  have zlow : (45/4:ℝ) ≤ z := by nlinarith only [zz,N,zp]
  have rn : ((n-2).factorial:ℝ)/n.factorial = 1/((n:ℝ)*(n-1)) := by
    obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le (show 2 ≤ n by omega)
    simp only [show 2+a=a+2 by omega,Nat.add_sub_cancel,Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,
      Nat.cast_one,Nat.cast_ofNat]
    rw [show (a:ℝ)+2-1=(a:ℝ)+1 by ring]
    field_simp
    ring
  rw [rn]
  have r2 := sq_le_sq₀ R0 (show 0≤63/20*z by positivity) |>.mpr cap
  have nlow : (127/128:ℝ)*n ≤ (n:ℝ)-1 := by linarith
  have zz' : (45/4:ℝ)*z ≤ n := by nlinarith only [mul_le_mul_of_nonneg_right zlow zp.le,zz]
  change z * (1/((n:ℝ)*(n-1)))*R^2*(10/9) ≤ 1
  rw [show z * (1/((n:ℝ)*(n-1)))*R^2*(10/9) = (z*R^2*(10/9))/((n:ℝ)*(n-1)) by ring]
  apply (div_le_one (mul_pos np (by linarith))).mpr
  nlinarith only [mul_le_mul_of_nonneg_left r2 zp.le,congrArg (fun a:ℝ ↦ z*a) zz,
    mul_le_mul_of_nonneg_right zz' np.le,mul_le_mul_of_nonneg_left nlow np.le]

/-- Loss two needs the full-order pole estimate. Further upper-half losses
contribute a geometric factor, while lower-half losses obey the factorial bound. -/
theorem central_weight {n h : ℕ} (hn : 128≤n) (h0 : 1≤h) (hi : h+2≤n)
    {x : ℝ} (hx : 0≤x) (upper : x≤5/2*sqrt ((n:ℝ)-1)) :
    sqrt n * (((h.factorial:ℝ)/n.factorial)*(radius x)^(n-h)) *
      |scaledMoment (radius x) (-exp (-x)) (h+1)| ≤ (4/5:ℝ)^(n-h) := by
  let R := (5/4:ℝ)*radius x
  let U := scaledMoment (radius x) (-exp (-x)) (h+1)
  have ⟨rmax,angular,_⟩ := central_geometry hn hx upper
  have N : (128:ℝ) ≤ n := by exact_mod_cast hn
  have npos : 0<(n:ℝ) := by linarith
  have zpos := sqrt_pos.mpr npos
  have zz := sq_sqrt npos.le
  have zl : (45/4:ℝ) ≤ sqrt n := by nlinarith only [zz,N,zpos]
  have cap : R≤63/20*sqrt n := by dsimp [R]; linarith only [rmax]
  have r0 : 0≤R := mul_nonneg (by norm_num) (radius_pos x).le
  have sp : 0<s x := div_pos pi_pos (radius_pos x)
  have hm := scaled_moment_mass (q:=h+1) (by omega) hx
  change 2*|U| ≤ _ at hm
  have den : 0<((h+1:ℕ):ℝ)*s x^2 := by positivity
  have hraw : |U|≤(n:ℝ) := by
    have low : 1/(((h+1:ℕ):ℝ)*s x^2) ≤ n := by
      apply (div_le_iff₀ den).mpr
      push_cast
      nlinarith only [angular,mul_nonneg (show 0≤(h:ℝ) by positivity) (mul_nonneg npos.le (sq_nonneg (s x)))]
    linarith only [hm,low,N]
  have wh : sqrt n * (((h.factorial:ℝ)/n.factorial)*R^(n-h))*|U| ≤ 1 := by
    by_cases half : n≤2*h
    · have base := high_base_budget hn r0 cap
      by_cases eq : h+2=n
      · have he : h=n-2 := by omega
        have qp : 8≤((h+1:ℕ):ℝ) := by exact_mod_cast (by omega : 8≤h+1)
        have qr : (n:ℝ)≤(3/2)*((h+1:ℕ):ℝ) := by
          have : n≤h+2 := by omega
          have hh : 2≤h := by omega
          have t : 2*(n:ℝ)≤3*((h+1:ℕ):ℝ) := by exact_mod_cast (by omega : 2*n≤3*(h+1))
          linarith only [t]
        have qa : 1≤((h+1:ℕ):ℝ)*s x^2 := by
          nlinarith only [angular,mul_nonneg (sub_nonneg.mpr qr) (sq_nonneg (s x))]
        have ub : |U|≤10/9 := full_order_mass hx qp qa
        rw [show n-h=2 by omega]
        calc _ ≤ sqrt n * (((h.factorial:ℝ)/n.factorial)*R^2)*(10/9) :=
                mul_le_mul_of_nonneg_left ub (by positivity)
             _ = _ := by rw [he]; ring
             _ ≤ 1 := base
      · have hle : h≤n-2 := by omega
        have high := upper_half_factorial_weight (by omega : 0<n-2) hle (by omega) r0
        have Rcap : 2*R/((n-2:ℕ):ℝ) ≤ 3/5 := by
          rw [Nat.cast_sub (by omega : 2≤n),Nat.cast_ofNat]
          apply (div_le_iff₀ (by linarith)).mpr
          nlinarith only [cap,zz,zl,mul_nonneg (sub_nonneg.mpr zl) zpos.le]
        have extra := (high.trans (pow_le_pow_left₀ (by positivity) Rcap _)).trans
          (show (3/5:ℝ)^(n-2-h)≤3/5 by
            simpa using pow_le_pow_of_le_one (by norm_num) (by norm_num : (3/5:ℝ)≤1) (show 1≤n-2-h by omega))
        have qa : 3/4≤((h+1:ℕ):ℝ)*s x^2 := by
          have hr : (n:ℝ)≤2*(h:ℝ) := by exact_mod_cast half
          push_cast; nlinarith only [angular,mul_nonneg (sub_nonneg.mpr hr) (sq_nonneg (s x)),sq_nonneg (s x)]
        have inv := one_div_le_one_div_of_le (by norm_num : (0:ℝ)<3/4) qa
        have ucap : |U|≤5/3 := by linarith only [hm,inv]
        have eu := mul_le_mul extra ucap (abs_nonneg _) (by norm_num)
        have fac : ((h.factorial:ℝ)/n.factorial)*R^(n-h) =
            (((n-2).factorial:ℝ)/n.factorial)*R^2 * (((h.factorial:ℝ)/(n-2).factorial)*R^(n-2-h)) := by
          rw [show n-h=2+(n-2-h) by omega,pow_add]
          field_simp
        rw [fac]
        calc _ = (sqrt n * (((n-2).factorial:ℝ)/n.factorial)*R^2) *
                    ((((h.factorial:ℝ)/(n-2).factorial)*R^(n-2-h))*|U|) := by ring
             _ ≤ _ := mul_le_mul_of_nonneg_left (eu.trans (by norm_num : (3/5:ℝ)*(5/3)≤10/9)) (by positivity)
             _ ≤ 1 := base
    · exact (mul_le_mul_of_nonneg_left hraw (by positivity)).trans (lower_degree_budget hn (by omega) r0 cap)
  have scale : radius x = (4/5:ℝ)*R := by dsimp [R]; ring
  change sqrt n * (((h.factorial:ℝ)/n.factorial)*(radius x)^(n-h)) * |U| ≤ _
  rw [scale,mul_pow]
  calc
    _ = (4/5:ℝ)^(n-h)*(sqrt n * (((h.factorial:ℝ)/n.factorial)*R^(n-h))*|U|) := by ring
    _ ≤ _ := by simpa only [mul_one] using mul_le_mul_of_nonneg_left wh (show 0≤(4/5:ℝ)^(n-h) by positivity)

#print axioms central_weight

#print axioms full_order_mass
end LongCycleBounds.OrdinaryEulerianGap
