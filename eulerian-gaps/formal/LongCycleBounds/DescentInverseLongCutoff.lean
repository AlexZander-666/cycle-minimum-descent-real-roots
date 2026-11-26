import LongCycleBounds.DescentInverseVariation

/-! A direct geometric bound on the positive-loss decorations of the genuine alphabet rows. -/
namespace LongCycleBounds.DescentMesh
open Finset Real Polynomial FixedCycleCount DescentNecklace
noncomputable section

private abbrev v : ℝ := 4/5
private abbrev s : ℝ := 179/200

private theorem finite_geom {a : ℝ} (h0 : 0 ≤ a) (h1 : a<1) (N : ℕ) :
    (∑ i ∈ range N,a^i) ≤ 1/(1-a) := by
  apply (le_div_iff₀ (sub_pos.mpr h1)).mpr
  rw [geom_sum_mul_neg]
  linarith only [pow_nonneg h0 N]

private theorem repeat_all {j : ℕ} (hj : 58 ≤ j) (B : ℕ) :
    (∑ b ∈ Icc 2 B,repeatedCost j b v) ≤ v^j := by
  let a := v^j
  have a0 : 0 ≤ a := by dsimp [a,v]; positivity
  have a2 : a ≤ 1/2 := (pow_le_pow_of_le_one (by norm_num : 0 ≤ v) (by norm_num)
    (by omega : 4 ≤ j)).trans (by norm_num [v])
  have term (t : ℕ) : repeatedCost j (2+t) v ≤ (a/2)*a^t := by
    have h := repeatedCost_le (j:=j) (b:=2+t) (by omega) (by omega) (by norm_num : 0 ≤ v)
      (by norm_num)
    simpa only [show 2+t-1=t+1 by omega,pow_succ,a,div_eq_mul_inv,mul_assoc,mul_comm,
      mul_left_comm,one_mul] using h
  rw [show Icc 2 B=Ico 2 (B+1) by ext b;simp,sum_Ico_eq_sum_range]
  refine (sum_le_sum (fun t _ ↦ term t)).trans ?_
  rw [←mul_sum]
  apply (mul_le_mul_of_nonneg_left (finite_geom a0 (by linarith) _) (by positivity)).trans
  change a/2*(1/(1-a)) ≤ a
  rw [mul_one_div,div_le_iff₀ (by linarith)]
  nlinarith only [mul_nonneg a0 (show 0 ≤ 1/2-a by linarith)]

private theorem cost_per_length {j : ℕ} (hj : 58 ≤ j) (B : ℕ) :
    primitiveCost j v + (∑ b ∈ Icc 2 B,repeatedCost j b v) ≤ (21/40:ℝ)*s^j := by
  have prim := primitiveCost_le (j:=j) (by omega) (by norm_num : 0 ≤ v) (by norm_num)
  have powv := pow_le_pow_left₀ (by norm_num : 0 ≤ v) (by norm_num [s,v] : v ≤ s^2) ((j+1)/2)
  rw [←pow_mul] at powv
  have powj := pow_le_pow_of_le_one (by norm_num : 0 ≤ s) (by norm_num)
    (by omega : j ≤ 2*((j+1)/2))
  have ratio : (160/179:ℝ)^j ≤ 1/40 :=
    (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega : 36 ≤ j)).trans (by norm_num)
  have rep := mul_le_mul_of_nonneg_right ratio (pow_nonneg (by norm_num : 0 ≤ s) j)
  rw [←mul_pow,show 160/179*s=v by norm_num [s,v]] at rep
  linarith only [prim,powv,powj,rep,repeat_all hj B]

private theorem log_cap {k : ℕ} (hk : 58 ≤ k) (N B : ℕ) :
    (∑ z : LogAtom k N B, |atomCoefficient z| * v^(atomLoss z)) ≤ 5*s^k := by
  rw [atom_mass,show Icc k N=Ico k (N+1) by ext i;simp,sum_Ico_eq_sum_range]
  refine (sum_le_sum fun i _ ↦ cost_per_length (j:=k+i) (by omega) B).trans ?_
  simp_rw [pow_add,←mul_assoc]
  rw [←mul_sum]
  apply (mul_le_mul_of_nonneg_left (finite_geom (by norm_num : 0 ≤ s) (by norm_num) _)
    (by positivity)).trans
  norm_num [s]
  ring_nf
  exact le_rfl

private theorem cap_small (k : ℕ) (hk : 58 ≤ k) : (2*(k:ℝ)+1)*(5*s^k) < 1 := by
  induction k,hk using Nat.le_induction with
  | base => norm_num [s]
  | succ k hk ih =>
    have kr : (58:ℝ) ≤ k := by exact_mod_cast hk
    have l : (2*((k:ℝ)+1)+1)*s ≤ 2*k+1 := by dsimp [s];linarith
    have g := mul_le_mul_of_nonneg_right l (show 0 ≤ 5*s^k by positivity)
    rw [Nat.cast_succ,pow_succ]
    nlinarith only [g,ih]

theorem word_mass_strict {k : ℕ} (hk : 58 ≤ k) (N B T : ℕ) :
    (∑ w : LogWord k N B T, |wordCoefficient w| * v^(wordLoss w)) < 1/(2*(k:ℝ)) := by
  classical
  let c := (∑ z : LogAtom k N B, |atomCoefficient z| * v^(atomLoss z))
  have c0 : 0 ≤ c := sum_nonneg fun _ _ ↦ by positivity
  have kr : (58:ℝ) ≤ k := by exact_mod_cast hk
  have limit := (mul_le_mul_of_nonneg_left (log_cap hk N B)
    (show 0 ≤ 2*(k:ℝ)+1 by positivity)).trans_lt (cap_small k hk)
  change (2*k+1:ℝ)*c<1 at limit
  have c1 : c<1 := by nlinarith only [limit,mul_nonneg (Nat.cast_nonneg (α:=ℝ) k) c0]
  have sm : (∑ i ∈ range T, c^(i+1)/((i+1).factorial:ℝ)) ≤ exp c-1 := by
    have a := Real.sum_le_exp_of_nonneg c0 (T+1)
    rw [sum_range_succ',pow_zero,Nat.factorial_zero,Nat.cast_one,div_one] at a
    linarith only [a]
  have eq : (∑ w : LogWord k N B T, |wordCoefficient w| * v^(wordLoss w)) =
      ∑ i ∈ range T, c^(i+1)/((i+1).factorial:ℝ) := by
    rw [Fintype.sum_sigma,←Fin.sum_univ_eq_sum_range]
    apply sum_congr rfl
    intro i _
    rw [←tupleMass_eq (fun z : LogAtom k N B ↦ |atomCoefficient z| * v^(atomLoss z)) (i.val+1)]
    unfold tupleMass
    rw [sum_div]
    apply sum_congr rfl
    intro w _
    simp only [wordCoefficient,wordLoss,abs_div,abs_prod,Nat.abs_cast,prod_mul_distrib,
      prod_pow_eq_pow_sum]
    ring
  rw [eq]
  refine sm.trans_lt ?_
  have expcap := exp_bound_div_one_sub_of_interval c0 c1
  have small : 1/(1-c)<1+1/(2*(k:ℝ)) := by
    rw [div_lt_iff₀ (sub_pos.mpr c1)]
    field_simp
    nlinarith only [limit]
  linarith

/-- Radius 4/5 dominance for the genuine finite necklace expansion at all ranks n≥k≥58. -/
theorem expanded_four_fifths {n k : ℕ} (hk : 58 ≤ k) (hn : k ≤ n) (N B T : ℕ) :
    lossNorm n (expandedCoefficient n k N B T) (4/5) < allowedFraction n k := by
  classical
  apply (expanded_loss_le n k N B T (by norm_num : 0 ≤ (4/5:ℝ))).trans_lt
  apply lt_of_le_of_lt _ ((word_mass_strict hk N B T).trans_le
    (Occupancy.allowedFraction_ge_half (by omega) hn))
  apply sum_le_sum
  intro w _
  split_ifs
  · have cap (m : ℕ) : allowedFraction m k ≤ 1 := by
      by_cases hz : m=0
      · simp [hz,allowedFraction_zero]
      have kr : (1:ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
      exact (allowedFraction_le (by omega : 2 ≤ k) (Nat.pos_of_ne_zero hz)).trans
        ((div_le_one (by linarith)).mpr kr)
    exact mul_le_of_le_one_left (by positivity) (cap _)
  · positivity

/-- Original alphabet polynomial of the actual ordinary-descent row, with a coefficient
inequality (rather than only complex nonvanishing). -/
theorem actual_four_fifths_long {n k : ℕ} (hk : 58 ≤ k) (hn : k ≤ n) :
    lossNorm n (fun i ↦ ((profilePolynomial n k).coeff i : ℝ)) (4/5) <
      ((profilePolynomial n k).coeff n : ℝ) := by
  have eq (i : ℕ) : ((profilePolynomial n k).coeff i : ℝ) = expandedCoefficient n k n n n i := by
    have h := congrArg (fun p : ℝ[X] ↦ p.coeff i) (profile_eq_expansion (n:=n) (k:=k)
      (by omega) (by omega))
    rw [←good_mul_badTaylor_coeff n k n n n i]
    have cast (a : ℚ) : (Rat.castHom ℝ) a = (a:ℝ) := rfl
    simpa only [coeff_map,cast,expansionRow] using h
  simp only [eq,expanded_top (by omega : 3 ≤ k) (by omega : 0<n)]
  exact expanded_four_fifths hk hn n n n

#print axioms word_mass_strict
#print axioms expanded_four_fifths
#print axioms actual_four_fifths_long
end
end LongCycleBounds.DescentMesh
