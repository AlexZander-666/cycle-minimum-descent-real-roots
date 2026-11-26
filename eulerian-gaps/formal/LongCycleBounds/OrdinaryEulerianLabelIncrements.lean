import LongCycleBounds.OrdinaryEulerianLabelDifferences

noncomputable section
namespace LongCycleBounds.OrdinaryEulerianGap
open DescentMesh DescentNecklace Finset

theorem increment_error {n q : ℕ} (hn : 1≤n) (hq : 1≤q) (a : ℕ→ℝ)
    (dominates : lossNorm n a (4/5)<a n) (subtop : a (n-1)=0) {K : ℝ} (K0 : 0≤K)
    (kern : ∀ i : ℕ, 1≤ i → (i:ℝ)*(5/(4*q:ℝ))^(i+1)≤K) :
    |labelG n a (q+1)-labelG n a q-1| ≤ K := by
  have ap : 0<a n := (show 0≤lossNorm n a (4/5) from sum_nonneg fun _ _ ↦ by positivity).trans_lt dominates
  have qp : 0<(q:ℝ) := by exact_mod_cast hq
  let term (p : ℝ) (h : ℕ) := a h*(1/p)^(n-h-1)
  have res : labelG n a (q+1)-labelG n a q-1 =
      (∑ h ∈ Ico 1 n,(term (q+1) h-term q h))/a n := by
    rw [labelG_expansion hn (by omega : 1≤q+1) a ap,labelG_expansion hn hq a ap,
      sum_sub_distrib,Nat.cast_add,Nat.cast_one]
    dsimp only [term]; ring
  rw [res,abs_div,abs_of_pos ap,div_le_iff₀ ap]
  apply (abs_sum_le_sum_abs _ _).trans
  have point (h : ℕ) (hh : h∈Ico 1 n) :
      |term (q+1) h-term q h| ≤ K*(|a h| *(4/5:ℝ)^(n-h)) := by
    have hhi := (mem_Ico.mp hh).2
    by_cases eq : h=n-1
    · simp [term,eq,subtop]
    let i := n-h-1
    have ip : 1≤ i := by dsimp [i]; omega
    have ie : n-h=i+1 := by dsimp [i]; omega
    have b := inverse_step i qp
    have decomp : 1/(q:ℝ)=(4/5:ℝ)*(5/(4*q)) := by field_simp
    rw [decomp] at b
    simp only [mul_pow] at b
    change |a h*(1/((q:ℝ)+1))^i-a h*(1/(q:ℝ))^i| ≤ _
    rw [←mul_sub,abs_mul]
    have c : |(1/((q:ℝ)+1))^i-(1/(q:ℝ))^i| ≤ (4/5:ℝ)^(i+1)*K := by
      rw [decomp,mul_pow]
      calc _ ≤ _ := b
           _ = (4/5:ℝ)^(i+1)*((i:ℝ)*(5/(4*q:ℝ))^(i+1)) := by ring
           _ ≤ _ := mul_le_mul_of_nonneg_left (kern i ip) (by positivity)
    rw [ie]
    calc _ ≤ _ := mul_le_mul_of_nonneg_left c (abs_nonneg (a h))
         _ = _ := by ring
  calc _ ≤ _ := sum_le_sum point
       _ = K*lossNorm n a (4/5) := by rw [lossNorm,mul_sum]
       _ ≤ _ := mul_le_mul_of_nonneg_left dominates.le K0

private theorem second_error {n : ℕ} (hn : 1≤n) (a : ℕ→ℝ)
    (dominates : lossNorm n a (4/5)<a n) (subtop : a (n-1)=0) :
    |labelG n a 2-2| ≤ 25/32 := by
  have ap : 0<a n := (show 0≤lossNorm n a (4/5) from sum_nonneg fun _ _ ↦ by positivity).trans_lt dominates
  rw [labelG_expansion hn (by norm_num : 1≤2) a ap,Nat.cast_ofNat,add_sub_cancel_left,abs_div,abs_of_pos ap,div_le_iff₀ ap]
  apply (abs_sum_le_sum_abs _ _).trans
  have point (h : ℕ) (hh : h∈Ico 1 n) :
      |a h*(1/2:ℝ)^(n-h-1)| ≤ (25/32)*(|a h| *(4/5:ℝ)^(n-h)) := by
    have hi := (mem_Ico.mp hh).2
    by_cases e : h=n-1
    · simp [e,subtop]
    have i : 2≤n-h := by omega
    have scale : (1/2:ℝ)^(n-h-1)=2*((4/5:ℝ)^(n-h)*(5/8:ℝ)^(n-h)) := by
      rw [←mul_pow,show (4/5:ℝ)*(5/8)=1/2 by norm_num]
      conv_rhs => rw [show n-h=(n-h-1)+1 by omega,pow_succ]
      ring
    rw [abs_mul,abs_of_nonneg (by positivity : 0≤(1/2:ℝ)^(n-h-1)),scale]
    have tail := pow_le_pow_of_le_one (by norm_num : 0≤(5/8:ℝ)) (by norm_num : (5/8:ℝ)≤1) i
    have mult := mul_le_mul_of_nonneg_left tail (show 0≤2*|a h| *(4/5:ℝ)^(n-h) by positivity)
    linarith only [mult]
  calc _ ≤ _ := sum_le_sum point
       _ = (25/32)*lossNorm n a (4/5) := by rw [lossNorm,mul_sum]
       _ ≤ _ := mul_le_mul_of_nonneg_left dominates.le (by norm_num)

theorem actual_label_steps {n k : ℕ} (hn : 128≤n) (hk : 3≤k) (kn : k≤n)
    {a : ℕ→ℝ} (choice : a=(fun h ↦ ((profilePolynomial n k).coeff h:ℝ)) ∨
      a=reflectedCoefficients n (fun h ↦ ((profilePolynomial n k).coeff h:ℝ))) :
    labelG n a 1=0 ∧ ∀ q : ℕ, 1≤q →
      (let Δ := labelG n a (q+1)-labelG n a q
       1/2≤Δ ∧ Δ≤3 ∧ (2≤q → Δ≤3/2) ∧ (3≤q → 119/144≤Δ ∧ Δ≤169/144)) := by
  obtain ⟨one,low,norm⟩ := actual_label_inputs hn hk kn choice
  have zer : labelG n a 1=0 := by simp [labelG,one]
  refine ⟨zer,?_⟩
  intro q hq
  dsimp only
  by_cases first : q=1
  · subst q
    have e := abs_le.mp (second_error (by omega) a norm low)
    rw [zer,sub_zero]
    norm_num at e ⊢
    exact ⟨by linarith only [e.1],by linarith only [e.2]⟩
  have qr : (2:ℝ)≤q := by exact_mod_cast (by omega : 2≤q)
  have large {b K : ℝ} (K0 : 0≤K) (qb : 5/(4*q:ℝ)≤b)
      (kb : ∀ i : ℕ,1≤ i → (i:ℝ)*b^(i+1)≤K) :=
    increment_error (by omega : 1≤n) hq a norm low K0
      (fun i hi ↦ (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) qb _) (Nat.cast_nonneg i)).trans (kb i hi))
  have e := abs_le.mp (large (by norm_num : 0≤(1/2:ℝ))
    ((div_le_iff₀ (by positivity)).mpr (by linarith)) (fun _ h ↦ discrete_kernel_two h))
  refine ⟨by linarith only [e.1],by linarith only [e.2],fun _ ↦ by linarith only [e.2],?_⟩
  intro q3
  have qr3 : (3:ℝ)≤q := by exact_mod_cast q3
  have f := abs_le.mp (large (by norm_num : 0≤(25/144:ℝ))
    ((div_le_iff₀ (by positivity)).mpr (by linarith)) (fun _ h ↦ discrete_kernel_three h))
  exact ⟨by linarith only [f.1],by linarith only [f.2]⟩

#print axioms actual_label_steps
end LongCycleBounds.OrdinaryEulerianGap
