import LongCycleBounds.DescentMeshFullKernel

noncomputable section
namespace LongCycleBounds.DescentMesh
open Finset Polynomial ArithmeticFunction
open scoped Moebius

private theorem divisor_coeff {j h : ℕ} (hj : 0<j) (hh : 0<h) :
    (∑ d∈j.divisors,(monomial (j/d) ((μ d:ℤ):ℝ)).coeff h) =
       if h∣j then ((μ (j/h):ℤ):ℝ) else 0 := by
  simp only [coeff_monomial]
  by_cases hd : h∣j
  · rw [if_pos hd,sum_eq_single (j/h)]
    · have dp := Nat.div_pos (Nat.le_of_dvd hj hd) hh
      have eq := Nat.mul_div_cancel' hd
      have eq' : j/(j/h)=h := Nat.div_eq_of_eq_mul_left dp eq.symm
      simp [eq']
    · intro d hdiv ne
      apply if_neg
      intro same
      have eq := Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hdiv)
      rw [same] at eq
      exact ne (Nat.div_eq_of_eq_mul_right hh eq.symm).symm
    · intro hn
      exact False.elim (hn (Nat.mem_divisors.mpr ⟨⟨h,by rw [mul_comm,Nat.mul_div_cancel' hd]⟩,hj.ne'⟩))
  · rw [if_neg hd]
    apply sum_eq_zero
    intro d dm
    apply if_neg
    intro same
    have eq := Nat.div_mul_cancel (Nat.dvd_of_mem_divisors dm)
    rw [same] at eq
    exact hd ⟨d,eq.symm⟩

private theorem repeats_coeff {j i H : ℕ} (hj : 0<j) (hi : 0 < i) (cut : i ≤ H)
    (P : ℝ[X]) (h : ℕ) :
    (∑ b∈Icc 1 H, ((monomial (j*b) P).coeff i).coeff h) =
      if j∣i then P.coeff h else 0 := by
  simp only [coeff_monomial,apply_ite (fun p : ℝ[X] ↦ p.coeff h),coeff_zero]
  by_cases jd : j∣i
  · rw [if_pos jd,sum_eq_single (i/j)]
    · simp [Nat.mul_div_cancel' jd]
    · intro b _ ne
      exact if_neg fun same ↦ ne (Nat.div_eq_of_eq_mul_right hj same.symm).symm
    · intro hn
      exact False.elim (hn (mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd hi jd) hj,
        (Nat.div_le_self ..).trans cut⟩))
  · rw [if_neg jd]
    exact sum_eq_zero fun b _ ↦ if_neg fun eq ↦ jd ⟨b,eq.symm⟩

/-- Collect the true Euler derivative by both degrees before taking absolute values. -/
theorem rawKernel_collected {k H h l : ℕ} (hk : 1 ≤ k) (hh : 0<h) (hl : 0<l) (cut : h*l ≤ H) :
    (((rawKernel k H).coeff (h*l)).coeff h) =
    ∑ d ∈ l.divisors with k ≤ h*d, ((μ d:ℤ):ℝ) := by
  classical
  simp only [rawKernel,finsetSum_coeff]
  let S := (Icc k H).filter (fun j ↦ j∣h*l ∧ h∣j)
  have key : (∑ j∈Icc k H, ∑ b∈Icc 1 H,
      ((monomial (j*b) (∑ d∈j.divisors,monomial (j/d) ((μ d:ℤ):ℝ))).coeff (h*l)).coeff h)
      = ∑ j∈S,((μ (j/h):ℤ):ℝ) := by
    rw [sum_filter]
    apply sum_congr rfl
    intro j hj
    have jp : 0<j := lt_of_lt_of_le (by omega : 0<k) (mem_Icc.mp hj).1
    rw [repeats_coeff jp (Nat.mul_pos hh hl) cut,finsetSum_coeff,divisor_coeff jp hh]
    by_cases e : j∣h*l <;> by_cases f : h∣j <;> simp [e,f]
  rw [key]
  apply sum_nbij' (fun j ↦ j/h) (fun d ↦ h*d)
  · intro j hj
    obtain ⟨jin,dv,hd⟩ := mem_filter.mp hj
    have eq := Nat.mul_div_cancel' hd
    have jl : h*(j/h)∣h*l := by rw [eq]; exact dv
    exact mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨(Nat.dvd_of_mul_dvd_mul_left hh jl),hl.ne'⟩,
      by simpa only [eq] using (mem_Icc.mp jin).1⟩
  · intro d hd
    obtain ⟨dl,lo⟩ := mem_filter.mp hd
    have dv := Nat.dvd_of_mem_divisors dl
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨lo,(Nat.mul_le_mul_left h (Nat.le_of_dvd hl dv)).trans cut⟩,
      Nat.mul_dvd_mul_left h dv,dvd_mul_right ..⟩
  · intro j hj; exact Nat.mul_div_cancel' (mem_filter.mp hj).2.2
  · intro d _; exact Nat.mul_div_cancel_left d hh
  · intro j _; rfl

theorem rawKernel_cancels {k H h l : ℕ} (hk : 1 ≤ k) (kh : k ≤ h) (hl : 1<l) (cut : h*l ≤ H) :
    (((rawKernel k H).coeff (h*l)).coeff h) = 0 := by
  rw [rawKernel_collected hk (by omega) (by omega) cut]
  have all : (l.divisors.filter fun d ↦ k ≤ h*d) = l.divisors := by
    apply filter_true_of_mem
    intro d dm
    exact kh.trans (Nat.le_mul_of_pos_right _ (Nat.pos_of_mem_divisors dm))
  rw [all]
  have total : ∑ d∈l.divisors,μ d = 0 := by
    rw [←coe_mul_zeta_apply,moebius_mul_coe_zeta,one_apply_ne (by omega : l≠1)]
  exact_mod_cast total

/-- Signed positive-loss coefficient before exponentiation, at every occupied
bidegree strictly below the main diagonal. -/
theorem badLog_collected {k H h l : ℕ} (hk : 3 ≤ k) (hh : 0<h) (hl : 1<l) (cut : h*l ≤ H) :
    ((h*l:ℕ):ℝ) * (((badLogPolynomial k H H).coeff (h*l)).coeff h) =
      ∑ d ∈ l.divisors with k ≤ h*d, ((μ d:ℤ):ℝ) := by
  have Y := congrArg (fun p : BiPoly ↦ (p.coeff (h*l)).coeff h) (good_add_bad_kernel (H:=H) hk (by nlinarith))
  have off : h*l ≠ h := by nlinarith
  have g : ((goodKernel H k).coeff (h*l)).coeff h=0 := by
    simp only [goodKernel,biTerm,finsetSum_coeff]
    apply sum_eq_zero
    intro j _
    simp only [coeff_monomial]
    split_ifs <;> simp_all [coeff_monomial]
  rw [rawKernel_collected (by omega : 1 ≤ k) hh (by omega) cut] at Y
  simp only [coeff_add,euler_coeff,←C_eq_natCast,coeff_C_mul,g,zero_add] at Y
  exact Y

#print axioms badLog_collected
#print axioms rawKernel_collected
#print axioms rawKernel_cancels
end LongCycleBounds.DescentMesh
