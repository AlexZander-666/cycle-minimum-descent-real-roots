import LongCycleBounds.DescentBoundaryDerangementReadout
import LongCycleBounds.DescentMeshColor
import Mathlib.Algebra.BigOperators.Intervals

noncomputable section
namespace LongCycleBounds.DescentDerangement
open Finset Polynomial DescentNecklace DescentMesh DescentTwoLetters

def signedInput (n : ℕ) (s : ℚ) (h : ℕ) : ℝ := (s:ℝ)^(n-h)*gnCoeff n h

private theorem top_loss_zero {n : ℕ} (hn : 0<n) : (gn n).coeff n=0 := by
  have eq := alphabet_zero hn (row n 2).coeff
  rwa [alphabet_eq_profile hn,original_profile_two hn,coeff_reflect,revAt_zero] at eq

theorem actual_color_value {n q : ℕ} (hn : 0<n) (hq : 0<q) (s : ℚ) :
    colorEval n (signedInput n s) q = ((q:ℝ)^n)*(((gn n).eval (s/(q:ℚ)) : ℚ):ℝ) := by
  have nz : (q:ℚ) ≠ 0 := by positivity
  let f (d : ℕ) := (gn n).coeff d * (s/(q:ℚ))^d
  have calcQ :
      (q:ℚ)^n*(gn n).eval (s/q) =
        ∑ h ∈ Icc 1 n, s^(n-h)*(gn n).coeff (n-h)*(q:ℚ)^h := by
    rw [eval_eq_sum_range' (Nat.lt_succ_of_le (gn_degree n))]
    change (q:ℚ)^n * (∑ d ∈ range (n+1), f d) = _
    rw [← sum_range_reflect f (n+1),mul_sum]
    let v (h : ℕ) := s^(n-h)*(gn n).coeff (n-h)*(q:ℚ)^h
    calc
      _ = ∑ h ∈ range (n+1), v h := by
        apply sum_congr rfl
        intro h hh
        have le := Nat.le_of_lt_succ (mem_range.mp hh)
        have pw : (q:ℚ)^n=(q:ℚ)^h*(q:ℚ)^(n-h) := by rw [← pow_add]; congr 1; omega
        simp only [Nat.add_sub_cancel,f,v,div_pow,pw]
        field_simp
      _ = _ := by
        symm
        apply sum_subset (fun h hh ↦ mem_range.mpr (Nat.lt_succ_of_le (mem_Icc.mp hh).2))
        intro h hh no
        have z : h=0 := by have := mem_range.mp hh; simp only [mem_Icc,not_and] at no; omega
        simp [z,top_loss_zero hn]
  have cast := congrArg (fun x : ℚ ↦ (x:ℝ)) calcQ
  push_cast at cast
  simpa only [colorEval,signedInput,gnCoeff] using cast.symm

theorem gn_at_minus_one (n : ℕ) :
    (gn n).eval (-1) = if Even n then 1 else 0 := by
  have atom (j : ℕ) : (gnAtom j).eval (-1)=(-1:ℚ)^j := by
    induction j with
    | zero => simp [gnAtom]
    | succ j ih =>
      rw [gnAtom,eval_mul,eval_mul,eval_C,eval_sub,eval_mul,eval_X,eval_C,eval_one,ih,pow_succ]
      push_cast
      field_simp
      ring
  induction n with
  | zero => simp [gn,gnAtom]
  | succ n ih =>
    rw [gn_succ,eval_add,ih,atom,pow_succ]
    simp only [Nat.even_add_one]
    by_cases e : Even n
    · simp [e,e.neg_one_pow]
    · simp [e,(Nat.not_even_iff_odd.mp e).neg_one_pow]

theorem gn_at_one {n : ℕ} (hn : 0<n) : (gn n).eval 1=0 := by
  have vanish (j : ℕ) (hj : 2≤j) : (gnAtom j).eval 1 = 0 := by
    induction j, hj using Nat.le_induction with
    | base => norm_num [gnAtom]
    | succ j _ ih => simp [gnAtom,ih]
  induction n, hn using Nat.le_induction with
  | base => norm_num [gn,gnAtom,sum_range_succ]
  | succ j hj ih => rw [gn_succ,eval_add,ih,vanish _ (by omega),add_zero]

#print axioms actual_color_value
#print axioms gn_at_minus_one
#print axioms gn_at_one
end LongCycleBounds.DescentDerangement
