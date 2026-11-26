import LongCycleBounds.DescentActualColors
import LongCycleBounds.DescentInverseAll

noncomputable section
namespace LongCycleBounds.OrdinaryEulerianGap
open Finset Polynomial DescentMesh DescentNecklace DescentTwoLetters Real

/-- Positive labels, with no zero-index shift. -/
def labelG (n : ℕ) (a : ℕ→ℝ) (q : ℕ) : ℝ :=
  colorEval n a q / (a n*(q:ℝ)^(n-1))

theorem inverse_step (s : ℕ) {q : ℝ} (qp : 0<q) :
    |(1/(q+1))^s-(1/q)^s| ≤ s*(1/q)^(s+1) := by
  let A := 1/q
  let B := 1/(q+1)
  have a0 : 0≤A := by dsimp [A]; positivity
  have b0 : 0≤B := by dsimp [B]; positivity
  have ba : B≤A := one_div_le_one_div_of_le qp (by linarith)
  have bdiff : A-B≤A^2 := by
    have eq : A-B=A*B := by dsimp [A,B]; field_simp; ring
    rw [eq,pow_two]; exact mul_le_mul_of_nonneg_left ba a0
  have bound (i : ℕ) : A^i-B^i ≤ i*A^(i+1) := by
    induction i with
    | zero => simp
    | succ i ih =>
      calc
        A^(i+1)-B^(i+1) = A*(A^i-B^i)+(A-B)*B^i := by ring
        _ ≤ A*(i*A^(i+1))+A^2*A^i := add_le_add (mul_le_mul_of_nonneg_left ih a0)
            (mul_le_mul bdiff (pow_le_pow_left₀ b0 ba _) (pow_nonneg b0 _) (sq_nonneg _))
        _ = _ := by push_cast; ring
  rw [abs_of_nonpos (sub_nonpos.mpr (pow_le_pow_left₀ b0 ba s)),neg_sub]
  exact bound s

private theorem decay_after (b : ℝ) (b0 : 0≤b) (b1 : b≤1) (s : ℕ)
    (step : ((s:ℝ)+1)*b≤ s) (i : ℕ) :
    ((s+i:ℕ):ℝ)*b^(s+i+1) ≤ (s:ℝ)*b^(s+1) := by
  induction i with
  | zero => simp
  | succ i ih =>
    have ib : (i:ℝ)*b≤ i := by simpa using mul_le_mul_of_nonneg_left b1 (show (0:ℝ)≤ i by positivity)
    have si : ((s+(i+1):ℕ):ℝ)*b ≤ (s+i:ℕ) := by push_cast; linarith only [step,ib]
    calc _ = (((s+(i+1):ℕ):ℝ)*b)*b^(s+i+1) := by rw [show s+(i+1)+1=s+i+1+1 by omega,pow_succ]; ring
         _ ≤ _ := mul_le_mul_of_nonneg_right si (pow_nonneg b0 _)
         _ ≤ _ := ih

theorem discrete_kernel_two {s : ℕ} (hs : 1≤ s) : (s:ℝ)*(5/8:ℝ)^(s+1) ≤ 1/2 := by
  by_cases one : s=1
  · subst s; norm_num
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le (show 2≤ s by omega)
  exact (decay_after (5/8) (by norm_num) (by norm_num) 2 (by norm_num) i).trans (by norm_num)

theorem discrete_kernel_three {s : ℕ} (hs : 1≤ s) : (s:ℝ)*(5/12:ℝ)^(s+1) ≤ 25/144 := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hs
  exact (decay_after (5/12) (by norm_num) (by norm_num) 1 (by norm_num) i).trans (by norm_num)

theorem actual_label_inputs {n k : ℕ} (hn : 128≤n) (hk : 3≤k) (kn : k≤n)
    {a : ℕ→ℝ} (choice : a=(fun h ↦ ((profilePolynomial n k).coeff h:ℝ)) ∨
      a=reflectedCoefficients n (fun h ↦ ((profilePolynomial n k).coeff h:ℝ))) :
    colorEval n a 1=0 ∧ a (n-1)=0 ∧ lossNorm n a (4/5)<a n := by
  have eq : (fun h ↦ ((profilePolynomial n k).coeff h:ℝ)) = rowAlphabet n k := by
    funext h
    have e := congrArg (fun p : ℝ[X] ↦ p.coeff h) (profile_eq_expansion (n:=n) (k:=k) hk (by omega))
    unfold rowAlphabet
    rw [←good_mul_badTaylor_coeff n k n n n h]
    simpa only [coeff_map,expansionRow,Rat.coe_castHom] using e
  have low : rowAlphabet n k (n-1)=0 := by
    simp only [rowAlphabet,expandedCoefficient,if_neg (show n-1≠n by omega),zero_add]
    apply sum_eq_zero
    intro w _
    have i : Fin (w.1.val+1) := 0
    have h := single_le_sum (s:=univ) (f:=fun j ↦ atomLoss (w.2 j)) (fun _ _ ↦ Nat.zero_le _) (mem_univ i)
    have loss : 2≤wordLoss w := (atom_loss hk _).1.trans h
    simp [show n-1≠n-wordLoss w by omega]
  have first := first_two_colors hk kn hn
  have norm := actual_four_fifths_all hk kn hn
  rw [eq] at choice norm
  rw [show ((profilePolynomial n k).coeff n:ℝ) = rowAlphabet n k n from congrFun eq n] at norm
  rcases choice with rfl|rfl
  · exact ⟨first.1,low,norm⟩
  · refine ⟨first.2.1,?_,?_⟩
    · simp [reflectedCoefficients,low]
    · simpa [reflected_lossNorm,reflectedCoefficients] using norm

theorem labelG_expansion {n q : ℕ} (hn : 1≤n) (hq : 1≤q) (a : ℕ→ℝ) (ap : 0<a n) :
    labelG n a q = q + (∑ h ∈ Ico 1 n, a h*(1/(q:ℝ))^(n-h-1)) / a n := by
  have qp : 0<(q:ℝ) := by exact_mod_cast hq
  have power (h : ℕ) (hi : h<n) :
      (q:ℝ)^h/(q:ℝ)^(n-1) = (1/q)^(n-h-1) := by
    have e : (q:ℝ)^(n-1) = q^h*q^(n-h-1) := by rw [←pow_add]; congr 1; omega
    rw [e,div_pow,one_pow]; field_simp
  rw [labelG,colorEval,←Ico_insert_right hn,sum_insert (by simp),add_div]
  have n1 : (q:ℝ)^n=(q:ℝ)^(n-1)*q := by rw [←pow_succ]; congr 1; omega
  rw [n1]
  have top : a n * ((q:ℝ)^(n-1)*q)/(a n * (q:ℝ)^(n-1))=q := by field_simp
  rw [top,add_right_inj,sum_div,sum_div]
  apply sum_congr rfl
  intro h hh
  have e := power h (mem_Ico.mp hh).2
  rw [←e]; ring

#print axioms actual_label_inputs
#print axioms inverse_step
end LongCycleBounds.OrdinaryEulerianGap
