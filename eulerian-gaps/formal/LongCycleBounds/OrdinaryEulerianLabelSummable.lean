import LongCycleBounds.OrdinaryEulerianLabelReadout

noncomputable section
namespace LongCycleBounds.OrdinaryEulerianGap
open DescentMesh DescentNecklace Outer Real

/-- Unit bounds on consecutive labels control every interval, including label zero
when the input is the zero-indexed sequence G(i)=g(i+1). -/
theorem lipschitz_steps {G : ℕ→ℝ} {L : ℝ}
    (step : ∀ i, |G (i+1)-G i|≤L) (i j : ℕ) :
    |G i-G j| ≤ L*|(i:ℝ)-j| := by
  have shift (s d : ℕ) : |G (s+d)-G s| ≤ L*d := by
    induction d with
    | zero => simp
    | succ d ih =>
      calc
        _ ≤ |G ((s+d)+1)-G (s+d)|+|G (s+d)-G s| := abs_sub_le _ _ _
        _ ≤ _ := add_le_add (step _) ih
        _ = _ := by push_cast; ring
  rcases le_total j i with le|le
  · obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le le
    simpa [abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) d)] using shift j d
  · obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le le
    rw [abs_sub_comm (G i),abs_sub_comm (i:ℝ)]
    simpa [abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) d)] using shift i d

/-- A function bounded by a linear function of the positive slot label gives an
absolutely summable alternating moment for every positive x and every exponent. -/
theorem summable_linear_weight (p : ℕ) {x : ℝ} (hx : 0<x) (G : ℕ→ℝ)
    {L : ℝ} (size : ∀ i : ℕ, |G i|≤L*((i:ℝ)+1)) :
    Summable (fun i : ℕ ↦ (-1:ℝ)^i * weight p x i * G i) := by
  apply ((summable_weight (p+1) x hx).mul_left L).of_norm_bounded
  intro i
  rw [Real.norm_eq_abs,abs_mul,abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul,abs_of_pos (weight_pos ..)]
  calc _ ≤ _ := mul_le_mul_of_nonneg_left (size i) (weight_pos ..).le
       _ = _ := by unfold weight; rw [pow_succ]; ring

theorem actual_label_exterior_inputs {n k : ℕ} (hn : 128≤n) (hk : 3≤k) (kn : k≤n)
    {a : ℕ→ℝ} (choice : a=(fun h ↦ ((profilePolynomial n k).coeff h:ℝ)) ∨
      a=reflectedCoefficients n (fun h ↦ ((profilePolynomial n k).coeff h:ℝ)))
    {x : ℝ} (hx : 0<x) :
    let G := fun i : ℕ ↦ labelG n a (i+1)
    (∀ i j : ℕ, |G i-G j|≤3*|(i:ℝ)-j|) ∧
    Summable (fun i : ℕ ↦ (-1:ℝ)^i*weight (n-1) x i*G i) ∧
    Summable (fun i : ℕ ↦ (-1:ℝ)^i*weight (n-1) x i*((i:ℝ)+1)) := by
  let G := fun i : ℕ ↦ labelG n a (i+1)
  obtain ⟨g1,inc⟩ := actual_label_steps hn hk kn choice
  have unit (i : ℕ) : |G (i+1)-G i|≤3 := by
    have h := inc (i+1) (by omega)
    exact abs_le.mpr ⟨by linarith only [h.1],h.2.1⟩
  have bound := lipschitz_steps unit
  refine ⟨bound,summable_linear_weight (n-1) hx G (L:=3) (fun i ↦ ?_),
    summable_linear_weight (n-1) hx (fun i ↦ (i:ℝ)+1) (L:=1) (fun i ↦ ?_)⟩
  · have h := bound i 0
    have z : G 0=0 := g1
    simp only [z,sub_zero,Nat.cast_zero,abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) i)] at h
    linarith only [h]
  · rw [abs_of_nonneg (by positivity),one_mul]

#print axioms actual_label_exterior_inputs
end LongCycleBounds.OrdinaryEulerianGap
