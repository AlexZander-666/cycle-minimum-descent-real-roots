import LongCycleBounds.OrdinaryEulerianCentralSign

noncomputable section
namespace LongCycleBounds.OrdinaryEulerianGap
open LongCycleFinite Finset Polynomial DescentMesh DescentNecklace DescentTwoLetters Band PoleBridge Real LongCycles

/-- The two inputs to the exterior test are the true inverse alphabet coefficients
and their reflection. The central interval, the reciprocal axis, and the passage
from opposite endpoint signs to complete interlacing are discharged here. -/
theorem original_large_of_exterior {n k : ℕ} (hn : 128≤n) (hk : 3≤k) (kn : k≤n)
    (ext : ∀ a : ℕ→ℝ,
      (a = (fun h ↦ ((profilePolynomial n k).coeff h : ℝ)) ∨
       a = reflectedCoefficients n (fun h ↦ ((profilePolynomial n k).coeff h : ℝ))) →
      ∀ x : ℝ, 5/2*sqrt ((n:ℝ)-1) ≤ x → (eulerian (n-1)).eval (-exp (-x))=0 →
       0<(descentTransform n a).eval (-exp (-x))*(eulerian n).eval (-exp (-x))) :
    StrictNegativeInterlacing (EulerianBrackets.originalQuotient n k) (eulerian (n-1)) (n-3) := by
  let a (h : ℕ) : ℝ := (profilePolynomial n k).coeff h
  have ab : lossNorm n a (4/5)<a n := actual_four_fifths_all hk kn hn
  have half (b : ℕ→ℝ) (choice : b=a ∨ b=reflectedCoefficients n a)
      (u : ℝ) (umin : -1≤u) (uneg : u<0) (zero : (eulerian (n-1)).eval u=0) :
      0<(descentTransform n b).eval u*(eulerian n).eval u := by
    let x := -log (-u)
    have hx : 0≤x := neg_nonneg.mpr (log_nonpos (by linarith) (by linarith))
    have um : -exp (-x) = u := by simp only [x,neg_neg,exp_log (by linarith : 0 < -u)]
    rw [←um] at zero ⊢
    rcases le_total x (5/2*sqrt ((n:ℝ)-1)) with central|exterior
    · apply central_transform_sign hn b _ hx central zero
      rcases choice with rfl|rfl
      · exact ab
      · rw [reflected_lossNorm]
        simpa [reflectedCoefficients] using ab
    · exact ext b choice x exterior zero
  apply original_of_eulerian_signs (by omega) hk
  intro t neg zero
  rw [original_eq_descentTransform (by omega : 0<n) k]
  by_cases side : -1≤t
  · exact half a (Or.inl rfl) t side neg zero
  have tinv : t⁻¹<0 := inv_lt_zero.mpr neg
  have t0 : t⁻¹≠0 := ne_of_lt tinv
  have coarse : -1≤t⁻¹ := by
    rw [inv_eq_one_div]
    exact (le_div_iff_of_neg neg).mpr (by linarith)
  have pre := eulerian_reciprocity (n-2) t0
  simp only [inv_inv,show n-2+1=n-1 by omega,zero,mul_zero] at pre
  have res := half (reflectedCoefficients n a) (Or.inr rfl) t⁻¹ coarse tinv pre.symm
  have ord := eulerian_reciprocity (n-1) t0
  simp only [inv_inv,show n-1+1=n by omega] at ord
  have rev := transform_reflect n a t0
  simp only [inv_inv] at rev
  rw [←rev,←ord] at res
  have scaled : 0 < (t⁻¹^(n-1))^2*((descentTransform n a).eval t*(eulerian n).eval t) := by
    calc (0:ℝ) < _ := res
         _ = _ := by ring
  exact pos_of_mul_pos_right scaled (sq_nonneg _)

#print axioms original_large_of_exterior
end LongCycleBounds.OrdinaryEulerianGap
