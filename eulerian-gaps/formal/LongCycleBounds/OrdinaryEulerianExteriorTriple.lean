import LongCycleBounds.OrdinaryEulerianExteriorDecay

noncomputable section
namespace LongCycleBounds.OrdinaryEulerianExterior
open Outer Real

private theorem scalar_core {W V X Y : ℝ} (W0 : 0<W) (V0 : 0≤V)
    (bound : (V≤W/50 ∧ 1/2≤X ∧ Y≤6) ∨
      (V≤W/7 ∧ 119/144≤X ∧ Y≤2*(169/144))) :
    (888/2401)*W < W*X-V*Y := by
  rcases bound with ⟨we,lo,hi⟩|⟨we,lo,hi⟩
  · nlinarith only [W0,we,mul_nonneg W0.le (sub_nonneg.mpr lo),mul_nonneg V0 (sub_nonneg.mpr hi)]
  · nlinarith only [W0,we,mul_nonneg W0.le (sub_nonneg.mpr lo),mul_nonneg V0 (sub_nonneg.mpr hi)]

private theorem select_core {j : ℕ} {W V A B X : ℝ} (W0 : 0<W) (V0 : 0≤V)
    (weak : V≤W/7) (small : j+1≤2 → V≤W/50)
    (incA : 1/2≤A ∧ A≤3 ∧ (2≤j → 119/144≤A ∧ A≤169/144))
    (incB : 1/2≤B ∧ B≤3 ∧ (2≤j+1 → 119/144≤B ∧ B≤169/144))
    (select : X=A ∨ X=B) :
    (888/2401)*W < W*X-V*(A+B) := by
  apply scalar_core W0 V0
  by_cases low : j+1≤2
  · exact Or.inl ⟨small low,select.elim (fun e ↦ e ▸ incA.1) (fun e ↦ e ▸ incB.1),
      by linarith only [incA.2.1,incB.2.1]⟩
  · have ia := incA.2.2 (by omega)
    have ib := incB.2.2 (by omega)
    exact Or.inr ⟨weak,select.elim (fun e ↦ e ▸ ia.1) (fun e ↦ e ▸ ib.1),
      by linarith only [ia.2,ib.2]⟩

/-- A single neighboring slot and sign work for all admissible colors at once.
The zero-indexed mode m corresponds to positive label m+1. -/
theorem directed_core {p : ℕ} (hp : 72≤p) {x : ℝ} (hx : 0<x) (region : 5*sqrt p/2≤x) :
    let m := mode p x hx
    ∃ (s : ℕ) (ε : ℝ), |ε|=1 ∧ |(m:ℝ)-s|≤1 ∧ ∀ G : ℕ→ℝ,
      (∀ j : ℕ, 1/2≤G (j+1)-G j ∧ G (j+1)-G j≤3 ∧
          (2≤j → 119/144≤G (j+1)-G j ∧ G (j+1)-G j≤169/144)) →
      let f (i : ℕ) := (-1:ℝ)^i*weight p x i*(G i-G s)
      (888/2401)*weight p x m < ε*(f m+leftAt f m 1+f (m+1)) := by
  dsimp only
  let w := weight p x
  have W0 (j : ℕ) : 0<w j := weight_pos _ _ _
  have weak := neighbors_min_le p (by omega) x hx region
  have small := neighbors_small p hp x hx
  change min (leftAt w (mode p x hx) 1) (w (mode p x hx+1))≤ w (mode p x hx)/7 at weak
  change mode p x hx≤2 → min (leftAt w (mode p x hx) 1) (w (mode p x hx+1))≤w (mode p x hx)/50 at small
  generalize hmode : mode p x hx=m at weak small ⊢
  cases m with
  | zero =>
    refine ⟨1,-1,by norm_num,by norm_num,?_⟩
    intro G g
    simp only [Nat.zero_add,leftAt,if_neg (by decide : ¬1≤0),pow_zero,one_mul,
      sub_self,mul_zero,add_zero,neg_one_mul]
    change (888/2401)*w 0 < -(w 0*(G 0-G 1))
    nlinarith only [W0 0,mul_nonneg (W0 0).le (sub_nonneg.mpr (g 0).1)]
  | succ j =>
    simp only [leftAt,if_pos (show 1≤j+1 by omega),Nat.add_one_sub_one] at weak small
    let E := (-1:ℝ)^j
    have e2 : E*E=1 := by dsimp [E];rw [←mul_pow];norm_num
    have sqE : |E|=1 := by simp [E]
    by_cases right : w j≤w (j+1+1)
    · rw [min_eq_left right] at weak small
      refine ⟨j+1+1,E,sqE,?_,?_⟩
      · push_cast; rw [show (j:ℝ)+1-((j+1)+1)= -1 by ring]; norm_num
      intro G g
      let A := G (j+1)-G j
      let B := G (j+1+1)-G (j+1)
      have cap := select_core (j:=j) (W0 (j+1)) (W0 j).le weak small (g j) (g (j+1)) (X:=B) (Or.inr rfl)
      change (888/2401)*w (j+1)<_
      apply cap.trans_eq
      simp only [leftAt,if_pos (show 1≤j+1 by omega),Nat.add_one_sub_one,sub_self,mul_zero,add_zero]
      change w (j+1)*B-w j*(A+B)= E*((-1:ℝ)^(j+1)*w (j+1)*(G (j+1)-G (j+1+1))+(-1)^j*w j*(G j-G (j+1+1)))
      rw [pow_succ]
      change _ = E*(E * -1*w (j+1)*(G (j+1)-G (j+1+1))+ E*w j*(G j-G (j+1+1)))
      dsimp only [A,B]
      linear_combination (w (j+1)*(G (j+1)-G (j+1+1))-w j*(G j-G (j+1+1)))*(e2)
    · rw [min_eq_right (le_of_not_ge right)] at weak small
      refine ⟨j,-E,by simpa only [abs_neg] using sqE,?_,?_⟩
      · push_cast; rw [show (j:ℝ)+1-j=1 by ring]; norm_num
      intro G g
      let A := G (j+1)-G j
      let B := G (j+1+1)-G (j+1)
      have cap := select_core (j:=j) (W0 (j+1)) (W0 (j+1+1)).le weak small (g j) (g (j+1)) (X:=A) (Or.inl rfl)
      change (888/2401)*w (j+1)<_
      apply cap.trans_eq
      simp only [leftAt,if_pos (show 1≤j+1 by omega),Nat.add_one_sub_one,sub_self,mul_zero,add_zero]
      change w (j+1)*A-w (j+1+1)*(A+B)= -E*((-1:ℝ)^(j+1)*w (j+1)*(G (j+1)-G j)+(-1)^(j+1+1)*w (j+1+1)*(G (j+1+1)-G j))
      rw [pow_succ _ (j+1),pow_succ _ j]
      change _ = -E*(E * -1*w (j+1)*(G (j+1)-G j)+E * -1 * -1*w (j+1+1)*(G (j+1+1)-G j))
      dsimp only [A,B]
      linear_combination (-w (j+1)*(G (j+1)-G j)+w (j+1+1)*(G (j+1+1)-G j))*e2

#print axioms directed_core
end LongCycleBounds.OrdinaryEulerianExterior
