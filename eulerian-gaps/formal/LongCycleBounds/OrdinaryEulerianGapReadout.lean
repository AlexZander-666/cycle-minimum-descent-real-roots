import LongCycleBounds.DescentEulerianBrackets
import LongCycleBounds.DescentInverseMixtures
import LongCycleBounds.DescentActualReciprocal
import LongCycleBounds.DescentGridRoots
import LongCycleBounds.EulerianSturm

noncomputable section
namespace LongCycleBounds.OrdinaryEulerianGap
open Polynomial Finset LongCycles LongCycleFinite DescentMesh DescentNecklace DescentTwoLetters Real

/-- Intervals between consecutive Eulerian zeros exhaust the lower degree, including
multiplicities. The sign test uses the unreduced row D and the next Eulerian row. -/
theorem strict_between_eulerian {d : ℕ} {D : ℝ[X]} (d0 : D.coeff 0=0)
    (deg : D.natDegree ≤ d+1)
    (signs : ∀ t : ℝ,t<0 → (eulerian (d+1+1)).eval t=0 →
      0<D.eval t * (eulerian (d+1+1+1)).eval t) :
    StrictNegativeInterlacing D.divX (eulerian (d+1+1)) d := by
  classical
  obtain ⟨s,fac,mono,neg⟩ := eulerian_simple_negative (d+1)
  have qfac : X*D.divX=D := by simpa [d0] using X_mul_divX_add D
  have node (i : Fin (d+1)) : (eulerian (d+1+1)).eval (s i)=0 := by
    rw [fac]
    exact Lagrange.eval_nodal_at_node (s:=univ) (v:=s) (mem_univ i)
  have directs (i : Fin (d+1)) : 0 < D.divX.eval (s i)*(eulerian (d+1+1)).derivative.eval (s i) := by
    have pos := signs (s i) (neg i) (node i)
    rw [longEulerian_succ (d+1+1),eval_add,eval_mul,eval_mul,eval_mul,node i,mul_zero,zero_add,
      eval_X,eval_sub,eval_one,←qfac,eval_mul,eval_X] at pos
    have h : 0 < (s i)^2*(1-s i)*(D.divX.eval (s i)*(eulerian (d+1+1)).derivative.eval (s i)) := by
      convert pos using 1; ring
    exact pos_of_mul_pos_right h (mul_nonneg (sq_nonneg _) (by linarith [neg i]))
  have alt (i : Fin (d+1)) : 0 < (-1:ℝ)^(d-i.val)*D.divX.eval (s i) := by
    have h := Sturm.node_derivative_sign s mono i
    rw [←fac,show d+1-1-i.val=d-i.val by omega] at h
    have res := mul_pos h (directs i)
    have h' : 0 < ((-1:ℝ)^(d-i.val)*D.divX.eval (s i)) * ((eulerian (d+1+1)).derivative.eval (s i))^2 := by
      rw [show ∀ x y z : ℝ, (x*y)*(z*y) = (x*z)*y^2 by intros; ring] at res
      exact res
    exact pos_of_mul_pos_left h' (sq_nonneg _)
  have flip (i : Fin d) : D.divX.eval (s i.castSucc)*D.divX.eval (s i.succ)<0 := by
    have left := alt i.castSucc
    have right := alt i.succ
    simp only [Fin.val_castSucc,Fin.val_succ] at left right
    have p := mul_pos left right
    rw [show d-i.val = (d-(i.val+1))+1 by have := i.isLt; omega,pow_succ] at p
    have same : ((-1:ℝ)^(d-(i.val+1)))*((-1:ℝ)^(d-(i.val+1)))=1 := by rw [←mul_pow]; simp
    nlinarith only [p,congrArg (fun z : ℝ ↦ z*(D.divX.eval (s i.castSucc)*D.divX.eval (s i.succ))) same]
  have hit (i : Fin d) := root_between D.divX (mono (show i.castSucc < i.succ by exact Fin.castSucc_lt_succ)) (flip i)
  choose r hr using hit
  have order : StrictMono r := by
    intro i j ij
    have le : i.succ ≤ j.castSucc := by exact ij
    exact (hr i).2.1.trans ((mono.monotone le).trans_lt (hr j).1)
  have nz : D.divX≠0 := by intro h; simpa [h] using alt 0
  have degQ : D.divX.natDegree ≤ d := by rw [natDegree_divX_eq_natDegree_tsub_one]; omega
  have mon := (eulerian_degree_monic (d+1)).2
  exact ⟨r,s,leadingCoeff_ne_zero.mpr nz,mon.leadingCoeff.symm ▸ one_ne_zero,
    factor_of_degree_bound r nz degQ order.injective (fun i ↦ (hr i).2.2),
    by simpa [mon.leadingCoeff] using fac,order,mono,fun i ↦ (hr i).2.1.trans (neg _),
    neg,fun i ↦ ⟨(hr i).1,(hr i).2.1⟩⟩

theorem original_of_eulerian_signs {n k : ℕ} (hn : 6 ≤ n) (hk : 3 ≤ k)
    (signs : ∀ t : ℝ,t<0 → (eulerian (n-1)).eval t=0 →
      0<((row n k).map (Int.castRingHom ℝ)).eval t*(eulerian n).eval t) :
    StrictNegativeInterlacing (EulerianBrackets.originalQuotient n k) (eulerian (n-1)) (n-3) := by
  let D := (row n k).map (Int.castRingHom ℝ)
  have d0 : D.coeff 0=0 := by
    obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n≠0)
    simp [D,coeff_map,constant_zero m (by omega : 2 ≤ k)]
  have f := strict_between_eulerian (d:=n-3) (D:=D) d0
    (show D.natDegree ≤ n-3+1 by simpa only [show n-3+1=n-2 by omega] using (row_degree_cap (by omega : 3≤n) hk))
    (by simpa only [show n-3+1+1=n-1 by omega,show n-1+1=n by omega] using signs)
  simpa only [D,EulerianBrackets.originalQuotient,show n-3+1+1=n-1 by omega] using f

#print axioms original_of_eulerian_signs
end LongCycleBounds.OrdinaryEulerianGap
