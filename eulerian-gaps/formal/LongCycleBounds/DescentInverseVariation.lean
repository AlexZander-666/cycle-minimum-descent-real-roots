import LongCycleBounds.WeightedPolynomialVariation
import LongCycleBounds.DescentActualCentral

/-! Exact relation between weighted ℓ¹ dominance of a reversed alphabet polynomial
and the coefficient error on the genuine ordinary descent transform. -/
noncomputable section
namespace LongCycleBounds.DescentMesh
open Polynomial Finset WeightedPolynomialVariation DescentNecklace

def inverseAlphabet (n k : ℕ) : ℝ[X] :=
  reflect n ((profilePolynomial n k).map (Rat.castHom ℝ))

theorem margin_reflect {r : ℝ} (p : ℝ[X]) {n : ℕ} (hn : 1 ≤ n)
    (deg : p.natDegree ≤ n) (zero : p.coeff 0=0) :
    margin r (reflect n p) = p.coeff n - lossNorm n p.coeff r := by
  have len : (reflect n p).divX.natDegree<n := by
    rw [natDegree_divX_eq_natDegree_tsub_one]
    have b := natDegree_reflect_le (N:=n) (p:=p)
    rw [max_eq_left deg] at b
    omega
  rw [margin,coeff_reflect,revAt_le (Nat.zero_le n),Nat.sub_zero,mass_range r _ len,mul_sum]
  congr 1
  let f (i : ℕ) := |p.coeff i| * r^(n-i)
  have each (i : ℕ) (hi : i ∈ range n) : r*(|(reflect n p).divX.coeff i| * r^i) =
      f (n-1-i) := by
    have bound := mem_range.mp hi
    simp only [f,coeff_divX,coeff_reflect,revAt_le (show i+1 ≤ n by omega),
      show n-1-i=n-(i+1) by omega, show n-(n-(i+1))=i+1 by omega,pow_succ]
    ring
  rw [sum_congr rfl each,sum_range_reflect,←sum_range_add_sum_Ico f hn]
  simp [f,lossNorm,zero]

theorem actual_inverse_margin {n : ℕ} (hn : 1 ≤ n) (k : ℕ) (r : ℝ) :
    margin r (inverseAlphabet n k) = ((profilePolynomial n k).coeff n : ℝ) -
      lossNorm n (fun h ↦ ((profilePolynomial n k).coeff h : ℝ)) r := by
  let P := (profilePolynomial n k).map (Rat.castHom ℝ)
  have deg : P.natDegree ≤ n := natDegree_map_le.trans (by rw [←alphabet_eq_profile hn];apply alphabet_degree)
  have zero : P.coeff 0=0 := by simp [P,←alphabet_eq_profile hn,alphabet_zero hn]
  simpa [inverseAlphabet, P,lossNorm,coeff_map] using margin_reflect (r:=r) P hn deg zero

/-- A kernel-checked conversion to the precise original coefficient budget at radius 4/5. -/
theorem actual_four_fifths_iff {n : ℕ} (hn : 1 ≤ n) (k : ℕ) :
    0 < margin (4/5) (inverseAlphabet n k) ↔
    lossNorm n (fun h ↦ ((profilePolynomial n k).coeff h : ℝ)) (4/5) <
      ((profilePolynomial n k).coeff n : ℝ) := by
  rw [actual_inverse_margin hn]
  exact sub_pos

#print axioms margin_reflect
#print axioms actual_inverse_margin
#print axioms actual_four_fifths_iff
end LongCycleBounds.DescentMesh
