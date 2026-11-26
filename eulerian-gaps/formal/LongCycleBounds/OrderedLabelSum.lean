import LongCycleBounds.SupportRatio
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv

namespace LongCycleBounds.FixedCycleCount
open Finset
noncomputable section

/-- A positive label of size d+h+1 is split at h interior cuts.
Subtracting one from each positive piece gives a weak composition of d. -/
def labelPieces (h d : ℕ) := (univ : Finset (Fin (h+1))).finsuppAntidiag d

theorem labelPieces_count (h d : ℕ) : (labelPieces h d).card=(d+h).choose h := by
  rw [labelPieces,card_finsuppAntidiag_nat_eq_choose]
  simp only [card_univ,Fintype.card_fin]
  rw [show h+1+d-1=d+h by omega,←Nat.choose_symm (show d≤d+h by omega),show d+h-d=h by omega]

theorem labelPieces_count_bound (h d : ℕ) : h.factorial * (labelPieces h d).card ≤ (d+h+1)^h := by
  rw [labelPieces_count,←Nat.descFactorial_eq_factorial_mul_choose]
  exact ((d+h).descFactorial_le_pow h).trans (Nat.pow_le_pow_left (by omega) _)

/-- Coefficient of an ordered sequence of h+1 genuine cycle moments before dividing by (h+1)!.
The row length is m+h+1, and the total positive label d+h+1. -/
def orderedLabelSum (h m k d : ℕ) : ℕ :=
  ∑ g ∈ labelPieces h d,
    ∑ f ∈ (piAntidiag (univ : Finset (Fin (h+1))) m).filter (fun f ↦ ∀ i,k≤f i+1),
      Nat.multinomial univ (fun i ↦ f i+1) * ∏ i, (g i+1)^(f i)

/-- Joint bound with the exact marking factorial and stars-and-bars divisor. -/
theorem orderedLabelSum_bound (h m k d : ℕ) :
    k^(h+1)*(k+(m+(h+1)-k*(h+1)))*m.factorial*h.factorial*orderedLabelSum h m k d ≤
      k*(m+(h+1)).factorial*(d+h+1)^(m+h) := by
  let S : Finset (Fin (h+1)) := univ
  let A := k^(h+1)*(k+(m+(h+1)-k*(h+1)))*m.factorial
  let B := k*(m+(h+1)).factorial
  let F := fun g : Fin (h+1) →₀ ℕ ↦
    ∑ f ∈ (piAntidiag S m).filter (fun f ↦ ∀ i,k≤f i+1),
      Nat.multinomial S (fun i ↦ f i+1) * ∏ i, (g i+1)^(f i)
  have one (g) (hg : g∈labelPieces h d) : A*F g≤B*(d+h+1)^m := by
    have eq := (mem_finsuppAntidiag.mp hg).1
    have row := multinomial_window_bound S m k (fun i ↦ g i+1)
    simpa [A,B,F,S,sum_add_distrib,eq,add_assoc] using row
  have hs := sum_le_sum one
  rw [←mul_sum] at hs
  simp only [sum_const,nsmul_eq_mul,Nat.cast_id] at hs
  have hc := labelPieces_count_bound h d
  change A*h.factorial*(∑ g ∈ labelPieces h d,F g) ≤ B*(d+h+1)^(m+h)
  calc
    _ = h.factorial*(A*(∑ g ∈ labelPieces h d,F g)) := by ring
    _ ≤ h.factorial*((labelPieces h d).card*(B*(d+h+1)^m)) := Nat.mul_le_mul_left _ hs
    _ = (B*(d+h+1)^m)*(h.factorial*(labelPieces h d).card) := by ring
    _ ≤ (B*(d+h+1)^m)*(d+h+1)^h := Nat.mul_le_mul_left _ hc
    _ = _ := by rw [pow_add,mul_assoc]

#print axioms labelPieces_count_bound
#print axioms orderedLabelSum_bound
end
end LongCycleBounds.FixedCycleCount
