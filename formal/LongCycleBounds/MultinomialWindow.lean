import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic

namespace LongCycleBounds.FixedCycleCount
open Finset
open scoped BigOperators

/-- Mark one object of each color in an ordered labelled partition. -/
theorem mark_all {ι : Type*} (S : Finset ι) (f : ι → ℕ) :
    (∏ i ∈ S, (f i+1)) * Nat.multinomial S (fun i ↦ f i+1) * (∑ i ∈ S,f i).factorial =
      ((∑ i ∈ S, f i)+S.card).factorial * Nat.multinomial S f := by
  have a := Nat.multinomial_spec S (fun i ↦ f i+1)
  simp only [Nat.factorial_succ,prod_mul_distrib,sum_add_distrib,sum_const,nsmul_eq_mul,Nat.cast_id,mul_one] at a
  have b := Nat.multinomial_spec S f
  rw [←b,←a]
  ring

private theorem cutoff {ι : Type*} (S : Finset ι) (k : ℕ) (d : ι → ℕ) :
    k * (∏ i ∈ S,(k+d i)) ≥ k^S.card*(k+∑ i ∈ S,d i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    rw [prod_insert ha,sum_insert ha,card_insert_of_notMem ha,pow_succ]
    have e := Nat.mul_le_mul_left (k+d a) ih
    nlinarith only [e,Nat.zero_le (k^S.card*d a*(∑ i ∈ S,d i))]

/-- A single inequality for any finite number of positive labels. Here f_i counts
the elements left on the i-th part after one element has been marked. -/
theorem multinomial_window_bound {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (m k : ℕ) (u : ι → ℕ) :
    k^S.card*(k+(m+S.card-k*S.card))*m.factorial *
      (∑ f ∈ (piAntidiag S m).filter (fun f ↦ ∀ i∈S,k≤f i+1),
        Nat.multinomial S (fun i ↦ f i+1) * ∏ i ∈ S, (u i)^(f i)) ≤
    k*(m+S.card).factorial*(∑ i ∈ S,u i)^m := by
  classical
  let good := fun f : ι → ℕ ↦ ∀ i∈S,k≤f i+1
  let P := piAntidiag S m
  let A := P.filter good
  have term (f : ι → ℕ) (hf : f∈A) :
      k^S.card*(k+(m+S.card-k*S.card))*m.factorial *
          (Nat.multinomial S (fun i ↦ f i+1) * ∏ i ∈ S,(u i)^(f i)) ≤
        k*(m+S.card).factorial*(Nat.multinomial S f * ∏ i ∈ S,(u i)^(f i)) := by
    obtain ⟨fp,ok⟩ := mem_filter.mp hf
    have fs := (mem_piAntidiag.mp fp).1
    let d := fun i ↦ f i+1-k
    have plus (i) (hi : i∈S) : k+d i=f i+1 := by dsimp [d];have := ok i hi;omega
    have sm := sum_congr (s₂:=S) rfl plus
    simp only [sum_add_distrib,sum_const,nsmul_eq_mul,Nat.cast_id,mul_one,fs] at sm
    rw [Nat.mul_comm S.card k] at sm
    have eq : (∑ i ∈ S,d i)=m+S.card-k*S.card := by omega
    have cut := cutoff S k d
    rw [prod_congr rfl plus,eq] at cut
    have marked := mark_all S f
    rw [fs] at marked
    have est := Nat.mul_le_mul_right (m.factorial*Nat.multinomial S (fun i ↦ f i+1)*
      (∏ i∈S,(u i)^(f i))) cut
    calc
      _ ≤ k*((∏ i ∈ S,(f i+1))*Nat.multinomial S (fun i ↦ f i+1)*m.factorial)*(∏ i∈S,(u i)^(f i)) := by
        convert est using 1 <;> ring
      _ = _ := by rw [marked];ring
  rw [mul_sum]
  apply (sum_le_sum term).trans
  rw [←mul_sum, sum_pow_eq_sum_piAntidiag]
  exact Nat.mul_le_mul_left _ (sum_le_sum_of_subset (filter_subset good P))

#print axioms mark_all
#print axioms multinomial_window_bound
end LongCycleBounds.FixedCycleCount
