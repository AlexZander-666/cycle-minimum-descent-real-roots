import LongCycleBounds.OccupancyProfiles
import Mathlib.Algebra.MvPolynomial.Basic

/-! Counting genuine functions from labelled balls to a partitioned finite set of slots. -/
noncomputable section
namespace LongCycleBounds.Occupancy
open Finset MvPolynomial
open scoped Classical

variable {I A : Type*} [Fintype I] [Fintype A] [DecidableEq A]

/-- The number of labelled inputs of a function assigned to each class. -/
def counts (f : I → A) (i : A) : ℕ := (univ.filter (fun s ↦ f s=i)).card

theorem sum_counts (f : I → A) : ∑ i, counts f i = Fintype.card I := by
  simpa only [counts,card_univ] using (card_eq_sum_card_fiberwise
    (s:=univ) (t:=univ) (f:=f) (fun _ _ ↦ mem_univ _)).symm

private def encode (f : A → ℕ) : A →₀ ℕ := Finsupp.indicator univ (fun i _ ↦ f i)

private theorem code_iff {a b : A → ℕ} : encode a = encode b ↔ a=b := by
  constructor
  · intro eq
    funext i
    have h := DFunLike.congr_fun eq i
    simpa [encode,Finsupp.indicator_of_mem] using h
  · rintro rfl; rfl

private theorem product_colors (f : I → A) :
    (∏ i, X (f i) : MvPolynomial A ℕ) = ∏ a, X a ^ counts f a := by
  rw [←prod_fiberwise_of_maps_to (s:=univ) (t:=univ) (g:=f) (fun _ _ ↦ mem_univ _)]
  apply prod_congr rfl
  intro a _
  unfold counts
  rw [←prod_const]
  apply prod_congr rfl
  intro i hi
  rw [(mem_filter.mp hi).2]

private theorem sum_colors (f : I → A) :
    (∑ i, X (f i) : MvPolynomial A ℕ) = ∑ a, (counts f a : MvPolynomial A ℕ) * X a := by
  rw [←sum_fiberwise_of_maps_to (s:=univ) (t:=univ) (g:=f) (fun _ _ ↦ mem_univ _)]
  apply sum_congr rfl
  intro a _
  unfold counts
  rw [←nsmul_eq_mul,←sum_const]
  apply sum_congr rfl
  intro i hi
  rw [(mem_filter.mp hi).2]

private theorem coeff_placed (a : A → ℕ) (f : I → A) :
    coeff (encode a) (∏ i, X (f i) : MvPolynomial A ℕ) = if counts f=a then 1 else 0 := by
  rw [product_colors,coeff_prod_X_pow]
  change (if encode a=encode (counts f) then _ else _) = _
  by_cases h : counts f=a
  · simp [h]
  · simp [code_iff,h,Ne.symm h]

private theorem coeff_profile (a l v : A → ℕ) :
    coeff (encode a) ((Nat.multinomial univ v : MvPolynomial A ℕ) *
      ∏ i, ((l i : MvPolynomial A ℕ)*X i)^(v i)) =
    if v=a then Nat.multinomial univ v * ∏ i, (l i)^(v i) else 0 := by
  simp only [mul_pow,prod_mul_distrib]
  rw [←mul_assoc]
  have constEq : (Nat.multinomial univ v : MvPolynomial A ℕ) * ∏ i, (l i: MvPolynomial A ℕ)^(v i)
      = C (Nat.multinomial univ v * ∏ i, (l i)^(v i)) := by simp
  rw [constEq,coeff_C_mul,coeff_prod_X_pow]
  change _*(if encode a=encode v then _ else _) = _
  by_cases h : v=a
  · simp [h]
  · simp [code_iff,h,Ne.symm h]

/-- A histogram fiber of maps into the actual slots has its multinomial size,
even if several slots belong to the same class or one class is empty. -/
theorem card_placements_profile (n : ℕ) (slot : I → A) (a : A → ℕ) (total : ∑ i,a i=n) :
    (univ.filter (fun b : Fin n → I ↦ counts (slot ∘ b)=a)).card =
      Nat.multinomial univ a * ∏ i, (counts slot i)^(a i) := by
  let P := (∑ i, X (slot i) : MvPolynomial A ℕ)^n
  have words : P=∑ b : Fin n → I, ∏ j, X (slot (b j)) := by
    simpa [P] using Fintype.prod_sum (fun (_:Fin n) i ↦ (X (slot i) : MvPolynomial A ℕ))
  have profile : P=∑ v ∈ piAntidiag (univ : Finset A) n,
      (Nat.multinomial univ v : MvPolynomial A ℕ) * ∏ i, ((counts slot i : MvPolynomial A ℕ)*X i)^(v i) := by
    unfold P
    rw [sum_colors, sum_pow_eq_sum_piAntidiag]
  have e := congrArg (coeff (encode a)) (words.symm.trans profile)
  simp only [coeff_sum] at e
  have each (b : Fin n → I) :
      coeff (encode a) (∏ j, X (slot (b j)) : MvPolynomial A ℕ)=if counts (slot ∘ b)=a then 1 else 0 :=
    coeff_placed a (slot ∘ b)
  simp only [each, coeff_profile, sum_ite_eq',if_pos (mem_piAntidiag.mpr ⟨total,fun _ _ ↦ mem_univ _⟩)] at e
  simpa only [sum_boole,Nat.cast_id] using e

theorem allocations_eq_card {h n k : ℕ} (slot : I → Fin h) :
    allocations n k (counts slot) =
      (univ.filter (fun b : Fin n → I ↦ ∀ i, k ≤ counts (slot ∘ b) i)).card := by
  let good := univ.filter (fun b : Fin n → I ↦ ∀ i, k ≤ counts (slot ∘ b) i)
  let profiles := (piAntidiag (univ : Finset (Fin h)) n).filter (fun a ↦ ∀ i,k ≤ a i)
  let p := fun b : Fin n → I ↦ counts (slot ∘ b)
  have maps : ∀ b ∈ good, p b ∈ profiles := by
    intro b hb
    refine mem_filter.mpr ⟨mem_piAntidiag.mpr ⟨?_,fun _ _ ↦ mem_univ _⟩,(mem_filter.mp hb).2⟩
    simpa only [p,Fintype.card_fin] using sum_counts (slot ∘ b)
  change _ = good.card
  rw [card_eq_sum_card_fiberwise maps]
  apply sum_congr rfl
  intro a ha
  have h := mem_filter.mp ha
  have hg : good.filter (fun b ↦ p b=a) = univ.filter (fun b ↦ p b=a) := by
    ext b
    simp only [good,mem_filter,mem_univ,true_and]
    exact ⟨fun e ↦ e.2,fun e ↦ ⟨(show ∀ i, k ≤ p b i from e ▸ h.2),e⟩⟩
  rw [hg]
  exact (card_placements_profile n slot a (mem_piAntidiag.mp h.1).1).symm

#print axioms card_placements_profile
#print axioms allocations_eq_card
end LongCycleBounds.Occupancy
