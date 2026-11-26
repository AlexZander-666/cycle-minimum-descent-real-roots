import LongCycleBounds.DescentFiniteMixtures
import LongCycleBounds.DescentFiveMixtures
import LongCycleBounds.DescentFiniteCertificatesThrough32

/-! All fixed-size nonzero nonnegative mixtures of genuine rows in the finite prefix. -/
noncomputable section
namespace LongCycleBounds.DescentNecklace
open Polynomial Finset LongCycleFinite DescentTwoLetters

def commonMixtureIntervals (n : ℕ) : Prop :=
  ∃ a : Array LongCycleFinite.Dyadic, a.size=n-2 ∧
    ∀ w : ℕ→ℝ, (∀ k ∈ Icc 3 n, 0≤w k) → (∃ k ∈ Icc 3 n, 0<w k) →
      let p := ∑ k ∈ Icc 3 n,C (w k)*(row n k).map (Int.castRingHom ℝ)
      ∃ q : ℝ[X], p=X*q ∧ Nonempty (QuotientMeshRoots q a (n-3)) ∧
        p.Splits ∧ p.roots.Nodup ∧ 0∈p.roots ∧ p.roots.card=n-2 ∧
        (p.roots.filter (· < 0)).card=n-3

theorem mixtures_through32 {n : ℕ} (hn : 3≤n) (upper : n≤32) (five : n≠5) :
    commonMixtureIntervals n := by
  obtain ⟨a,rows,size,checked⟩ := FrozenCertificates.finite_certificate_through32 hn upper five
  exact ⟨a,size,fun w h p ↦ representative_mixtures hn size checked w h p⟩

theorem mixture_splits_through32 {n : ℕ} (hn : 3≤n) (upper : n≤32)
    (w : ℕ→ℝ) (h : ∀ k ∈ Icc 3 n, 0≤w k) (positive : ∃ k ∈ Icc 3 n, 0<w k) :
    (∑ k ∈ Icc 3 n,C (w k)*(row n k).map (Int.castRingHom ℝ)).Splits := by
  by_cases five : n=5
  · subst n; exact (five_mixture_roots w h positive).2.1
  · obtain ⟨_,_,family⟩ := mixtures_through32 hn upper five
    obtain ⟨_,_,_,split,_⟩ := family w h positive
    exact split

#print axioms mixtures_through32
#print axioms mixture_splits_through32
end LongCycleBounds.DescentNecklace
