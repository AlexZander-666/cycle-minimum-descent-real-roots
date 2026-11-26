import LongCycleBounds.DescentBoundaryOrderedSigns
import LongCycleBounds.DescentLowerCutoffPilot

noncomputable section
namespace LongCycleBounds.DescentBoundary
open Finset Polynomial DescentNecklace

theorem all_mixtures_of_certificate {n : ℕ} (hn : 3 ≤ n) (cert : LowerCutoffMeshCertificate n)
    (w : ℕ → ℝ) (hw : ∀ k ∈ Icc 1 n, 0 ≤ w k) (pos : ∃ k ∈ Icc 1 n, 0 < w k) :
    (mixture n w).Splits ∧ (mixture n w).roots.Nodup ∧ ∀ x ∈ (mixture n w).roots, x ≤ 0 := by
  obtain ⟨nodes, rows, sz, checked, lower⟩ := cert
  let ix (i : Fin (n-2)) : Fin nodes.size := ⟨i.val, by rw [sz]; exact i.isLt⟩
  let a (i : Fin (n-2)) := (nodes[(ix i).val]'(ix i).isLt).value
  obtain ⟨neg, mono⟩ := representativeMesh_geometry checked
  apply all_mixtures_of_ordered_signs hn a (fun _ _ h ↦ mono (show ix _ < ix _ from h))
    (fun i ↦ neg (ix i)) _ w hw pos
  intro k hk i
  have bounds := mem_Icc.mp hk
  have raw : RawSharedSigns (realRow n k) nodes := by
    by_cases large : 3 ≤ k
    · exact rawSharedSigns_of_representativeChecks hn large bounds.2 checked
    · exact lower k (by omega)
  simpa only [rawMeshNegative, decide_eq_true_eq, sz, ix, a] using raw (ix i)

theorem six_all_weights (w : ℕ → ℝ) (hw : ∀ k ∈ Icc 1 6, 0 ≤ w k)
    (pos : ∃ k ∈ Icc 1 6, 0 < w k) :
    (mixture 6 w).Splits ∧ (mixture 6 w).roots.Nodup ∧ ∀ x ∈ (mixture 6 w).roots, x ≤ 0 :=
  all_mixtures_of_certificate (by decide) Size6.lower_cutoff_mesh w hw pos
theorem seven_all_weights (w : ℕ → ℝ) (hw : ∀ k ∈ Icc 1 7, 0 ≤ w k)
    (pos : ∃ k ∈ Icc 1 7, 0 < w k) :
    (mixture 7 w).Splits ∧ (mixture 7 w).roots.Nodup ∧ ∀ x ∈ (mixture 7 w).roots, x ≤ 0 :=
  all_mixtures_of_certificate (by decide) Size7.lower_cutoff_mesh w hw pos

#print axioms all_mixtures_of_certificate
#print axioms six_all_weights
#print axioms seven_all_weights
end LongCycleBounds.DescentBoundary
