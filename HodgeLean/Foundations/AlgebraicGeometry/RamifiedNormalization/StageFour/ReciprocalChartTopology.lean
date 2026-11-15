import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Analysis.Complex.Basic

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped OnePoint
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- Two reciprocal affine charts on a compact Hausdorff fibre retain zero and infinity literally. -/
theorem reciprocal_chart_compactification
    {E : Type*} [TopologicalSpace E] [T2Space E] [CompactSpace E]
    (j₁ j₂ : ℂ → E) (hj₁ : Topology.IsEmbedding j₁)
    (hcover : ∀ x, (∃ z, j₁ z = x) ∨ ∃ z, j₂ z = x)
    (hcross : ∀ z : ℂ, z ≠ 0 → j₂ z = j₁ z⁻¹)
    (hmiss : j₂ 0 ∉ Set.range j₁) :
    ∃ e : E ≃ₜ OnePoint ℂ,
      (∀ z : ℂ, e (j₁ z) = (z : OnePoint ℂ)) ∧ e (j₂ 0) = ∞ := by
  have hrange : Set.range j₁ = {j₂ 0}ᶜ := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩ hx
      exact hmiss ⟨z, hx⟩
    · intro hx
      rcases hcover x with ⟨z, rfl⟩ | ⟨z, rfl⟩
      · exact ⟨z, rfl⟩
      · have hz : z ≠ 0 := by
          intro hz
          apply hx
          rw [hz]
          exact Set.mem_singleton _
        exact ⟨z⁻¹, (hcross z hz).symm⟩
  let H := OnePoint.equivOfIsEmbeddingOfRangeEq (j₂ 0) j₁ hj₁ hrange
  have hfinite (z : ℂ) : H (z : OnePoint ℂ) = j₁ z :=
    OnePoint.equivOfIsEmbeddingOfRangeEq_apply_coe _ _ _ _ z
  have hinfty : H ∞ = j₂ 0 :=
    OnePoint.equivOfIsEmbeddingOfRangeEq_apply_infty _ _ _ _
  refine ⟨H.symm, ?_, ?_⟩
  · intro z
    rw [← hfinite z, H.symm_apply_apply]
  · rw [← hinfty, H.symm_apply_apply]

end AlgebraicGeometry.RamifiedNormalization.StageFour
