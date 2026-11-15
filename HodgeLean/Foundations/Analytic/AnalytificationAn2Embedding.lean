import HodgeLean.Foundations.Analytic.AnalytificationAn2Affine

noncomputable section

open Topology AlgebraicGeometry
open AlgebraicGeometry.ComplexPoint

namespace HodgeLean.Foundations.Analytic

theorem AnalytificationAn2_isEmbedding_coordinates
    {A : Type} [CommRing A] [Algebra ℂ A] {ι : Type} [Finite ι]
    (c : ι → A)
    (h : ∀ a : A, ∃ p : MvPolynomial ι ℂ,
      ∀ φ : A →ₐ[ℂ] ℂ, φ a = MvPolynomial.eval (fun i ↦ φ (c i)) p) :
    @IsEmbedding (A →ₐ[ℂ] ℂ) (ι → ℂ)
      (ComplexPoint.affineAlgebraHomTopology A) inferInstance
      (fun φ i ↦ φ (c i)) := by
  let F : (A →ₐ[ℂ] ℂ) → (ι → ℂ) := fun φ i ↦ φ (c i)
  have hF : Continuous F := continuous_pi fun i ↦
    ComplexPoint.continuous_affineAlgebraHom_apply A (c i)
  rw [isEmbedding_iff]
  constructor
  · rw [isInducing_iff]
    apply le_antisymm
    · exact continuous_iff_le_induced.mp hF
    · change TopologicalSpace.induced F inferInstance ≤
        TopologicalSpace.induced (fun φ : A →ₐ[ℂ] ℂ ↦ (φ : A → ℂ)) inferInstance
      let t := TopologicalSpace.induced F (inferInstance : TopologicalSpace (ι → ℂ))
      change t ≤ TopologicalSpace.induced (fun φ : A →ₐ[ℂ] ℂ ↦ (φ : A → ℂ)) inferInstance
      letI : TopologicalSpace (A →ₐ[ℂ] ℂ) := t
      apply continuous_iff_le_induced.mp
      rw [continuous_pi_iff]
      intro a
      obtain ⟨p, hp⟩ := h a
      have hc : Continuous fun φ : A →ₐ[ℂ] ℂ ↦ MvPolynomial.eval (F φ) p :=
        (MvPolynomial.continuous_eval p).comp continuous_induced_dom
      simpa only [F, hp] using hc
  · intro φ ψ hφψ
    ext a
    obtain ⟨p, hp⟩ := h a
    rw [hp φ, hp ψ]
    exact congrArg (fun v ↦ MvPolynomial.eval v p) hφψ

end HodgeLean.Foundations.Analytic
