import HodgeLean.Foundations.QuotientDuality.MonomialAffinePointAction
import HodgeLean.Foundations.QuotientDuality.MonomialAffineAutomorphism

/-! Algebraic isomorphisms and continuity for the affine point action. -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.QuotientDuality

theorem affine_action_algebraic_and_continuous
    {A G : Type} [CommRing A] [Algebra ℂ A] [Group G]
    (ρ : G →* (A ≃ₐ[ℂ] A)) :
    letI := affineAutomorphismPointAction ρ
    ContinuousConstSMul G (ComplexPoint (Over.mk (affineSpecStructureMap A))) ∧
      ∃ σ : G → (Over.mk (affineSpecStructureMap A) ≅ Over.mk (affineSpecStructureMap A)),
        ∀ g x, g • x = Point.map (σ g).hom x := by
  letI := affineAutomorphismPointAction ρ
  refine ⟨⟨fun g => ?_⟩, (fun g => affineAlgebraAutomorphismIso (ρ g⁻¹)), fun _ _ => rfl⟩
  exact Point.continuous_map (affineAlgebraAutomorphismIso (ρ g⁻¹)).hom

#print axioms affine_action_algebraic_and_continuous
end HodgeLean.Foundations.QuotientDuality
