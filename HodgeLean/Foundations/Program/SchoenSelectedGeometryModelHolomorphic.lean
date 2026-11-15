import HodgeLean.Foundations.Program.SchoenSelectedGeometryModelTower
import HodgeLean.Adapters.ExpHolomorphic

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Program

/-- A commuting algebraic model square makes the corresponding analytic map holomorphic. -/
theorem s0_model_square_holomorphic
    {C Z : Type} [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
    [TopologicalSpace Z] [ChartedSpace ℂ Z] [IsManifold 𝓘(ℂ, ℂ) ω Z]
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (eC : C ≃ₜ ComplexPoint X) (eZ : Z ≃ₜ ComplexPoint Y)
    (hC : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, Fin (TopologicalSpace.dim X.left) → ℂ) ω eC)
    (hZ : ContMDiff 𝓘(ℂ, Fin (TopologicalSpace.dim Y.left) → ℂ) 𝓘(ℂ, ℂ) ω eZ.symm)
    (q : X ⟶ Y) (f : C → Z) (hq : ∀ x, Point.map q (eC x) = eZ (f x)) :
    ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f := by
  have hh := hZ.comp ((spec_contMDiff_pointMap X Y
    (TopologicalSpace.dim X.left) (TopologicalSpace.dim Y.left) q).comp hC)
  have heq : f = fun x ↦ eZ.symm (Point.map q (eC x)) := by
    funext x
    rw [hq, eZ.symm_apply_apply]
  rw [heq]
  exact hh

#print axioms s0_model_square_holomorphic
end HodgeLean.Foundations.Program
