import HodgeLean.Foundations.Program.SchoenSelectedGeometryCurvePullback
import HodgeLean.Foundations.Program.SchoenSelectedGeometryAlgebraicSquare
import HodgeLean.Foundations.Program.SchoenSelectedGeometryBettiSquare

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open AlgebraicTopology.Singular HodgeLean.Adapters HodgeLean.RealDefs HodgeLean.Foundations.Singular
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Program

/-- Algebraization preserves injectivity of pullback for nonconstant maps of compact curves. -/
theorem s0_algebraic_curve_pullback_injective
    {C Y : Type}
    [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ, ℂ) ω Y]
    [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    (f : C → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f)
    (hnc : ∃ x x', f x ≠ f x')
    (X Z : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (eC : C ≃ₜ ComplexPoint X) (eY : Y ≃ₜ ComplexPoint Z)
    (q : X ⟶ Z) (hq : ∀ z, Point.map q (eC z) = eY (f z)) :
    Function.Injective (homPullback q 1) := by
  have hs := s0_algebraic_pullback_square ⟨eC, eC.continuous⟩ ⟨eY, eY.continuous⟩
    ⟨f, hf.continuous⟩ q hq 1
  intro a b hab
  apply (cupComparison Z 1).injective
  apply (cohomologyHomeomorphEquiv eY 1).symm.injective
  apply s0_curve_pullback_injective f hf hnc
  change cohomologyMap ℚ 1 (TopCat.ofHom ⟨f, hf.continuous⟩)
      (cohomologyMap ℚ 1 (TopCat.ofHom ⟨eY, eY.continuous⟩) (cupComparison Z 1 a)) =
    cohomologyMap ℚ 1 (TopCat.ofHom ⟨f, hf.continuous⟩)
      (cohomologyMap ℚ 1 (TopCat.ofHom ⟨eY, eY.continuous⟩) (cupComparison Z 1 b))
  rw [← hs, ← hs, hab]

#print axioms s0_algebraic_curve_pullback_injective
end HodgeLean.Foundations.Program
