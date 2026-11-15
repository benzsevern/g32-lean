import HodgeLean.Foundations.Program.SchoenSelectedGeometryFiniteCoordinate
import HodgeLean.Foundations.Program.SchoenSelectedGeometryCurveDimension

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

/-- A nonconstant sphere coordinate identifies the dimension of an integral projective model.
Source: finite fibres of holomorphic maps of compact curves and quasi-finite dimension bounds. -/
theorem s0_model_dimension_of_nonconstant_coordinate
    {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (q : X ⟶ Over.mk (ProjectiveSpace.toBase (Fin 2) (Spec ↧ℂ)))
    (e : C ≃ₜ ComplexPoint X)
    (h : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun x ↦ s0_sphere_projective_homeomorph.symm (Point.map q (e x))))
    (hnc : ∃ x y : C, Point.map q (e x) ≠ Point.map q (e y)) :
    TopologicalSpace.dim X.left = 1 := by
  letI : IsFinite q.left := s0_finite_of_holomorphic_sphere_coordinate X q e h hnc
  obtain ⟨x, y, hxy⟩ := hnc
  letI : Nontrivial X.left := ⟨⟨(e x).underlying, (e y).underlying, fun he ↦
    hxy (congrArg (Point.map q) (underlying_injective_of_locallyOfFiniteType he))⟩⟩
  exact s0_dimension_one_of_quasiFinite_line_projection X.left q.left

#print axioms s0_model_dimension_of_nonconstant_coordinate
end HodgeLean.Foundations.Program
