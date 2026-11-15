import HodgeLean.Foundations.RationalHomologyManifold.Defs
import HodgeLean.Foundations.Connected
import HodgeLean.Foundations.Program.SchoenTransferJ12ProjectiveBooleanModel
import HodgeLean.Foundations.Program.SchoenTransferJ12BooleanTriangulation

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000
open CategoryTheory AlgebraicGeometry
open HodgeLean.Foundations.RationalHomologyManifold
namespace HodgeLean.Foundations.Program

/-- A compact smooth complex curve has a finite geometric triangulation.
The realization is homeomorphic to the actual complex-point space.
Source: Cairns, On the Triangulation of Regular Loci, Annals of Mathematics
35 (1934), 579–587, https://doi.org/10.2307/1968752. -/
theorem s4_selected_curve_finite_triangulation
    (Y : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hdim : TopologicalSpace.dim Y.left = 1) :
    Nonempty (FiniteTriangulation (TopCat.of (ComplexPoint Y))) := by
  obtain ⟨N, f, ⟨h⟩⟩ := s4_selected_projective_boolean_model Y
  exact s4_selected_boolean_finite_triangulation (TopCat.of (ComplexPoint Y)) N f h

end HodgeLean.Foundations.Program
