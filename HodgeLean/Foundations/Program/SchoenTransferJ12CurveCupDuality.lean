import HodgeLean.Foundations.Program.SchoenTransferJ12CurveCrossAction
import HodgeLean.Foundations.Program.SchoenTransferJ12CurveCupCap
import HodgeLean.Foundations.Program.SchoenTransferJ12CurveTriangulation
import HodgeLean.Foundations.QuotientDuality.LocalSmoothOrientation
import HodgeConjecture.Lemmas.AlgebraicGeometry.Smooth.Equidimensional

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000
open CategoryTheory AlgebraicGeometry
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf

/-- The actual degree-one cup pairing of a smooth projective integral curve is nondegenerate.
Source: Hatcher, Algebraic Topology, Theorem 3.30, rational Poincaré duality for the oriented curve. -/
theorem s4_selected_curve_cup_nondegenerate
    (Y : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hdim : TopologicalSpace.dim Y.left = 1) (I : HQ Y 2 ≃ₗ[ℚ] ℚ) :
    ∀ v : HQ Y 1,
      (∀ w : HQ Y 1, I ((cupProductOf Y).cup rfl v w) = 0) → v = 0 := by
  let : SmoothOfRelativeDimension 1 Y.hom := by rw [← hdim]; infer_instance
  let := (finbetti_finiteBetti Y).finite 1
  let : Module.Finite ℚ
      (AlgebraicTopology.Singular.Cohomology ℚ (TopCat.of (ComplexPoint Y)) 1) :=
    Module.Finite.equiv (cupComparison Y 1)
  obtain ⟨t⟩ := s4_selected_curve_finite_triangulation Y hdim
  exact s4_selected_curve_cup_of_triangulation Y t
    (QuotientDuality.smoothLocalRationalOrientation Y 1) I

#print axioms s4_selected_curve_cup_nondegenerate
end HodgeLean.Foundations.Program
