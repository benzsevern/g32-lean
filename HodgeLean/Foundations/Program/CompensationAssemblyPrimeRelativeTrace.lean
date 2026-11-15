import HodgeLean.Foundations.Program.CompensationAssemblyProjectionLift
import HodgeLean.Foundations.Program.CompensationAssemblyRelativeNaturality

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 10000
set_option maxRecDepth 2048
open CategoryTheory AlgebraicTopology.Singular
open AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations.Singular
namespace HodgeLean.Foundations.Program

theorem cq_prime_product_relative_lift (A Y : Over (Spec ↧ℂ))
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (x : (A ⊗ Y).left) {p : ℕ} (hx : Order.coheight x = p) :
    ∃ c : RelativeCohomology ℚ
        (cq_pairProduct (TopPair.ofSubset (X := TopCat.of (ComplexPoint A))
          ((cycleComponentAnalyticClosedSupport A ((fst A Y).left x) :
            Set (ComplexPoint A))ᶜ)) (TopCat.of (ComplexPoint Y))) (2 * p),
      relativeCohomologyToAbsolute ℚ _ (2 * p) c =
        cohomologyHomeomorphEquiv (HodgeLean.Foundations.complexPointProdHomeomorph A Y)
          (2 * p) (cupComparison (A ⊗ Y) (2 * p)
            (cycleComponentSheafClass (A ⊗ Y) x hx)) := by
  apply cq_relative_absolute_exists
  exact cq_projection_component_restriction_zero A Y x hx

end HodgeLean.Foundations.Program
