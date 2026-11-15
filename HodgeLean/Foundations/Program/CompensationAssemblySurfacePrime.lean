import HodgeLean.Foundations.Program.CompensationAssemblySurfaceComparison
import HodgeLean.Foundations.Program.CompensationAssemblyProductSupport

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 10000
set_option maxRecDepth 2048
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open AlgebraicTopology.Singular
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations.Singular
namespace HodgeLean.Foundations.Program

theorem cq_projection_prime_zero
    (A Y : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [GrpObj Y] [IsCommMonObj Y] [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hA : TopologicalSpace.dim A.left = 6) (hY : TopologicalSpace.dim Y.left = 2)
    (I : HQ Y 4 ≃ₗ[ℚ] ℚ)
    (e : (HQ A 1 × HQ Y 1) ≃ₗ[ℚ] HQ (A ⊗ Y) 1)
    (heA : ∀ a, e (a, 0) = homPullback (fst A Y) 1 a)
    (heY : ∀ b, e (0, b) = homPullback (snd A Y) 1 b)
    (x : (A ⊗ Y).left) (hx : Order.coheight x = 5)
    (himage : Order.coheight ((fst A Y).left x) ≠ 3) :
    cq_projectionMap A Y I e (cycleComponentSheafClass (A ⊗ Y) x hx) = 0 := by
  rw [cq_projectionMap_eq_surfaceProjection A Y hY I e heA heY]
  have ht : cq_surfaceTrace (TopCat.of (ComplexPoint A)) Y hY I 6
      (cohomologyHomeomorphEquiv (HodgeLean.Foundations.complexPointProdHomeomorph A Y)
        10 (cupComparison (A ⊗ Y) 10
          (cycleComponentSheafClass (A ⊗ Y) x hx))) = 0 := by
    apply cq_projection_image_singular_restriction_injective A Y hA hY x hx himage
    rw [← cq_surfaceTrace_naturality,
      cq_projection_component_restriction_zero A Y x hx, map_zero, map_zero]
  exact (congrArg (cupComparison A 6).symm ht).trans
    (cupComparison A 6).symm.toLinearMap.map_zero

end HodgeLean.Foundations.Program
