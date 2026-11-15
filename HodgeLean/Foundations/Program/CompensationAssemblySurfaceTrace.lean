import HodgeLean.Foundations.Program.CompensationAssemblyProjectionSupport

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 2048
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Program

def cq_surfaceModelTrace (T : TopCat.{0}) (Y : Over (Spec ↧ℂ))
    [GrpObj Y] [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hY : TopologicalSpace.dim Y.left = 2) (n : ℕ) :
    Cohomology ℚ (TopCat.of (T × ComplexPoint Y)) (n + 4) →ₗ[ℚ] Cohomology ℚ T n := by
  letI : SmoothOfRelativeDimension 2 Y.hom := by
    have h := SmoothOfRelativeDimension.of_isIntegral (f := Y.hom)
    rwa [hY] at h
  exact cq_fibreTrace T (TopCat.of (ComplexPoint Y)) 4 n
    (HodgeLean.Foundations.complexPointTorusHomeomorph Y 2)

theorem cq_surfaceModelTrace_naturality {U T : TopCat.{0}} (f : U ⟶ T)
    (Y : Over (Spec ↧ℂ))
    [GrpObj Y] [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hY : TopologicalSpace.dim Y.left = 2) (n : ℕ)
    (c : Cohomology ℚ (TopCat.of (T × ComplexPoint Y)) (n + 4)) :
    cq_surfaceModelTrace U Y hY n
      (cohomologyMap ℚ (n + 4) (cq_fibreProductMap f (TopCat.of (ComplexPoint Y))) c) =
      cohomologyMap ℚ n f (cq_surfaceModelTrace T Y hY n c) := by
  letI : SmoothOfRelativeDimension 2 Y.hom := by
    have h := SmoothOfRelativeDimension.of_isIntegral (f := Y.hom)
    rwa [hY] at h
  exact cq_fibreTrace_naturality f (TopCat.of (ComplexPoint Y)) 4 n
    (HodgeLean.Foundations.complexPointTorusHomeomorph Y 2) c

end HodgeLean.Foundations.Program
