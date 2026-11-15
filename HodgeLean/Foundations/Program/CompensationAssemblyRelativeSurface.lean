import HodgeLean.Foundations.Program.CompensationAssemblyRelativeFibre
import HodgeLean.Foundations.Program.CompensationAssemblySurfaceNormalized

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 10000
set_option maxRecDepth 2048
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open AlgebraicTopology.Singular
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations.Singular
namespace HodgeLean.Foundations.Program

def cq_relativeSurfaceTrace (P : TopPair.{0}) (Y : Over (Spec ↧ℂ))
    [GrpObj Y] [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hY : TopologicalSpace.dim Y.left = 2) (I : HQ Y 4 ≃ₗ[ℚ] ℚ) (n : ℕ) :
    RelativeCohomology ℚ (cq_pairProduct P (TopCat.of (ComplexPoint Y))) (n + 4) →ₗ[ℚ]
      RelativeCohomology ℚ P n := by
  letI : SmoothOfRelativeDimension 2 Y.hom := by
    have h := SmoothOfRelativeDimension.of_isIntegral (f := Y.hom)
    rwa [hY] at h
  exact cq_relativeNormalizedFibreTrace P (TopCat.of (ComplexPoint Y)) 4 n
    (HodgeLean.Foundations.complexPointTorusHomeomorph Y 2)
    ((cupComparison Y 4).symm.trans I)

theorem cq_relativeSurfaceTrace_absolute (P : TopPair.{0}) (Y : Over (Spec ↧ℂ))
    [GrpObj Y] [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hY : TopologicalSpace.dim Y.left = 2) (I : HQ Y 4 ≃ₗ[ℚ] ℚ) (n : ℕ)
    (a : RelativeCohomology ℚ (cq_pairProduct P (TopCat.of (ComplexPoint Y))) (n + 4)) :
    relativeCohomologyToAbsolute ℚ P n (cq_relativeSurfaceTrace P Y hY I n a) =
      cq_surfaceTrace P.fst Y hY I n
        (relativeCohomologyToAbsolute ℚ
          (cq_pairProduct P (TopCat.of (ComplexPoint Y))) (n + 4) a) := by
  letI : SmoothOfRelativeDimension 2 Y.hom := by
    have h := SmoothOfRelativeDimension.of_isIntegral (f := Y.hom)
    rwa [hY] at h
  exact cq_relativeNormalizedFibreTrace_absolute P (TopCat.of (ComplexPoint Y)) 4 n
    (HodgeLean.Foundations.complexPointTorusHomeomorph Y 2)
    ((cupComparison Y 4).symm.trans I) a

end HodgeLean.Foundations.Program
