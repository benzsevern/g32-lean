import HodgeLean.Foundations.Program.CompensationAssemblyPrimeTraceTransport
import HodgeLean.Foundations.Program.CompensationAssemblyRelativeTracePairing

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 10000
set_option maxRecDepth 2048
open CategoryTheory AlgebraicTopology.Singular
open AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations.Singular
namespace HodgeLean.Foundations.Program

def cq_relativeSurfaceSweep (P : TopPair.{0}) (Y : Over (Spec ↧ℂ))
    [GrpObj Y] [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hY : TopologicalSpace.dim Y.left = 2) (I : HQ Y 4 ≃ₗ[ℚ] ℚ) (n : ℕ) :
    RelativeHomology ℚ P n →ₗ[ℚ]
      RelativeHomology ℚ (cq_pairProduct P (TopCat.of (ComplexPoint Y))) (n + 4) := by
  letI : SmoothOfRelativeDimension 2 Y.hom := by
    have h := SmoothOfRelativeDimension.of_isIntegral (f := Y.hom)
    rwa [hY] at h
  exact cq_relativeNormalizedFibreSweep P (TopCat.of (ComplexPoint Y)) 4 n
    (HodgeLean.Foundations.complexPointTorusHomeomorph Y 2)
    ((cupComparison Y 4).symm.trans I)

theorem cq_relativeSurfaceTrace_pairing (P : TopPair.{0}) (Y : Over (Spec ↧ℂ))
    [GrpObj Y] [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hY : TopologicalSpace.dim Y.left = 2) (I : HQ Y 4 ≃ₗ[ℚ] ℚ) (n : ℕ)
    (a : RelativeCohomology ℚ (cq_pairProduct P (TopCat.of (ComplexPoint Y))) (n + 4))
    (z : RelativeHomology ℚ P n) :
    relativeCohomologyEquivDualHomology ℚ P n (cq_relativeSurfaceTrace P Y hY I n a) z =
      relativeCohomologyEquivDualHomology ℚ _ (n + 4) a
        (cq_relativeSurfaceSweep P Y hY I n z) := by
  letI : SmoothOfRelativeDimension 2 Y.hom := by
    have h := SmoothOfRelativeDimension.of_isIntegral (f := Y.hom)
    rwa [hY] at h
  exact cq_relativeNormalizedFibreTrace_pairing P (TopCat.of (ComplexPoint Y)) 4 n
    (HodgeLean.Foundations.complexPointTorusHomeomorph Y 2)
    ((cupComparison Y 4).symm.trans I) a z

def cq_prime_surface_relative_class (A Y : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [GrpObj Y] [IsCommMonObj Y] [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hY : TopologicalSpace.dim Y.left = 2) (I : HQ Y 4 ≃ₗ[ℚ] ℚ)
    (x : (A ⊗ Y).left) (hx : Order.coheight x = 5) :
    RelativeCohomology ℚ
      (TopPair.ofSubset (X := TopCat.of (ComplexPoint A))
        ((cycleComponentAnalyticClosedSupport A ((fst A Y).left x) :
          Set (ComplexPoint A))ᶜ)) 6 :=
  cq_relativeSurfaceTrace _ Y hY I 6 (cq_prime_product_relative_class A Y x hx)

set_option backward.isDefEq.respectTransparency false in
theorem cq_prime_surface_relative_class_absolute (A Y : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [GrpObj Y] [IsCommMonObj Y] [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hY : TopologicalSpace.dim Y.left = 2) (I : HQ Y 4 ≃ₗ[ℚ] ℚ)
    (x : (A ⊗ Y).left) (hx : Order.coheight x = 5) :
    relativeCohomologyToAbsolute ℚ _ 6 (cq_prime_surface_relative_class A Y hY I x hx) =
      cupComparison A 6 (cq_surfaceProjection A Y hY I 6
        (cycleComponentSheafClass (A ⊗ Y) x hx)) := by
  rw [cq_prime_surface_relative_class, cq_relativeSurfaceTrace_absolute,
    cq_prime_product_relative_class_absolute A Y x hx]
  exact ((cupComparison A 6).apply_symm_apply _).symm

end HodgeLean.Foundations.Program
