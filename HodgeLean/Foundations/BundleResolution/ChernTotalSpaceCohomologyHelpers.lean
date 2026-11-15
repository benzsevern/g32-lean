import HodgeLean.Foundations.BundleResolution.ChernTotalSpaceHomotopyHelpers
import HodgeLean.Foundations.Singular.Circle

/-! # Actual zero-section pullback in singular cohomology

The supplied total-space scalar deformation induces a cohomology
equivalence whose forward map is the actual zero-section pullback.
HC no distance; AV milestone no distance. -/

noncomputable section
open CategoryTheory Bundle TopologicalSpace AlgebraicTopology.Singular
open HodgeLean.Foundations.BundleThom
namespace HodgeLean.Foundations.BundleResolution

variable {B : Type} [TopologicalSpace B] {k : ℕ} (E : I1ComplexBundle B k)

def i1_complexBundleTotalCohomologyEquiv (n : ℕ) :
    Cohomology ℚ (TopCat.of (TotalSpace (Fin k → ℂ) E.fibre)) n ≃ₗ[ℚ]
      Cohomology ℚ (TopCat.of B) n :=
  ((HomologicalComplex.linearDualHomotopyEquiv
    (AlgebraicTopology.singularChainHomotopyEquivOfHomotopyEquiv ℚ
      (i1_complexBundleTotalHomotopyEquiv E))).toHomologyIso n).symm.toLinearEquiv

theorem i1_complexBundleZeroPullback_injective (n : ℕ) :
    Function.Injective (cohomologyMap ℚ n (TopCat.ofHom (i1_zeroSection k E.fibre))) :=
  (i1_complexBundleTotalCohomologyEquiv E n).injective

end HodgeLean.Foundations.BundleResolution
