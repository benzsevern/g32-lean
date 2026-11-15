import HodgeLean.Foundations.BundleResolution.ChernRelativeCupHelpers
import HodgeLean.Foundations.BundleResolution.ChernTotalSpaceCohomologyHelpers
import HodgeLean.Foundations.BundleThom.Thom

/-! # Multiplication by the selected actual bundle Thom class

The canonical relative cup action and the actual total projection give the
singular Thom multiplication map in every base cohomology degree.
HC no distance; AV milestone no distance. -/

noncomputable section
open CategoryTheory Bundle TopologicalSpace AlgebraicTopology.Singular
open HodgeLean.Foundations.BundleThom
namespace HodgeLean.Foundations.BundleResolution

variable {B : Type} [TopologicalSpace B] [CompactSpace B] [T2Space B]
variable {k : ℕ} (E : I1ComplexBundle B k)

def i1_complexBundleThomMultiplication (n : ℕ) :
    Cohomology ℚ (TopCat.of B) n →ₗ[ℚ]
      CohomologyWithSupport ℚ (i1_totalSpace k E.fibre)
        (i1_zeroSupport k E.fibre) (2 * k + n) :=
  (i1_relativeCup (TopPair.ofSubset (X := i1_totalSpace k E.fibre)
    (i1_zeroSupport k E.fibre)ᶜ) (2 * k) n (i1_bundleThom k E.fibre)).comp
      (cohomologyMap ℚ n (TopCat.ofHom (i1_complexBundleTotalProjection E)))

theorem i1_complexBundleThomMultiplication_pairing (n : ℕ)
    (α : Cohomology ℚ (TopCat.of B) n)
    (z : RelativeHomology ℚ (TopPair.ofSubset (X := i1_totalSpace k E.fibre)
      (i1_zeroSupport k E.fibre)ᶜ) (2 * k + n)) :
    relativeCohomologyEquivDualHomology ℚ
      (TopPair.ofSubset (X := i1_totalSpace k E.fibre) (i1_zeroSupport k E.fibre)ᶜ)
      (2 * k + n) (i1_complexBundleThomMultiplication E n α) z =
    cohomologyEquivDualHomology ℚ (i1_totalSpace k E.fibre) n
      (cohomologyMap ℚ n (TopCat.ofHom (i1_complexBundleTotalProjection E)) α)
      (relativeCapCohomologyLinear ℚ
        (TopPair.ofSubset (X := i1_totalSpace k E.fibre) (i1_zeroSupport k E.fibre)ᶜ)
        (2 * k) n (i1_bundleThom k E.fibre) z) :=
  i1_relativeCup_pairing _ _ _ _ _ _

theorem i1_complexBundleThomMultiplication_bijective_of_cap_bijective (n : ℕ)
    (hcap : Function.Bijective (relativeCapCohomologyLinear ℚ
      (TopPair.ofSubset (X := i1_totalSpace k E.fibre) (i1_zeroSupport k E.fibre)ᶜ)
      (2 * k) n (i1_bundleThom k E.fibre))) :
    Function.Bijective (i1_complexBundleThomMultiplication E n) := by
  have hp : Function.Bijective
      (cohomologyMap ℚ n (TopCat.ofHom (i1_complexBundleTotalProjection E))) :=
    (i1_complexBundleTotalCohomologyEquiv E n).symm.bijective
  exact (i1_relativeCup_bijective_of_cap_bijective _ _ _ _ hcap).comp hp

end HodgeLean.Foundations.BundleResolution
