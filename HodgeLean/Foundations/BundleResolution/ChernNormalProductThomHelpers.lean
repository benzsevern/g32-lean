import HodgeLean.Foundations.BundleResolution.ChernRelativeProductCupHelpers
import HodgeLean.Foundations.BundleResolution.ChernSingleDegreeTensorHelpers
import HodgeLean.Foundations.BundleResolution.ChernNormalCohomologyHelpers

/-! # Actual normal product Thom multiplication

The prescribed normalized normal coclass occupies the unique nonzero
first-factor degree of the actual relative Kunneth equivalence.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicTopology.Singular
open HodgeLean.Foundations.Singular HodgeLean.RealDefs
namespace HodgeLean.Foundations.BundleResolution

def i1_normalProductThomMultiplication (k : ℕ) (Y : TopCat) (n : ℕ) :
    Cohomology ℚ Y n →ₗ[ℚ]
      RelativeCohomology ℚ (i1_relativeProductPair (puncturedPair ℂ k) Y) (2 * k + n) :=
  (i1_relativeCup (i1_relativeProductPair (puncturedPair ℂ k) Y) (2 * k) n
    (relativeCohomologyMap ℚ (2 * k) (i1_relativeProductFirst (puncturedPair ℂ k) Y)
      (normalizedPointCoclass k))).comp
    (cohomologyMap ℚ n (productSecond (puncturedPair ℂ k).fst Y))

theorem i1_normalProductThomMultiplication_bijective (k : ℕ) (Y : TopCat) (n : ℕ) :
    Function.Bijective (i1_normalProductThomMultiplication k Y n) := by
  let M : ℕ → Type := fun p => RelativeCohomology ℚ (puncturedPair ℂ k) p
  let N : ℕ → Type := fun q => Cohomology ℚ Y q
  let e := i1_relativeProductCohomologyEquiv (puncturedPair ℂ k) Y
    (i1_complexNormal_cohomology_finite k) (2 * k + n)
  let t := i1_singleDegreeTensorInsertion M N (2 * k) n (normalizedPointCoclass k)
  have ht : Function.Bijective t := i1_singleDegreeTensorInsertion_bijective M N
    (2 * k) n (normalizedPointCoclass k) (i1_normalizedPointCoclass_scalar_bijective k)
    (i1_complexNormal_cohomology_subsingleton_of_ne k)
  have he : i1_normalProductThomMultiplication k Y n = e.toLinearMap.comp t := by
    ext α
    exact (i1_relativeProductCohomologyEquiv_tmul (puncturedPair ℂ k) Y
      (i1_complexNormal_cohomology_finite k) (2 * k) n (normalizedPointCoclass k) α).symm
  rw [he]
  exact e.bijective.comp ht

end HodgeLean.Foundations.BundleResolution
