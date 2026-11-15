import HodgeLean.Foundations.BundleResolution.ChernThomMultiplicationHelpers
import HodgeLean.Foundations.BundleResolution.ChernRelativeCocycleClassHelpers

/-! # An actual cocycle representing the selected bundle Thom class

Surjectivity of the actual relative cocycle class map selects a representative
of the independently normalized bundle Thom class.
HC no distance; AV milestone no distance. -/

noncomputable section
open CategoryTheory Bundle TopologicalSpace AlgebraicTopology.Singular
open HodgeLean.Foundations.BundleThom
namespace HodgeLean.Foundations.BundleResolution

variable {B : Type} [TopologicalSpace B] [CompactSpace B] [T2Space B]
variable {k : ℕ} (E : I1ComplexBundle B k)

def i1_bundleThomCocycle : RelativeCocycle ℚ
    (TopPair.ofSubset (X := i1_totalSpace k E.fibre) (i1_zeroSupport k E.fibre)ᶜ) (2 * k) :=
  Classical.choose (i1_relativeCocycleClass_surjective
    (TopPair.ofSubset (X := i1_totalSpace k E.fibre) (i1_zeroSupport k E.fibre)ᶜ)
    (2 * k) (i1_bundleThom k E.fibre))

theorem i1_bundleThomCocycle_class :
    i1_relativeCocycleClass
      (TopPair.ofSubset (X := i1_totalSpace k E.fibre) (i1_zeroSupport k E.fibre)ᶜ)
      (2 * k) (i1_bundleThomCocycle E) = i1_bundleThom k E.fibre :=
  Classical.choose_spec (i1_relativeCocycleClass_surjective
    (TopPair.ofSubset (X := i1_totalSpace k E.fibre) (i1_zeroSupport k E.fibre)ᶜ)
    (2 * k) (i1_bundleThom k E.fibre))

end HodgeLean.Foundations.BundleResolution
