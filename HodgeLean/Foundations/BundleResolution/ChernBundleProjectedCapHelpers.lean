import HodgeLean.Foundations.BundleResolution.ChernRelativeCapToBaseQuasiIsoHelpers
import HodgeLean.Foundations.BundleResolution.ChernBundleThomGlobalQuasiIsoHelpers
import HodgeLean.Foundations.BundleResolution.ChernThomMultiplicationHelpers

/-! # Actual selected bundle Thom cap to base homology

The selected Thom class, relative cap and the original bundle projection
supply the rational linear map paired with actual Thom multiplication.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Bundle TopologicalSpace AlgebraicTopology.Singular
open HodgeLean.Foundations.BundleThom
namespace HodgeLean.Foundations.BundleResolution

variable {B : Type} [TopologicalSpace B] [CompactSpace B] [T2Space B]
variable {k : ℕ} (E : I1ComplexBundle B k)

def i1_complexBundleThomCapToBase (n : ℕ) :
    RelativeHomology ℚ (TopPair.ofSubset (X := i1_totalSpace k E.fibre)
      (i1_zeroSupport k E.fibre)ᶜ) (2 * k + n) →ₗ[ℚ] Homology ℚ (TopCat.of B) n :=
  i1_relativeCapToBase (i1_totalSpace k E.fibre) (TopCat.of B)
    (TopCat.ofHom (i1_complexBundleTotalProjection E)) (i1_zeroSupport k E.fibre)ᶜ
    (2 * k) n (i1_bundleThom k E.fibre)

theorem i1_complexBundleThomCapToBase_pairing (n : ℕ)
    (α : Cohomology ℚ (TopCat.of B) n)
    (z : RelativeHomology ℚ (TopPair.ofSubset (X := i1_totalSpace k E.fibre)
      (i1_zeroSupport k E.fibre)ᶜ) (2 * k + n)) :
    relativeCohomologyEquivDualHomology ℚ
      (TopPair.ofSubset (X := i1_totalSpace k E.fibre) (i1_zeroSupport k E.fibre)ᶜ) (2 * k + n)
      (i1_complexBundleThomMultiplication E n α) z =
    cohomologyEquivDualHomology ℚ (TopCat.of B) n α (i1_complexBundleThomCapToBase E n z) :=
  i1_relativeCapToBase_pairing (i1_totalSpace k E.fibre) (TopCat.of B)
    (TopCat.ofHom (i1_complexBundleTotalProjection E)) (i1_zeroSupport k E.fibre)ᶜ
    (2 * k) n (i1_bundleThom k E.fibre) α z

theorem i1_complexBundleThomCapToBase_bijective [Nonempty B] (n : ℕ) :
    Function.Bijective (i1_complexBundleThomCapToBase E n) := by
  haveI := i1_bundleThomCocycle_global_cap_quasiIso E
  dsimp only [i1_complexBundleThomCapToBase]
  rw [← i1_bundleThomCocycle_class E]
  exact i1_relativeCapToBase_bijective_of_global_quasiIso (i1_totalSpace k E.fibre) (TopCat.of B)
    (TopCat.ofHom (i1_complexBundleTotalProjection E)) (i1_zeroSupport k E.fibre)ᶜ
    k n (i1_bundleThomCocycle E)

end HodgeLean.Foundations.BundleResolution
