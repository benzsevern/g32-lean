import HodgeLean.Foundations.BundleResolution.ChernGlobalCapHomologyHelpers
import HodgeLean.Foundations.BundleResolution.ChernRelativeCupClassHelpers

/-! # Actual relative cap followed by a continuous projection

This rational linear map is dual to multiplication by the relative class
and pullback of the absolute base class.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomologicalComplex AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.BundleResolution

variable (X Y : TopCat.{0}) (f : X ⟶ Y) (Z : Set X) (p n : ℕ)

def i1_relativeCapToBase
    (α : RelativeCohomology ℚ (TopPair.ofSubset (X := X) Z) p) :
    RelativeHomology ℚ (TopPair.ofSubset (X := X) Z) (p + n) →ₗ[ℚ] Homology ℚ Y n :=
  (homologyMap ℚ n f).comp
    (relativeCapCohomologyLinear ℚ (TopPair.ofSubset (X := X) Z) p n α)

theorem i1_relativeCapToBase_pairing
    (α : RelativeCohomology ℚ (TopPair.ofSubset (X := X) Z) p)
    (β : Cohomology ℚ Y n) (z : RelativeHomology ℚ (TopPair.ofSubset (X := X) Z) (p + n)) :
    relativeCohomologyEquivDualHomology ℚ (TopPair.ofSubset (X := X) Z) (p + n)
      (i1_relativeCup (TopPair.ofSubset (X := X) Z) p n α (cohomologyMap ℚ n f β)) z =
    cohomologyEquivDualHomology ℚ Y n β (i1_relativeCapToBase X Y f Z p n α z) := by
  rw [i1_relativeCup_pairing]
  exact cohomologyEquivDualHomology_cohomologyMap ℚ n f β
    (relativeCapCohomologyLinear ℚ (TopPair.ofSubset (X := X) Z) p n α z)

end HodgeLean.Foundations.BundleResolution
