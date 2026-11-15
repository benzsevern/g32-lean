import HodgeLean.Foundations.QuotientDuality.ProperCycleIteratedSupportIntersections
import HodgeLean.Foundations.QuotientDuality.ProperCycleRelativeSubsetEquality

/-! # Literal ambient identity in recursive support intersection transport
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The specified inverse recursive support intersection comparison retains the literal ambient identity.
Source: properCycle_iterated_support_intersection_pair_iso; properCycle_subset_eq_pair_ambient.
HC no distance; AV milestone no distance. -/
theorem properCycle_iterated_intersection_inverse_ambient
    (Y : TopCat.{0}) (S T : Set Y) (n : ℕ) :
    TopPair.Hom.fst (properCycle_iterated_support_intersection_pair_iso Y S T n).inv =
      𝟙 (properCycle_real_support_space Y n) := by
  exact properCycle_subset_eq_pair_ambient _ _ _
    (congrArg (fun A : Set (properCycle_real_support_space Y n) => Aᶜ)
      (properCycle_iterated_support_intersection Y S T n).symm)

end HodgeLean.Foundations.QuotientDuality
