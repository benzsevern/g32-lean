import HodgeLean.Foundations.QuotientDuality.ProperCycleIteratedSupportIntersections
import HodgeLean.Foundations.QuotientDuality.ProperCycleRealSupportEqualityTransport

/-! # Original normal caps on actual iterated support-relative pairs
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The original normal cap in each actual iterated real product, retaining ordinary source excision and the specified support-intersection pair identification.
Source: properCycle_union_relative_support_cap; properCycle_iterated_support_intersection_pair_iso.
HC no distance; AV milestone no distance. -/
def properCycle_iterated_union_relative_cap
    (Y : TopCat.{0}) (S T : Set Y) (hS : IsClosed S) (hT : IsClosed T) (p : ℕ)
    (a : RelativeCohomology ℚ (TopPair.ofSubset (X := Y) Sᶜ) p) (n : ℕ) :
    RelativeHomology ℚ (TopPair.ofSubset (X := properCycle_real_support_space Y n)
      (properCycle_real_point_support Y (S ∩ T) n)ᶜ) (p+n) ⟶
      RelativeHomology ℚ (TopPair.ofSubset (X := properCycle_real_support_space Y n)
        (properCycle_real_point_support Y T n)ᶜ) n :=
  HomologicalComplex.homologyMap ((relativeChainFunctor ℚ).map
    (properCycle_iterated_support_intersection_pair_iso Y S T n).inv) (p+n) ≫
    properCycle_union_relative_support_cap (properCycle_real_support_space Y n)
      (properCycle_real_normal_support Y S n) (properCycle_real_point_support Y T n)
      (properCycle_real_normal_support_isClosed Y S hS n)
      (properCycle_real_point_support_isClosed Y T hT n) p n
      (properCycle_real_support_coclass Y S p a n)

end HodgeLean.Foundations.QuotientDuality
