import HodgeLean.Foundations.QuotientDuality.ProperCycleProductSupportPointPair
import HodgeLean.Foundations.QuotientDuality.ProperCycleTangentProjectionComparison

/-! # Original projected product cap through ordinary support-relative coordinates
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual ordinary product support cap, retaining its original point-source pair identification and literal tangential projection.
Source: properCycle_union_relative_support_cap; properCycle_product_support_point_pair_iso; properCycle_product_tangent_projection_pair.
HC no distance; AV milestone no distance. -/
def properCycle_product_projected_support_cap
    (E F : Type) [NormedAddCommGroup E] [NormedAddCommGroup F] (p q : ℕ)
    (a : RelativeCohomology ℚ (TopPair.ofSubset (X := TopCat.of F) ({0} : Set F)ᶜ) p) :
    orientationGroup (TopCat.of (E × F)) (p+q) (0,0) →ₗ[ℚ]
      orientationGroup (TopCat.of E) q 0 :=
  (relativeHomologyMap ℚ q (properCycle_product_tangent_projection_pair E F)).comp
    ((properCycle_union_relative_support_cap (TopCat.of (E × F))
      (Prod.snd ⁻¹' ({0} : Set F)) {z | z.1 = 0}
      (isClosed_singleton.preimage continuous_snd) (isClosed_singleton.preimage continuous_fst)
      p q (relativeCohomologyMap ℚ p (properCycle_product_support_projection E (TopCat.of F) {0}) a)).hom.comp
      (relativeHomologyMap ℚ (p+q) (properCycle_product_support_point_pair_iso E F).inv))

end HodgeLean.Foundations.QuotientDuality
