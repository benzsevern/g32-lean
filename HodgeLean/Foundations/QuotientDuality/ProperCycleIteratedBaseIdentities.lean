import HodgeLean.Foundations.QuotientDuality.ProperCycleIteratedBaseTransport

/-! # Literal identity maps on actual iterated real support spaces
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- Actual iterated real-product base transport retains the literal identity ambient map at every stage.
Source: properCycle_iterated_real_base_map; properCycle_real_support_product_map.
HC no distance; AV milestone no distance. -/
theorem properCycle_iterated_real_base_map_id (Y : TopCat.{0}) (n : ℕ) :
    properCycle_iterated_real_base_map (𝟙 Y) n = 𝟙 (properCycle_real_support_space Y n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change properCycle_real_support_product_map (properCycle_iterated_real_base_map (𝟙 Y) n) = _
    rw [ih]
    rfl

end HodgeLean.Foundations.QuotientDuality
