import HodgeLean.Foundations.QuotientDuality.ProperCycleIteratedSupportSuspension

/-! # Literal base transport on actual iterated real support spaces
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The specified base map on each actual iterated real-product space, retaining every real coordinate literally.
Source: properCycle_real_support_product_map; Munkres, Topology, section 19.
HC no distance; AV milestone no distance. -/
def properCycle_iterated_real_base_map {X Y : TopCat.{0}} (f : X ⟶ Y) :
    (n : ℕ) → properCycle_real_support_space X n ⟶ properCycle_real_support_space Y n
  | 0 => f
  | n+1 => properCycle_real_support_product_map (properCycle_iterated_real_base_map f n)

/-- Literal iterated base maps retain the specified recursive point-support complements.
Source: properCycle_real_support_product_complement_map; properCycle_real_point_support.
HC no distance; AV milestone no distance. -/
theorem properCycle_iterated_real_point_complement_map
    {X Y : TopCat.{0}} (f : X ⟶ Y) (T : Set X) (U : Set Y)
    (h : Set.MapsTo f Tᶜ Uᶜ) (n : ℕ) :
    Set.MapsTo (properCycle_iterated_real_base_map f n)
      (properCycle_real_point_support X T n)ᶜ
      (properCycle_real_point_support Y U n)ᶜ := by
  induction n with
  | zero => exact h
  | succ n ih =>
    exact properCycle_real_support_product_complement_map (properCycle_iterated_real_base_map f n)
      (properCycle_real_point_support X T n) (properCycle_real_point_support Y U n) ih {0}

end HodgeLean.Foundations.QuotientDuality
