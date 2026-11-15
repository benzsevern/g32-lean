import HodgeLean.Foundations.QuotientDuality.ProperCycleIsolatedComponentSupport

/-! # Actual reduced component images as closed subsets of literal cycle support
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace
open HodgeLean.Adapters
namespace HodgeLean.Foundations.QuotientDuality

/-- Each actual reduced component has closed image in the literal analytic cycle support.
Source: properCycle_component_support_map_range; ComplexPoint.continuous_underlying_to_zariski.
HC no distance; AV milestone no distance. -/
lemma properCycle_component_support_closed_range
    (X : Over (Spec ↧ℂ)) (γ : AlgebraicCycle X.left ℚ)
    (ξ : X.left) (hξ : ξ ∈ γ.support) :
    IsClosed (Set.range (properCycle_component_support_map X γ ξ hξ)) := by
  rw [properCycle_component_support_map_range]
  exact isClosed_closure.preimage
    ((AlgebraicGeometry.ComplexPoint.continuous_underlying_to_zariski X).comp continuous_subtype_val)

end HodgeLean.Foundations.QuotientDuality
