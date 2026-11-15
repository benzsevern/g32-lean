import HodgeLean.Foundations.QuotientDuality.ProperCycleComponentBoundaryGeneric

/-! # Dimension of the actual boundary of generic component opens
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry TopologicalSpace
open HodgeLean.Adapters
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual algebraic boundary of selected generic component opens has complex dimension at most one less than the pure middle component dimension.
Source: properCycle_component_open_boundary_generic; a3b4a_classAlgebraicSupport_boundary_coheight; properCycle_closed_support_dimension_le_of_coheight.
HC no distance; AV milestone no distance. -/
lemma properCycle_component_open_boundary_dimension
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (k : ℕ) (hdim : TopologicalSpace.dim X.left = 2*k)
    (γ : AlgebraicCycle X.left ℚ) (hc : ∀ ξ ∈ γ.support, Order.coheight ξ = k)
    (W : ∀ ξ : γ.support, (properCycle_component_over X ξ.val).left.Opens)
    (hW : ∀ ξ, genericPoint (properCycle_component_over X ξ.val).left ∈ W ξ) :
    topologicalKrullDim (properCycle_component_open_boundary X γ W) ≤ (k-1 : ℕ) := by
  have hco : ∀ ξ ∈ γ.support, (k : ℕ∞) ≤ Order.coheight ξ :=
    fun ξ hξ => (hc ξ hξ).ge
  have hbound := properCycle_closed_support_dimension_le_of_coheight X
    (properCycle_component_open_boundary X γ W) (k+1)
    (a3b4a_classAlgebraicSupport_boundary_coheight X.hom γ k hco
      (properCycle_component_open_boundary X γ W)
      (properCycle_component_open_boundary_le X γ W)
      (properCycle_component_open_boundary_generic X γ k hc W hW))
  rw [hdim, show 2*k-(k+1) = k-1 by omega] at hbound
  exact hbound

end HodgeLean.Foundations.QuotientDuality
