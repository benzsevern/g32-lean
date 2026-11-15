import HodgeLean.Foundations.QuotientDuality.ProperCycleChartOpenParametrization
import HodgeLean.Foundations.QuotientDuality.ProperCycleConnectedFlatMultiplicity
import HodgeLean.Foundations.QuotientDuality.ProperCycleConnectedFlatComponent

/-! # Actual constant multiplicity neighborhoods in flattened support
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry TopologicalSpace Topology
open HodgeLean.Adapters HodgeLean.Foundations.Analytic
namespace HodgeLean.Foundations.QuotientDuality

/-- Each point of an original pure flattened support has an actual open parametrized neighborhood on which its original multiplicity is the coefficient of one actual reduced component.
Source: properCycle_chart_open_parametrization; properCycle_connected_flat_component; properCycle_connected_flat_multiplicity.
HC no distance; AV milestone no distance. -/
lemma properCycle_flat_multiplicity_neighborhood
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (k : ℕ) (hk : 0 < k) (hdim : TopologicalSpace.dim X.left = 2*k)
    (γ : AlgebraicCycle X.left ℚ) (hc : ∀ ξ ∈ γ.support, Order.coheight ξ = k)
    (d : ℕ) (e : OpenPartialHomeomorph (ComplexPoint X) ((Fin k → ℂ) × (Fin d → ℂ)))
    (hflat : ∀ x ∈ e.source, x ∈ a3b4_cycleSupport X.hom γ ↔ (e x).2 = 0)
    (he : a3b4_IsHolChart X.hom e)
    (x : a3b4_cycleSupport X.hom γ) (hx : x.val ∈ e.source) :
    ∃ (j : TopCat.of (Fin k → ℂ) ⟶ TopCat.of (a3b4_cycleSupport X.hom γ))
      (ξ : γ.support), IsOpenEmbedding j ∧ j 0 = x ∧
      (∀ y, (j y).val ∈ e.source) ∧
      (∀ y, j y ∈ Set.range (properCycle_component_support_map X γ ξ.val ξ.property)) ∧
      ∀ y, a3b4_multiplicity X.hom γ (j y).val = γ ξ.val := by
  obtain ⟨c, hsrc, hval⟩ := properCycle_flat_support_partial_chart (a3b4_an X.hom)
    (a3b4_cycleSupport X.hom γ) e 0 hflat x hx
  obtain ⟨j, hj, hjc, hj0⟩ := properCycle_chart_open_parametrization
    (TopCat.of (a3b4_cycleSupport X.hom γ)) (Fin k → ℂ) c x (hsrc ▸ hx)
  have hje : ∀ y, (j y).val ∈ e.source := by
    intro y
    have h := hjc y
    rw [hsrc] at h
    exact h
  obtain ⟨ξ, hξ⟩ := properCycle_connected_flat_component X k hdim γ hc d e hflat he
    (TopCat.of (Fin k → ℂ)) j hj hje
  refine ⟨j, ξ, hj, hj0, hje, hξ, ?_⟩
  exact fun y => properCycle_connected_flat_multiplicity X k hk hdim γ hc d e hflat he
    (TopCat.of (Fin k → ℂ)) j hj hje ξ hξ y

end HodgeLean.Foundations.QuotientDuality
