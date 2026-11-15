import HodgeLean.Foundations.QuotientDuality.ProperCycleLocalRangeOpenEmbedding
import HodgeLean.Foundations.QuotientDuality.ProperCycleIsolatedComponentOpen

/-! # Actual smooth component opens as open pieces of collected support
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace Topology
open HodgeLean.Adapters
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual open-component inclusion followed by the reduced component map into collected support.
Source: properCycle_component_support_map; ComplexPoint.openInclusion.
HC no distance; AV milestone no distance. -/
def properCycle_component_open_support_map
    (X : Over (Spec ↧ℂ)) (γ : AlgebraicCycle X.left ℚ) (ξ : X.left) (hξ : ξ ∈ γ.support)
    (W : (properCycle_component_over X ξ).left.Opens) :
    TopCat.of (ComplexPoint (openScheme (properCycle_component_over X ξ) W)) ⟶
      TopCat.of (a3b4_cycleSupport X.hom γ) :=
  TopCat.ofHom (Point.continuousMap (openInclusion (properCycle_component_over X ξ) W)) ≫
    properCycle_component_support_map X γ ξ hξ

/-- Every actual component open avoiding all other primes is open in the literal collected support, including in a singular ambient scheme.
Source: properCycle_isolated_component_support_neighborhood; properCycle_embedding_open_composite.
HC no distance; AV milestone no distance. -/
lemma properCycle_component_open_support_map_isOpenEmbedding
    (X : Over (Spec ↧ℂ)) [QuasiCompact X.hom]
    (γ : AlgebraicCycle X.left ℚ) (ξ : X.left) (hξ : ξ ∈ γ.support)
    (W : (properCycle_component_over X ξ).left.Opens)
    (hother : ∀ z : (properCycle_component_over X ξ).left, z ∈ W →
      ∀ η ∈ γ.support, η ≠ ξ →
        (properCycle_component_over_inclusion X ξ).left z ∉ closure ({η} : Set X.left)) :
    IsOpenEmbedding (properCycle_component_open_support_map X γ ξ hξ W) := by
  let V := properCycle_component_over X ξ
  let f := properCycle_component_support_map X γ ξ hξ
  let g := TopCat.ofHom (Point.continuousMap (openInclusion V W))
  change IsOpenEmbedding (f ∘ g)
  apply properCycle_embedding_open_composite f g
    (properCycle_component_support_map_embedding X γ ξ hξ)
    (ComplexPoint.isOpenEmbedding_map_open V W)
  intro y
  apply properCycle_isolated_component_support_neighborhood X γ ξ hξ (f (g y))
  intro η hη hn
  exact hother (g y).underlying y.underlying.property η hη hn

end HodgeLean.Foundations.QuotientDuality
