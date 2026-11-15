import HodgeLean.Foundations.QuotientDuality.ProperCycleIntrinsicComponentOnSupport

/-! # Intrinsic component classes under actual support enlargement
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular TopologicalSpace
open HodgeLean.Adapters
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual reduced component maps commute with literal support inclusion.
Source: Fulton, Intersection Theory, section 1.4; properCycle_component_support_map.
HC no distance; AV milestone no distance. -/
lemma properCycle_component_support_map_enlarge
    (X : Over (Spec ↧ℂ)) (γ δ : AlgebraicCycle X.left ℚ)
    (h : a3b4_cycleSupport X.hom γ ⊆ a3b4_cycleSupport X.hom δ)
    (ξ : X.left) (hγ : ξ ∈ γ.support) (hδ : ξ ∈ δ.support) :
    properCycle_component_support_map X γ ξ hγ ≫
      TopCat.ofHom (ContinuousMap.inclusion h) =
        properCycle_component_support_map X δ ξ hδ := by
  ext z : 1
  rfl

/-- An actual support inclusion carries each specified intrinsic component class to the same intrinsic class in the enlarged support.
Source: Fulton, Intersection Theory, section 19.1; actual functoriality of singular homology.
HC no distance; AV milestone no distance. -/
lemma properCycle_intrinsic_component_on_support_enlarge
    (X : Over (Spec ↧ℂ)) [IsProjective X.hom] (γ δ : AlgebraicCycle X.left ℚ)
    (h : a3b4_cycleSupport X.hom γ ⊆ a3b4_cycleSupport X.hom δ)
    (ξ : X.left) (hγ : ξ ∈ γ.support) (hδ : ξ ∈ δ.support) (d : ℕ)
    (hdim : topologicalKrullDim (cycleComponent X.left ξ) = (d : ℕ)) :
    homologyMap ℚ (2*d) (TopCat.ofHom (ContinuousMap.inclusion h))
      (properCycle_intrinsic_component_on_support X γ ξ hγ d hdim) =
      properCycle_intrinsic_component_on_support X δ ξ hδ d hdim := by
  unfold properCycle_intrinsic_component_on_support
  rw [← LinearMap.comp_apply, ← homologyMap_comp,
    properCycle_component_support_map_enlarge X γ δ h ξ hγ hδ]

end HodgeLean.Foundations.QuotientDuality
