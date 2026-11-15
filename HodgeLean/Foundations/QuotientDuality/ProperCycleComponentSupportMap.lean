import HodgeLean.Foundations.QuotientDuality.ProperCycleIntrinsicComponentComparison
import HodgeLean.Adapters.NormalConeB4aClassSupport

/-! # Actual reduced component maps into the literal original cycle support
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular TopologicalSpace
open HodgeLean.Adapters
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual reduced component immersion factors through the literal analytic support of every original cycle containing that component.
Source: Fulton, Intersection Theory, sections 1.4 and 1.5, reduced prime supports.
HC no distance; AV milestone no distance. -/
def properCycle_component_support_map
    (X : Over (Spec ↧ℂ)) (γ : AlgebraicCycle X.left ℚ)
    (ξ : X.left) (hξ : ξ ∈ γ.support) :
    TopCat.of (ComplexPoint (properCycle_component_over X ξ)) ⟶
      TopCat.of (a3b4_cycleSupport X.hom γ) := by
  let f := Point.continuousMap (properCycle_component_over_inclusion X ξ)
  have hf (z : ComplexPoint (properCycle_component_over X ξ)) : f z ∈ a3b4_cycleSupport X.hom γ := by
    change (f z).underlying ∈ ⋃ η ∈ γ.support, closure ({η} : Set X.left)
    apply Set.mem_iUnion₂.mpr
    refine ⟨ξ, hξ, ?_⟩
    rw [← range_cycleComponentι]
    exact ⟨z.underlying, rfl⟩
  exact TopCat.ofHom ⟨fun z => ⟨f z, hf z⟩, f.continuous.subtype_mk hf⟩

/-- The actual component map into cycle support retains its original ambient complex-point map exactly.
Source: Fulton, Intersection Theory, section 1.4, the reduced component inclusion.
HC no distance; AV milestone no distance. -/
lemma properCycle_component_support_map_inclusion
    (X : Over (Spec ↧ℂ)) (γ : AlgebraicCycle X.left ℚ)
    (ξ : X.left) (hξ : ξ ∈ γ.support) :
    properCycle_component_support_map X γ ξ hξ ≫
      (TopPair.ofSubset (X := a3b4_an X.hom) (a3b4_cycleSupport X.hom γ)).map =
      TopCat.ofHom (Point.continuousMap (properCycle_component_over_inclusion X ξ)) := by
  ext z : 1
  rfl

/-- The actual reduced component map into the literal original cycle support is a topological embedding.
Source: isEmbedding_map_of_closedImmersion; the subspace topology on analytic cycle support.
HC no distance; AV milestone no distance. -/
lemma properCycle_component_support_map_embedding
    (X : Over (Spec ↧ℂ)) (γ : AlgebraicCycle X.left ℚ)
    (ξ : X.left) (hξ : ξ ∈ γ.support) :
    Topology.IsEmbedding (properCycle_component_support_map X γ ξ hξ) := by
  letI : IsClosedImmersion (properCycle_component_over_inclusion X ξ).left := by
    change IsClosedImmersion (cycleComponentι X.left ξ)
    infer_instance
  have hf := AlgebraicGeometry.ComplexPoint.isEmbedding_map_of_closedImmersion
    (properCycle_component_over_inclusion X ξ)
  exact hf.codRestrict (a3b4_cycleSupport X.hom γ)
    (fun z => (properCycle_component_support_map X γ ξ hξ z).property)

end HodgeLean.Foundations.QuotientDuality
