import HodgeLean.Foundations.QuotientDuality.ProperCycleComponentOpenSupport
import HodgeLean.Foundations.QuotientDuality.ProperCycleSigmaOpenEmbedding

/-! # The actual disjoint union of selected isolated component pieces
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace Topology
open HodgeLean.Adapters
namespace HodgeLean.Foundations.QuotientDuality

/-- Actual open component maps have jointly injective disjoint union when each selected scheme open avoids all other original component supports.
Source: properCycle_component_open_support_map_isOpenEmbedding; range_cycleComponentι.
HC no distance; AV milestone no distance. -/
lemma properCycle_component_open_union_injective
    (X : Over (Spec ↧ℂ)) [QuasiCompact X.hom] (γ : AlgebraicCycle X.left ℚ)
    (W : ∀ ξ : γ.support, (properCycle_component_over X ξ.val).left.Opens)
    (hother : ∀ (ξ : γ.support) (y : (properCycle_component_over X ξ.val).left), y ∈ W ξ →
      ∀ η ∈ γ.support, η ≠ ξ.val →
        (properCycle_component_over_inclusion X ξ.val).left y ∉ closure ({η} : Set X.left)) :
    Function.Injective (fun z : Σ ξ : γ.support,
        ComplexPoint (openScheme (properCycle_component_over X ξ.val) (W ξ)) =>
      properCycle_component_open_support_map X γ z.1.val z.1.property (W z.1) z.2) := by
  rintro ⟨ξ, y⟩ ⟨η, z⟩ he
  let u := Point.map (openInclusion (properCycle_component_over X ξ.val) (W ξ)) y
  let v := Point.map (openInclusion (properCycle_component_over X η.val) (W η)) z
  have hpoint := congrArg (fun w : a3b4_cycleSupport X.hom γ => w.val.underlying) he
  change (properCycle_component_over_inclusion X ξ.val).left u.underlying =
    (properCycle_component_over_inclusion X η.val).left v.underlying at hpoint
  have hξη : ξ = η := by
    by_contra hn
    have hnot := hother ξ u.underlying y.underlying.property η.val η.property
      (fun h => hn (Subtype.ext h.symm))
    apply hnot
    have hv : (properCycle_component_over_inclusion X η.val).left v.underlying ∈
        closure ({η.val} : Set X.left) := by
      rw [← range_cycleComponentι]
      exact ⟨v.underlying, rfl⟩
    rw [hpoint]
    exact hv
  subst η
  have hyz := (properCycle_component_open_support_map_isOpenEmbedding X γ ξ.val ξ.property
    (W ξ) (hother ξ)).injective he
  exact congrArg (Sigma.mk ξ) hyz

end HodgeLean.Foundations.QuotientDuality
