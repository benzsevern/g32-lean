import HodgeLean.Foundations.QuotientDuality.ProperCycleComponentOpenBoundary

/-! # Generic points avoid the selected component boundaries
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace
open HodgeLean.Adapters
namespace HodgeLean.Foundations.QuotientDuality

/-- Selected generic component opens leave an actual boundary containing none of the original pure cycle primes.
Source: properCycle_component_generic_point; a3b4a_classComponent_intersection_coheight.
HC no distance; AV milestone no distance. -/
lemma properCycle_component_open_boundary_generic
    (X : Over (Spec ↧ℂ)) [QuasiCompact X.hom] (γ : AlgebraicCycle X.left ℚ)
    (k : ℕ) (hc : ∀ ξ ∈ γ.support, Order.coheight ξ = k)
    (W : ∀ ξ : γ.support, (properCycle_component_over X ξ.val).left.Opens)
    (hW : ∀ ξ, genericPoint (properCycle_component_over X ξ.val).left ∈ W ξ) :
    ∀ ξ ∈ γ.support, ξ ∉ properCycle_component_open_boundary X γ W := by
  intro ξ hξ hz
  obtain ⟨η, y, hyW, hy⟩ := Set.mem_iUnion.mp hz
  by_cases he : ξ = η.val
  · have hy' : y = genericPoint (cycleComponent X.left η.val) :=
      (cycleComponentι X.left η.val).isClosedEmbedding.injective
        (hy.trans (he.trans (properCycle_component_generic_point X.left η.val).symm))
    exact hyW (hy'.symm ▸ hW η)
  · have hξη : ξ ∈ closure ({η.val} : Set X.left) := by
      rw [← range_cycleComponentι]
      exact ⟨y, hy⟩
    have hl := a3b4a_classComponent_intersection_coheight X.left k ξ η.val ξ he
      (hc ξ hξ).ge (hc η.val η.property).ge (subset_closure (Set.mem_singleton ξ)) hξη
    rw [hc ξ hξ] at hl
    have hn : k+1 ≤ k := by exact_mod_cast hl
    omega

end HodgeLean.Foundations.QuotientDuality
