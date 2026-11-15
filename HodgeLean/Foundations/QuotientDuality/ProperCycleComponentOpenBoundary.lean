import HodgeLean.Foundations.QuotientDuality.ProperCycleComponentOpenSupport
import HodgeLean.Foundations.QuotientDuality.ProperCycleAlgebraicCodimension
import HodgeLean.Adapters.NormalConeB4aClassIntersection

/-! # Actual algebraic boundaries of selected component opens
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace
open HodgeLean.Adapters
namespace HodgeLean.Foundations.QuotientDuality

/-- The finite union of the actual reduced-component boundaries of the selected original component opens.
Source: Fulton, Intersection Theory, section 1.5; closedness of reduced component immersions.
HC no distance; AV milestone no distance. -/
def properCycle_component_open_boundary
    (X : Over (Spec ↧ℂ)) [QuasiCompact X.hom] (γ : AlgebraicCycle X.left ℚ)
    (W : ∀ ξ : γ.support, (properCycle_component_over X ξ.val).left.Opens) :
    Closeds X.left := by
  classical
  letI : CompactSpace X.left := a3b4_compactSpace X.hom
  letI : Fintype γ.support := (a3b2_support_finite γ).fintype
  exact ⟨⋃ ξ : γ.support, cycleComponentι X.left ξ.val '' ((W ξ : Set (properCycle_component_over X ξ.val).left)ᶜ),
    isClosed_iUnion_of_finite (fun (ξ : γ.support) => (cycleComponentι X.left ξ.val).isClosedEmbedding.isClosedMap
      _ (W ξ).compl.isClosed)⟩

/-- The actual union of component boundaries remains inside the original algebraic cycle support.
Source: range_cycleComponentι; properCycle_component_open_boundary.
HC no distance; AV milestone no distance. -/
lemma properCycle_component_open_boundary_le
    (X : Over (Spec ↧ℂ)) [QuasiCompact X.hom] (γ : AlgebraicCycle X.left ℚ)
    (W : ∀ ξ : γ.support, (properCycle_component_over X ξ.val).left.Opens) :
    properCycle_component_open_boundary X γ W ≤ a3b4a_classAlgebraicSupport X.hom γ := by
  intro z hz
  obtain ⟨ξ, y, _, rfl⟩ := Set.mem_iUnion.mp hz
  apply Set.mem_iUnion₂.mpr
  refine ⟨ξ.val, ξ.property, ?_⟩
  rw [← range_cycleComponentι]
  exact ⟨y, rfl⟩

end HodgeLean.Foundations.QuotientDuality
