import HodgeLean.Foundations.QuotientDuality.ProperCycleComponentOpenBoundary

/-! # Actual component opens cover the complement of their algebraic boundary
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.Adapters
namespace HodgeLean.Foundations.QuotientDuality

/-- Every original support point outside the selected algebraic boundary lies in an actual selected component-open image.
Source: properCycle_component_support_map_range; ComplexPoint.openHomeomorph.
HC no distance; AV milestone no distance. -/
lemma properCycle_component_open_boundary_cover
    (X : Over (Spec ↧ℂ)) [QuasiCompact X.hom] (γ : AlgebraicCycle X.left ℚ)
    (W : ∀ ξ : γ.support, (properCycle_component_over X ξ.val).left.Opens)
    (z : a3b4_cycleSupport X.hom γ)
    (hz : z.val.underlying ∉ properCycle_component_open_boundary X γ W) :
    ∃ ξ : γ.support, z ∈ Set.range
      (properCycle_component_open_support_map X γ ξ.val ξ.property (W ξ)) := by
  obtain ⟨ξ, hξ, hzξ⟩ := Set.mem_iUnion₂.mp z.property
  let η : γ.support := ⟨ξ, hξ⟩
  let V := properCycle_component_over X ξ
  let f := properCycle_component_support_map X γ ξ hξ
  have hr : z ∈ Set.range f := by
    rw [properCycle_component_support_map_range]
    exact hzξ
  obtain ⟨y, rfl⟩ := hr
  have hyW : y.underlying ∈ W η := by
    by_contra hn
    apply hz
    exact Set.mem_iUnion.mpr ⟨η, y.underlying, hn, rfl⟩
  let u := (openHomeomorph V (W η)).symm ⟨y, hyW⟩
  refine ⟨η, u, ?_⟩
  have hu : Point.map (openInclusion V (W η)) u = y :=
    congrArg Subtype.val ((openHomeomorph V (W η)).apply_symm_apply ⟨y, hyW⟩)
  change f (Point.map (openInclusion V (W η)) u) = f y
  exact congrArg f hu

end HodgeLean.Foundations.QuotientDuality
