import HodgeLean.Foundations.QuotientDuality.ProperCycleComponentSupportClosedRange
import Mathlib.Topology.Baire.Lemmas

/-! # Actual nonempty component pieces in original support regions
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace
open HodgeLean.Adapters
namespace HodgeLean.Foundations.QuotientDuality

/-- Every nonempty Baire region mapped continuously into the literal cycle support has a nonempty open piece lying in one actual reduced component image.
Source: properCycle_component_support_closed_range; nonempty_interior_of_iUnion_of_closed; a3b2_support_finite.
HC no distance; AV milestone no distance. -/
lemma properCycle_component_baire_piece
    (X : Over (Spec ↧ℂ)) [IsProjective X.hom] (γ : AlgebraicCycle X.left ℚ)
    (Y : TopCat.{0}) [Nonempty Y] [BaireSpace Y]
    (j : Y ⟶ TopCat.of (a3b4_cycleSupport X.hom γ)) :
    ∃ (ξ : γ.support) (V : Opens Y), (V : Set Y).Nonempty ∧
      ∀ y ∈ V, j y ∈ Set.range (properCycle_component_support_map X γ ξ.val ξ.property) := by
  classical
  letI : CompactSpace X.left := a3b4_compactSpace X.hom
  letI : Fintype γ.support := (a3b2_support_finite γ).fintype
  let F : γ.support → Set Y := fun ξ =>
    j ⁻¹' Set.range (properCycle_component_support_map X γ ξ.val ξ.property)
  have hc (ξ : γ.support) : IsClosed (F ξ) :=
    (properCycle_component_support_closed_range X γ ξ.val ξ.property).preimage j.hom.continuous
  have hcover : ⋃ ξ : γ.support, F ξ = Set.univ := by
    apply Set.eq_univ_of_forall
    intro y
    have hy := (j y).property
    change (j y).val.underlying ∈ ⋃ ξ ∈ γ.support, closure ({ξ} : Set X.left) at hy
    obtain ⟨ξ, hξ, hyξ⟩ := Set.mem_iUnion₂.mp hy
    apply Set.mem_iUnion.mpr
    refine ⟨⟨ξ, hξ⟩, ?_⟩
    change j y ∈ Set.range (properCycle_component_support_map X γ ξ hξ)
    rw [properCycle_component_support_map_range]
    exact hyξ
  obtain ⟨ξ, p, hp⟩ := nonempty_interior_of_iUnion_of_closed hc hcover
  refine ⟨ξ, ⟨interior (F ξ), isOpen_interior⟩, ⟨p, hp⟩, ?_⟩
  intro y hy
  change y ∈ F ξ
  exact interior_subset hy

end HodgeLean.Foundations.QuotientDuality
