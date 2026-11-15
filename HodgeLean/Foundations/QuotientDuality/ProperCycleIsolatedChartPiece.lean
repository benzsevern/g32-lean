import HodgeLean.Foundations.QuotientDuality.ProperCycleIsolatedComponentSupport

/-! # Actual component pieces inside the original chart witnesses
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace
open HodgeLean.Adapters
namespace HodgeLean.Foundations.QuotientDuality

/-- An original isolated component chart point lifts to the actual reduced component and has an actual open support piece inside both the component image and the chart source.
Source: properCycle_component_support_map_range; properCycle_isolated_component_support_neighborhood.
HC no distance; AV milestone no distance. -/
lemma properCycle_isolated_chart_piece
    (X : Over (Spec ↧ℂ)) [IsProjective X.hom]
    (γ : AlgebraicCycle X.left ℚ) (ξ : X.left) (hξ : ξ ∈ γ.support)
    {T : Type} [TopologicalSpace T] (e : OpenPartialHomeomorph (ComplexPoint X) T)
    (x : ComplexPoint X) (hx : x ∈ e.source) (hxS : x ∈ a3b4_cycleSupport X.hom γ)
    (hxξ : x.underlying ∈ closure ({ξ} : Set X.left))
    (hother : ∀ η ∈ γ.support, η ≠ ξ → x.underlying ∉ closure ({η} : Set X.left)) :
    ∃ (y : ComplexPoint (properCycle_component_over X ξ)),
      properCycle_component_support_map X γ ξ hξ y = ⟨x, hxS⟩ ∧
      ∃ O : Opens (TopCat.of (a3b4_cycleSupport X.hom γ)),
        (O : Set (a3b4_cycleSupport X.hom γ)) ⊆
          Set.range (properCycle_component_support_map X γ ξ hξ) ∧
        (∀ s ∈ O, s.val ∈ e.source) ∧
        properCycle_component_support_map X γ ξ hξ y ∈ O := by
  let z : a3b4_cycleSupport X.hom γ := ⟨x, hxS⟩
  have hz : z ∈ Set.range (properCycle_component_support_map X γ ξ hξ) := by
    rw [properCycle_component_support_map_range]
    exact hxξ
  obtain ⟨y, hy⟩ := hz
  have hnb := properCycle_isolated_component_support_neighborhood X γ ξ hξ z hother
  obtain ⟨A, hAr, hA, hzA⟩ := mem_nhds_iff.mp hnb
  let O : Opens (TopCat.of (a3b4_cycleSupport X.hom γ)) :=
    ⟨A ∩ {s | s.val ∈ e.source}, hA.inter (e.open_source.preimage continuous_subtype_val)⟩
  refine ⟨y, hy, O, fun _ h => hAr h.1, fun _ h => h.2, ?_⟩
  rw [hy]
  exact ⟨hzA, hx⟩

end HodgeLean.Foundations.QuotientDuality
