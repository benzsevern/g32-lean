import HodgeLean.Foundations.QuotientDuality.ProperCycleComponentBairePiece
import HodgeLean.Foundations.QuotientDuality.ProperCycleConnectedChartImageRange
import HodgeLean.Foundations.QuotientDuality.ProperCycleFlatSupportPartialChart
import HodgeLean.Foundations.QuotientDuality.ProperCycleIntrinsicFlatChartPoint
import HodgeLean.Foundations.QuotientDuality.ProperCycleTangentialCenteredHolomorphic
import HodgeLean.Foundations.QuotientDuality.ProperCycleSingularComponentDimension

/-! # Actual component pieces propagated over connected flattened support regions
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular TopologicalSpace Topology
open HodgeLean.Adapters HodgeLean.Foundations.Analytic
namespace HodgeLean.Foundations.QuotientDuality

/-- An actual reduced component containing a nonempty open piece of a connected original flattened support region contains the entire region, detected by its specified intrinsic homology class.
Source: properCycle_intrinsic_flat_chart_point; properCycle_connected_chart_image_range.
HC no distance; AV milestone no distance. -/
lemma properCycle_connected_flat_component_of_piece
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (k : ℕ) (hdim : TopologicalSpace.dim X.left = 2*k)
    (γ : AlgebraicCycle X.left ℚ) (hc : ∀ ξ ∈ γ.support, Order.coheight ξ = k)
    (d : ℕ) (e : OpenPartialHomeomorph (ComplexPoint X) ((Fin k → ℂ) × (Fin d → ℂ)))
    (hflat : ∀ x ∈ e.source, x ∈ a3b4_cycleSupport X.hom γ ↔ (e x).2 = 0)
    (he : a3b4_IsHolChart X.hom e)
    (Y : TopCat.{0}) [PreconnectedSpace Y]
    (j : Y ⟶ TopCat.of (a3b4_cycleSupport X.hom γ)) (hj : IsOpenEmbedding j)
    (hje : ∀ y, (j y).val ∈ e.source)
    (ξ : γ.support) (W : Opens Y) (hW : (W : Set Y).Nonempty)
    (hpiece : ∀ y ∈ W, j y ∈ Set.range (properCycle_component_support_map X γ ξ.val ξ.property)) :
    ∀ y : Y, j y ∈ Set.range (properCycle_component_support_map X γ ξ.val ξ.property) := by
  letI : T2Space (ComplexPoint X) := f4_t2Space X
  letI : T2Space (a3b4_an X.hom) := f4_t2Space X
  let T := TopCat.of (a3b4_cycleSupport X.hom γ)
  obtain ⟨p, hp⟩ := hW
  let f := properCycle_component_support_map X γ ξ.val ξ.property
  obtain ⟨y, hy⟩ := hpiece p hp
  let O : Opens T := ⟨j '' (W : Set Y), hj.isOpenMap _ W.isOpen⟩
  have hOr : (O : Set T) ⊆ Set.range f := by
    rintro s ⟨u, hu, rfl⟩
    exact hpiece u hu
  let b := properCycle_tangential_centered_chart k d e (e (j p).val).1
  have hb := properCycle_tangential_centered_chart_data k d e (e (j p).val).1
  have hflatb : ∀ x ∈ b.source, x ∈ a3b4_cycleSupport X.hom γ ↔ (b x).2 = 0 := by
    intro x hx
    change x ∈ a3b4_cycleSupport X.hom γ ↔ (e x).2 = 0
    exact hflat x (hb.1 ▸ hx)
  have hholb := properCycle_tangential_centered_chart_holomorphic X k d e he (e (j p).val).1
  have hOe : ∀ s ∈ O, s.val ∈ b.source := by
    rintro s ⟨u, hu, rfl⟩
    rw [hb.1]
    exact hje u
  have hyO : f y ∈ O := by rw [hy]; exact ⟨p, hp, rfl⟩
  have hcenter : b (f y).val = (0, 0) := by
    change ((e (f y).val).1 - (e (j p).val).1, (e (f y).val).2) = (0, 0)
    rw [hy, sub_self, (hflat (j p).val (hje p)).mp (j p).property]
  have hD := properCycle_middle_component_dimension X k hdim ξ.val (hc ξ.val ξ.property)
  have hvalue := properCycle_intrinsic_flat_chart_point X γ ξ.val ξ.property k d hD
    b hflatb hholb O hOr hOe y hyO hcenter
  have hn : localOrientation T (2*k)
      (properCycle_intrinsic_component_on_support X γ ξ.val ξ.property k hD) (f y) ≠ 0 := by
    intro hz
    dsimp only at hvalue
    rw [hz, map_zero, map_zero] at hvalue
    exact standardComplexLocalClass_ne_zero_for_chart k hvalue.symm
  rw [hy] at hn
  obtain ⟨c, hsrc, hval⟩ := properCycle_flat_support_partial_chart (a3b4_an X.hom)
    (a3b4_cycleSupport X.hom γ) e 0 hflat (j p) (hje p)
  have hjc : ∀ u, j u ∈ c.source := by intro u; rw [hsrc]; exact hje u
  exact properCycle_connected_chart_image_range T Y
    (TopCat.of (ComplexPoint (properCycle_component_over X ξ.val))) k c j hjc f
    (properCycle_intrinsic_class (properCycle_component_over X ξ.val) k hD) p hn

end HodgeLean.Foundations.QuotientDuality
