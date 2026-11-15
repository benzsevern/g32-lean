import HodgeLean.Foundations.QuotientDuality.ProperCycleConnectedFlatComponentOfPiece
import HodgeLean.Foundations.QuotientDuality.ProperCycleFlatComponentPieceUnique

/-! # Actual other-component point values on connected flat regions
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular TopologicalSpace Topology
open HodgeLean.Adapters HodgeLean.Foundations.Analytic
namespace HodgeLean.Foundations.QuotientDuality

/-- The specified intrinsic class of any other pure component has zero original point value throughout a connected flattened support region contained in one actual component.
Source: properCycle_connected_chart_image_range; properCycle_flat_component_piece_unique.
HC no distance; AV milestone no distance. -/
lemma properCycle_connected_flat_other_point
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (k : ℕ) (hk : 0 < k) (hdim : TopologicalSpace.dim X.left = 2*k)
    (γ : AlgebraicCycle X.left ℚ) (hc : ∀ ξ ∈ γ.support, Order.coheight ξ = k)
    (d : ℕ) (e : OpenPartialHomeomorph (ComplexPoint X) ((Fin k → ℂ) × (Fin d → ℂ)))
    (hflat : ∀ x ∈ e.source, x ∈ a3b4_cycleSupport X.hom γ ↔ (e x).2 = 0)
    (Y : TopCat.{0}) [PreconnectedSpace Y]
    (j : Y ⟶ TopCat.of (a3b4_cycleSupport X.hom γ)) (hj : IsOpenEmbedding j)
    (hje : ∀ y, (j y).val ∈ e.source)
    (ξ : γ.support)
    (hξ : ∀ y, j y ∈ Set.range (properCycle_component_support_map X γ ξ.val ξ.property))
    (η : γ.support) (hne : η ≠ ξ) (q : Y) :
    localOrientation (TopCat.of (a3b4_cycleSupport X.hom γ)) (2*k)
      (properCycle_intrinsic_component_on_support X γ η.val η.property k
        (properCycle_middle_component_dimension X k hdim η.val (hc η.val η.property))) (j q) = 0 := by
  classical
  letI : T2Space (ComplexPoint X) := f4_t2Space X
  letI : T2Space (a3b4_an X.hom) := f4_t2Space X
  by_contra hn
  obtain ⟨c, hsrc, hval⟩ := properCycle_flat_support_partial_chart (a3b4_an X.hom)
    (a3b4_cycleSupport X.hom γ) e 0 hflat (j q) (hje q)
  have hjc : ∀ y, j y ∈ c.source := by intro y; rw [hsrc]; exact hje y
  have hη := properCycle_connected_chart_image_range
    (TopCat.of (a3b4_cycleSupport X.hom γ)) Y
    (TopCat.of (ComplexPoint (properCycle_component_over X η.val))) k c j hjc
    (properCycle_component_support_map X γ η.val η.property)
    (properCycle_intrinsic_class (properCycle_component_over X η.val) k
      (properCycle_middle_component_dimension X k hdim η.val (hc η.val η.property))) q hn
  let O : Opens (TopCat.of (a3b4_cycleSupport X.hom γ)) :=
    ⟨Set.range j, hj.isOpen_range⟩
  have hO : (O : Set (a3b4_cycleSupport X.hom γ)).Nonempty := ⟨j q, q, rfl⟩
  have hOe : ∀ s ∈ O, s.val ∈ e.source := by rintro s ⟨y, rfl⟩; exact hje y
  have hOη : ∀ s ∈ O,
      s ∈ Set.range (properCycle_component_support_map X γ η.val η.property) := by
    rintro s ⟨y, rfl⟩; exact hη y
  have hOξ : ∀ s ∈ O,
      s ∈ Set.range (properCycle_component_support_map X γ ξ.val ξ.property) := by
    rintro s ⟨y, rfl⟩; exact hξ y
  exact hne (properCycle_flat_component_piece_unique X k hk hdim γ hc η ξ d e hflat
    O hO hOe hOη hOξ)

end HodgeLean.Foundations.QuotientDuality
