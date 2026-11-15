import HodgeLean.Foundations.QuotientDuality.ProperCycleConnectedFlatComponentOfPiece
import HodgeLean.Foundations.QuotientDuality.ProperCycleFlatComponentPieceUnique

/-! # Actual local component neighborhoods in connected flattened support regions
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry TopologicalSpace Topology
open HodgeLean.Adapters
namespace HodgeLean.Foundations.QuotientDuality

/-- On a connected original flattened support region contained in an actual component, an original local full-support component neighborhood occurs exactly for that component.
Source: properCycle_connected_flat_component_of_piece; properCycle_flat_component_piece_unique; isOpen_induced_iff.
HC no distance; AV milestone no distance. -/
lemma properCycle_connected_flat_local_component
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (k : ℕ) (hk : 0 < k) (hdim : TopologicalSpace.dim X.left = 2*k)
    (γ : AlgebraicCycle X.left ℚ) (hc : ∀ ξ ∈ γ.support, Order.coheight ξ = k)
    (d : ℕ) (e : OpenPartialHomeomorph (ComplexPoint X) ((Fin k → ℂ) × (Fin d → ℂ)))
    (hflat : ∀ x ∈ e.source, x ∈ a3b4_cycleSupport X.hom γ ↔ (e x).2 = 0)
    (he : a3b4_IsHolChart X.hom e)
    (Y : TopCat.{0}) [PreconnectedSpace Y]
    (j : Y ⟶ TopCat.of (a3b4_cycleSupport X.hom γ)) (hj : IsOpenEmbedding j)
    (hje : ∀ y, (j y).val ∈ e.source)
    (ξ : γ.support)
    (hξ : ∀ y, j y ∈ Set.range (properCycle_component_support_map X γ ξ.val ξ.property))
    (q : Y) (η : γ.support) :
    (∃ U : Set (a3b4_an X.hom), IsOpen U ∧ (j q).val ∈ U ∧
      U ∩ a3b4_cycleSupport X.hom γ ⊆ Point.underlying ⁻¹' closure ({η.val} : Set X.left)) ↔ η = ξ := by
  let S := a3b4_cycleSupport X.hom γ
  let O : Opens (TopCat.of S) := ⟨Set.range j, hj.isOpen_range⟩
  have hO : (O : Set S).Nonempty := ⟨j q, ⟨q, rfl⟩⟩
  have hOe : ∀ s ∈ O, s.val ∈ e.source := by rintro s ⟨u, rfl⟩; exact hje u
  have hOξ : (O : Set S) ⊆ Set.range (properCycle_component_support_map X γ ξ.val ξ.property) := by
    rintro s ⟨u, rfl⟩
    exact hξ u
  constructor
  · rintro ⟨U, hU, hqU, hUS⟩
    let V : Opens Y := ⟨(fun y : Y => (j y).val) ⁻¹' U,
      hU.preimage (continuous_subtype_val.comp j.hom.continuous)⟩
    have hV : (V : Set Y).Nonempty := ⟨q, hqU⟩
    have hpiece : ∀ y ∈ V, j y ∈ Set.range (properCycle_component_support_map X γ η.val η.property) := by
      intro y hy
      rw [properCycle_component_support_map_range]
      exact hUS ⟨hy, (j y).property⟩
    have hη := properCycle_connected_flat_component_of_piece X k hdim γ hc d e hflat he
      Y j hj hje η V hV hpiece
    have hOη : (O : Set S) ⊆ Set.range (properCycle_component_support_map X γ η.val η.property) := by
      rintro s ⟨u, rfl⟩
      exact hη u
    exact properCycle_flat_component_piece_unique X k hk hdim γ hc η ξ d e hflat O hO hOe hOη hOξ
  · intro hη
    subst η
    obtain ⟨U, hU, hEq⟩ :=
      (isOpen_induced_iff (f := fun z : S => z.val)).mp hj.isOpen_range
    refine ⟨U, hU, ?_, ?_⟩
    · change j q ∈ Subtype.val ⁻¹' U
      rw [hEq]
      exact ⟨q, rfl⟩
    · intro x hx
      let s : S := ⟨x, hx.2⟩
      have hs : s ∈ Set.range j := by rw [← hEq]; exact hx.1
      obtain ⟨y, hy⟩ := hs
      have hyξ := hξ y
      rw [properCycle_component_support_map_range] at hyξ
      change s.val.underlying ∈ closure ({ξ.val} : Set X.left)
      rw [← hy]
      exact hyξ

end HodgeLean.Foundations.QuotientDuality
