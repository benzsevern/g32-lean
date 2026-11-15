import HodgeLean.Foundations.QuotientDuality.ProperCycleConnectedFlatLocalComponent

/-! # Literal original multiplicity on connected flattened support regions
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry TopologicalSpace Topology
open HodgeLean.Adapters
namespace HodgeLean.Foundations.QuotientDuality

/-- The original multiplicity on a connected flattened support region is the literal coefficient of its actual containing component.
Source: properCycle_connected_flat_local_component; a3b4_multiplicity; Finset.sum_eq_single.
HC no distance; AV milestone no distance. -/
lemma properCycle_connected_flat_multiplicity
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
    (q : Y) : a3b4_multiplicity X.hom γ (j q).val = γ ξ.val := by
  classical
  letI : CompactSpace X.left := a3b4_compactSpace X.hom
  unfold a3b4_multiplicity
  rw [Finset.sum_eq_single ξ.val]
  · exact if_pos ((properCycle_connected_flat_local_component X k hk hdim γ hc d e hflat he
      Y j hj hje ξ hξ q ξ).mpr rfl)
  · intro η hη hne
    have hηmem : η ∈ γ.support := (a3b2_support_finite γ).mem_toFinset.mp hη
    apply if_neg
    intro hlocal
    have heq := (properCycle_connected_flat_local_component X k hk hdim γ hc d e hflat he
      Y j hj hje ξ hξ q ⟨η, hηmem⟩).mp hlocal
    exact hne (congrArg Subtype.val heq)
  · intro hnot
    exact (hnot ((a3b2_support_finite γ).mem_toFinset.mpr ξ.property)).elim

end HodgeLean.Foundations.QuotientDuality
