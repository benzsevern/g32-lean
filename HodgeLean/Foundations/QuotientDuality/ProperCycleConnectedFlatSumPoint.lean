import HodgeLean.Foundations.QuotientDuality.ProperCycleConnectedFlatOtherPoint
import HodgeLean.Foundations.QuotientDuality.ProperCycleIntrinsicSupportSum

/-! # Literal intrinsic sum point values on connected flat regions
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular TopologicalSpace Topology
open HodgeLean.Adapters HodgeLean.Foundations.Analytic
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual intrinsic support sum has the literal containing-component point value throughout a connected flat region, including its intersections with other components.
Source: properCycle_connected_flat_other_point; properCycle_intrinsic_support_sum.
HC no distance; AV milestone no distance. -/
lemma properCycle_connected_flat_sum_point
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
    (v : γ.support → ℚ) (q : Y) :
    localOrientation (TopCat.of (a3b4_cycleSupport X.hom γ)) (2*k)
      (properCycle_intrinsic_support_sum X k hdim γ hc v) (j q) =
      v ξ • localOrientation (TopCat.of (a3b4_cycleSupport X.hom γ)) (2*k)
        (properCycle_intrinsic_component_on_support X γ ξ.val ξ.property k
          (properCycle_middle_component_dimension X k hdim ξ.val (hc ξ.val ξ.property))) (j q) := by
  classical
  letI : CompactSpace X.left := a3b4_compactSpace X.hom
  letI : Fintype γ.support := (a3b2_support_finite γ).fintype
  let L := (relativeHomologyProjection ℚ
    (pointComplementPair (M := a3b4_cycleSupport X.hom γ) (j q)) (2*k)).hom
  change L (∑ η : γ.support, v η •
    properCycle_intrinsic_component_on_support X γ η.val η.property k
      (properCycle_middle_component_dimension X k hdim η.val (hc η.val η.property))) = _
  rw [map_sum]
  simp only [map_smul]
  apply Finset.sum_eq_single ξ
  · intro η _ hη
    exact (congrArg (fun t => v η • t)
      (properCycle_connected_flat_other_point X k hk hdim γ hc d e hflat Y j hj hje
        ξ hξ η hη q)).trans (smul_zero _)
  · intro h
    exact (h (Finset.mem_univ ξ)).elim

end HodgeLean.Foundations.QuotientDuality
