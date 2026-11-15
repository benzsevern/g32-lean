import HodgeLean.Foundations.QuotientDuality.ProperCycleConnectedFlatSumPoint
import HodgeLean.Foundations.QuotientDuality.ProperCycleCapCoordinateSupportFactorization

/-! # Actual cap point values on connected flat support regions
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular TopologicalSpace Topology
open HodgeLean.Adapters HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

/-- Actual cap coordinates give the literal containing-component point value throughout a connected original flat support region.
Source: properCycle_cap_coordinates_support_factorization; properCycle_connected_flat_sum_point.
HC no distance; AV milestone no distance. -/
lemma properCycle_connected_flat_cap_point
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
    (c : Homology ℚ (a3b4_an X.hom) (2*k+2*k)) (a : s2e_supportedClass X γ k) (q : Y) :
    localOrientation (TopCat.of (a3b4_cycleSupport X.hom γ)) (2*k)
      (properCycle_original_support_cap X γ k c a) (j q) =
      (properCycle_cap_coordinates X k hk hdim γ hc c a ξ *
        properCycle_standard_complex_cap_scalar k k) •
        localOrientation (TopCat.of (a3b4_cycleSupport X.hom γ)) (2*k)
          (properCycle_intrinsic_component_on_support X γ ξ.val ξ.property k
            (properCycle_middle_component_dimension X k hdim ξ.val (hc ξ.val ξ.property))) (j q) := by
  let L := (relativeHomologyProjection ℚ
    (pointComplementPair (M := a3b4_cycleSupport X.hom γ) (j q)) (2*k)).hom
  have h := congrArg L (properCycle_cap_coordinates_support_factorization X k hk hdim γ hc c a)
  rw [map_smul] at h
  have hs := properCycle_connected_flat_sum_point X k hk hdim γ hc d e hflat Y j hj hje
    ξ hξ (properCycle_cap_coordinates X k hk hdim γ hc c a) q
  change L (properCycle_intrinsic_support_sum X k hdim γ hc _) = _ at hs
  rw [hs, smul_smul] at h
  change L (properCycle_original_support_cap X γ k c a) = _
  simpa only [mul_comm (properCycle_standard_complex_cap_scalar k k)
    (properCycle_cap_coordinates X k hk hdim γ hc c a ξ)] using h

end HodgeLean.Foundations.QuotientDuality
