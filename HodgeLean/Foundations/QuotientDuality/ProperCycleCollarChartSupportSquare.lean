import HodgeLean.Foundations.QuotientDuality.ProperCycleCollarChartSupportPair
import HodgeLean.Foundations.QuotientDuality.ProperCycleContractibleFactorProjection

/-! # The original tangential support point square for actual collar coordinates
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular TopologicalSpace
namespace HodgeLean.Foundations.QuotientDuality

/-- The original product tangential projection after the actual collar chart map equals the literal retraction followed by the original tangential support chart point map.
Source: ProperCycleSupportCollar.chart_retraction_point_pair_value; properCycle_flat_support_point_pair.
HC no distance; AV milestone no distance. -/
lemma ProperCycleSupportCollar.chart_support_point_square
    {X : TopCat.{0}} {S : Set X} (C : ProperCycleSupportCollar X S)
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (Y : TopCat.{0})
    (e : OpenPartialHomeomorph X (E × Y)) (W : Opens X)
    (hWe : (W : Set X) ⊆ e.source) (hWN : (W : Set X) ⊆ C.neighborhood)
    (hR : ∀ (x : X) (hx : x ∈ W), (C.retraction ⟨x, hWN hx⟩).val ∈ e.source)
    (y : Y) (hflat : ∀ x ∈ e.source, x ∈ S ↔ (e x).2 = y)
    (z : S) (hzW : z.val ∈ W) (hcenter : e z.val = (0, y)) :
    TopPair.ofSubsetHom
      (TopPair.Hom.fst (C.chart_retraction_point_pair E Y e W hWe hWN hR y hflat z hzW hcenter))
      (C.chart_retraction_triad_maps E Y e W hWe hWN hR y hflat z hzW hcenter).2 ≫
        properCycle_factor_projection_pair (TopCat.of E) Y ({0} : Set E)ᶜ =
      C.chart_support_point_pair e W hWe hWN hR z hzW ≫
        properCycle_flat_support_point_pair X S e y hflat z (hWe hzW)
          (congrArg Prod.fst hcenter) := by
  ext x : 2
  · apply Subtype.ext
    have h := congrArg Prod.fst
      (C.chart_retraction_point_pair_value E Y e W hWe hWN hR y hflat z hzW hcenter x.val)
    exact h
  · have h := congrArg Prod.fst
      (C.chart_retraction_point_pair_value E Y e W hWe hWN hR y hflat z hzW hcenter x)
    exact h

end HodgeLean.Foundations.QuotientDuality
