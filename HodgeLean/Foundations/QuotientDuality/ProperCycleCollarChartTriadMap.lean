import HodgeLean.Foundations.QuotientDuality.ProperCycleCollarChartTriad

/-! # The actual triad chain map of collar chart coordinates
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular TopologicalSpace
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual collar chart map induces the original quotient-chain map for its literal support and retraction-fibre complements.
Source: properCycle_triad_relative_chain_map; ProperCycleSupportCollar.chart_retraction_triad_maps.
HC no distance; AV milestone no distance. -/
def ProperCycleSupportCollar.chart_triad_chain_map
    {X : TopCat.{0}} {S : Set X} (C : ProperCycleSupportCollar X S)
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (Y : TopCat.{0})
    (e : OpenPartialHomeomorph X (E × Y)) (W : Opens X)
    (hWe : (W : Set X) ⊆ e.source) (hWN : (W : Set X) ⊆ C.neighborhood)
    (hR : ∀ (x : X) (hx : x ∈ W), (C.retraction ⟨x, hWN hx⟩).val ∈ e.source)
    (y : Y) (hflat : ∀ x ∈ e.source, x ∈ S ↔ (e x).2 = y)
    (z : S) (hzW : z.val ∈ W) (hcenter : e z.val = (0, y)) :
    triadRelativeChainComplex ℚ (TopCat.of W) (Subtype.val ⁻¹' Sᶜ)
      ((fun x : W => C.retraction ⟨x.val, hWN x.property⟩) ⁻¹' {z}ᶜ) ⟶
    triadRelativeChainComplex ℚ (TopCat.of (E × Y))
      (Prod.snd ⁻¹' {y}ᶜ) ((Prod.fst ⁻¹' {(0 : E)})ᶜ) :=
  properCycle_triad_relative_chain_map
    (TopPair.Hom.fst (C.chart_retraction_point_pair E Y e W hWe hWN hR y hflat z hzW hcenter)) _ _ _ _
    (C.chart_retraction_triad_maps E Y e W hWe hWN hR y hflat z hzW hcenter).1
    (C.chart_retraction_triad_maps E Y e W hWe hWN hR y hflat z hzW hcenter).2

end HodgeLean.Foundations.QuotientDuality
