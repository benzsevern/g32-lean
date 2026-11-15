import HodgeLean.Foundations.QuotientDuality.ProperCycleCollarChartSupportSquare
import HodgeLean.Foundations.QuotientDuality.ProperCycleCollarChartTriadMap
import HodgeLean.Foundations.QuotientDuality.ProperCycleTriadCapHomologyNaturality

/-! # The original cap diagram for actual collar chart coordinates
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular TopologicalSpace
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual collar chart triad cap, projected by its literal retraction into tangential support point homology, is the original normal-product triad cap transported by the actual ambient triad map.
Source: properCycle_triad_cap_naturality; ProperCycleSupportCollar.chart_support_point_square.
HC no distance; AV milestone no distance. -/
lemma ProperCycleSupportCollar.chart_cap_naturality
    {X : TopCat.{0}} {S : Set X} (C : ProperCycleSupportCollar X S)
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (Y : TopCat.{0})
    (e : OpenPartialHomeomorph X (E × Y)) (W : Opens X)
    (hWe : (W : Set X) ⊆ e.source) (hWN : (W : Set X) ⊆ C.neighborhood)
    (hR : ∀ (x : X) (hx : x ∈ W), (C.retraction ⟨x, hWN hx⟩).val ∈ e.source)
    (y : Y) (hflat : ∀ x ∈ e.source, x ∈ S ↔ (e x).2 = y)
    (z : S) (hzW : z.val ∈ W) (hcenter : e z.val = (0, y)) (p q : ℕ)
    (a : RelativeCohomology ℚ (TopPair.ofSubset (X := TopCat.of (E × Y))
      (Prod.snd ⁻¹' {y}ᶜ)) p)
    (d : TriadRelativeHomology ℚ (TopCat.of W) (Subtype.val ⁻¹' Sᶜ)
      ((fun x : W => C.retraction ⟨x.val, hWN x.property⟩) ⁻¹' {z}ᶜ) (p+q)) :
    let f := TopPair.Hom.fst (C.chart_retraction_point_pair E Y e W hWe hWN hR y hflat z hzW hcenter)
    let hm := C.chart_retraction_triad_maps E Y e W hWe hWN hR y hflat z hzW hcenter
    relativeHomologyMap ℚ q
        (properCycle_flat_support_point_pair X S e y hflat z (hWe hzW) (congrArg Prod.fst hcenter))
      (relativeHomologyMap ℚ q (C.chart_support_point_pair e W hWe hWN hR z hzW)
        (triadCapCohomologyLinear ℚ (TopCat.of W) (Subtype.val ⁻¹' Sᶜ)
          ((fun x : W => C.retraction ⟨x.val, hWN x.property⟩) ⁻¹' {z}ᶜ) p q
          (relativeCohomologyMap ℚ p (TopPair.ofSubsetHom f hm.1) a) d)) =
    relativeHomologyMap ℚ q (properCycle_factor_projection_pair (TopCat.of E) Y ({0} : Set E)ᶜ)
      (triadCapCohomologyLinear ℚ (TopCat.of (E × Y))
        (Prod.snd ⁻¹' {y}ᶜ) ((Prod.fst ⁻¹' {(0 : E)})ᶜ) p q a
        ((HomologicalComplex.homologyMap
          (C.chart_triad_chain_map E Y e W hWe hWN hR y hflat z hzW hcenter) (p+q)).hom d)) := by
  dsimp only
  rw [← LinearMap.comp_apply, ← relativeHomologyMap_comp, ← C.chart_support_point_square E Y e W hWe hWN hR y hflat z hzW hcenter,
    relativeHomologyMap_comp, LinearMap.comp_apply]
  exact congrArg
    (relativeHomologyMap ℚ q (properCycle_factor_projection_pair (TopCat.of E) Y ({0} : Set E)ᶜ))
    (properCycle_triad_cap_naturality _ _ _ _ _
      (C.chart_retraction_triad_maps E Y e W hWe hWN hR y hflat z hzW hcenter).1
      (C.chart_retraction_triad_maps E Y e W hWe hWN hR y hflat z hzW hcenter).2 p q a d)

end HodgeLean.Foundations.QuotientDuality
