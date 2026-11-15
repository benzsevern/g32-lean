import HodgeLean.Foundations.QuotientDuality.ProperCycleCollarChartFibre
import HodgeLean.Foundations.QuotientDuality.ProperCycleTriadMap

/-! # The actual collar map preserves both original chart triad complements
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular TopologicalSpace
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual collar chart point map sends the support complement to the normal complement and the retraction-fibre complement to the tangential complement.
Source: ProperCycleSupportCollar.chart_retraction_point_pair_value; ProperCycleSupportCollar.chart_retraction_tangent_zero_iff.
HC no distance; AV milestone no distance. -/
lemma ProperCycleSupportCollar.chart_retraction_triad_maps
    {X : TopCat.{0}} {S : Set X} (C : ProperCycleSupportCollar X S)
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (Y : TopCat.{0})
    (e : OpenPartialHomeomorph X (E × Y)) (W : Opens X)
    (hWe : (W : Set X) ⊆ e.source) (hWN : (W : Set X) ⊆ C.neighborhood)
    (hR : ∀ (x : X) (hx : x ∈ W), (C.retraction ⟨x, hWN hx⟩).val ∈ e.source)
    (y : Y) (hflat : ∀ x ∈ e.source, x ∈ S ↔ (e x).2 = y)
    (z : S) (hzW : z.val ∈ W) (hcenter : e z.val = (0, y)) :
    let f := TopPair.Hom.fst
      (C.chart_retraction_point_pair E Y e W hWe hWN hR y hflat z hzW hcenter)
    Set.MapsTo f (Subtype.val ⁻¹' Sᶜ) (Prod.snd ⁻¹' {y}ᶜ) ∧
      Set.MapsTo f ((fun x : W => C.retraction ⟨x.val, hWN x.property⟩) ⁻¹' {z}ᶜ)
        ((Prod.fst ⁻¹' {(0 : E)})ᶜ) := by
  dsimp only
  constructor
  · intro x hx
    change (TopPair.Hom.fst
      (C.chart_retraction_point_pair E Y e W hWe hWN hR y hflat z hzW hcenter) x).2 ≠ y
    rw [C.chart_retraction_point_pair_value E Y e W hWe hWN hR y hflat z hzW hcenter x]
    exact fun he => hx ((hflat x.val (hWe x.property)).mpr he)
  · intro x hx
    change (TopPair.Hom.fst
      (C.chart_retraction_point_pair E Y e W hWe hWN hR y hflat z hzW hcenter) x).1 ≠ 0
    exact fun he => hx ((C.chart_retraction_tangent_zero_iff E Y e W hWe hWN hR y hflat z hzW hcenter x).mp he)

end HodgeLean.Foundations.QuotientDuality
