import HodgeLean.Foundations.QuotientDuality.ProperCycleCollarChartTriad
import HodgeConjecture.Definitions.AlgebraicTopology.LocalHomology.NormalProjectionCoclass

/-! # The original normal projection in actual collar chart coordinates
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular TopologicalSpace
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual collar chart map followed by the literal normal projection equals the original chart normal projection as a map of support-complement pairs.
Source: ProperCycleSupportCollar.chart_retraction_point_pair_value; chartNormalProjectionPair.
HC no distance; AV milestone no distance. -/
lemma ProperCycleSupportCollar.chart_normal_projection_square
    {X : TopCat.{0}} {S : Set X} (C : ProperCycleSupportCollar X S)
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (d : ℕ)
    (e : OpenPartialHomeomorph X (E × (Fin d → ℂ))) (W : Opens X)
    (hWe : (W : Set X) ⊆ e.source) (hWN : (W : Set X) ⊆ C.neighborhood)
    (hR : ∀ (x : X) (hx : x ∈ W), (C.retraction ⟨x, hWN hx⟩).val ∈ e.source)
    (hflat : ∀ x ∈ e.source, x ∈ S ↔ (e x).2 = 0)
    (z : S) (hzW : z.val ∈ W) (hcenter : e z.val = (0, 0)) :
    TopPair.ofSubsetHom
        (TopPair.Hom.fst (C.chart_retraction_point_pair E (TopCat.of (Fin d → ℂ)) e W
          hWe hWN hR 0 hflat z hzW hcenter))
        (C.chart_retraction_triad_maps E (TopCat.of (Fin d → ℂ)) e W
          hWe hWN hR 0 hflat z hzW hcenter).1 ≫
      properCycle_product_support_projection E (TopCat.of (Fin d → ℂ)) {0} =
    chartNormalProjectionPair E d e S hflat (W : Set X) hWe := by
  ext x : 2
  · apply Subtype.ext
    have h := congrArg Prod.snd
      (C.chart_retraction_point_pair_value E (TopCat.of (Fin d → ℂ)) e W
        hWe hWN hR 0 hflat z hzW hcenter x.val)
    exact h
  · have h := congrArg Prod.snd
      (C.chart_retraction_point_pair_value E (TopCat.of (Fin d → ℂ)) e W
        hWe hWN hR 0 hflat z hzW hcenter x)
    exact h

end HodgeLean.Foundations.QuotientDuality
