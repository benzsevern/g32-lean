import HodgeLean.Foundations.QuotientDuality.ProperCycleCollarNormalProjectionSquare

/-! # The original chart normal coclass under the actual collar map
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular TopologicalSpace
namespace HodgeLean.Foundations.QuotientDuality

/-- Pulling the original product normal coclass back by actual collar coordinates gives exactly the original chart normal projection coclass.
Source: ProperCycleSupportCollar.chart_normal_projection_square; chartNormalProjectionCoclass.
HC no distance; AV milestone no distance. -/
lemma ProperCycleSupportCollar.chart_normal_coclass
    {X : TopCat.{0}} {S : Set X} (C : ProperCycleSupportCollar X S)
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (d : ℕ)
    (e : OpenPartialHomeomorph X (E × (Fin d → ℂ))) (W : Opens X)
    (hWe : (W : Set X) ⊆ e.source) (hWN : (W : Set X) ⊆ C.neighborhood)
    (hR : ∀ (x : X) (hx : x ∈ W), (C.retraction ⟨x, hWN hx⟩).val ∈ e.source)
    (hflat : ∀ x ∈ e.source, x ∈ S ↔ (e x).2 = 0)
    (z : S) (hzW : z.val ∈ W) (hcenter : e z.val = (0, 0)) :
    relativeCohomologyMap ℚ (2 * d)
      (TopPair.ofSubsetHom (X := TopCat.of W) (Y := TopCat.of (E × (Fin d → ℂ)))
        (TopPair.Hom.fst (C.chart_retraction_point_pair E (TopCat.of (Fin d → ℂ)) e W
          hWe hWN hR 0 hflat z hzW hcenter))
        (C.chart_retraction_triad_maps E (TopCat.of (Fin d → ℂ)) e W
          hWe hWN hR 0 hflat z hzW hcenter).1)
      (relativeCohomologyMap ℚ (2 * d)
        (properCycle_product_support_projection E (TopCat.of (Fin d → ℂ)) {0})
        (normalizedRelativeCoclass (standardComplexLocalClass ℚ d)
          (standardComplexLocalClass_ne_zero_for_chart d))) =
    chartNormalProjectionCoclass E d e S hflat (W : Set X) hWe := by
  rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp,
    C.chart_normal_projection_square E d e W hWe hWN hR hflat z hzW hcenter]
  rfl

end HodgeLean.Foundations.QuotientDuality
