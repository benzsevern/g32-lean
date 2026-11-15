import HodgeLean.Foundations.QuotientDuality.ProperCycleCollarComplexLocalCap
import HodgeLean.Foundations.QuotientDuality.ProperCycleCollarNormalCoclass

/-! # The original complex cap scalar in actual collar coordinates
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular TopologicalSpace
namespace HodgeLean.Foundations.QuotientDuality

/-- With its actual chart image equal to the specified complex product orientation, the original collar cap of a literal normal multiplicity has exactly that multiplicity times the original complex cap scalar.
Source: ProperCycleSupportCollar.chart_complex_local_cap; properCycle_complex_product_local_cap_multiplicity.
HC no distance; AV milestone no distance. -/
lemma ProperCycleSupportCollar.chart_complex_cap_scalar
    {X : TopCat.{0}} [T1Space X] {S : Set X} (C : ProperCycleSupportCollar X S) (hS : IsClosed S)
    (r d : ℕ) (e : OpenPartialHomeomorph X ((Fin r → ℂ) × (Fin d → ℂ)))
    (W : Opens X) (hWe : (W : Set X) ⊆ e.source) (hWN : (W : Set X) ⊆ C.neighborhood)
    (hR : ∀ (x : X) (hx : x ∈ W), (C.retraction ⟨x, hWN hx⟩).val ∈ e.source)
    (hflat : ∀ x ∈ e.source, x ∈ S ↔ (e x).2 = 0)
    (z : S) (hzW : z.val ∈ W) (hcenter : e z.val = (0, 0))
    (c : orientationGroup (TopCat.of W) (2*(r+d)) ⟨z.val, hzW⟩)
    (hc : relativeHomologyMap ℚ (2*(r+d))
      (properCycle_chart_image_point_pair X (Fin r → ℂ) (TopCat.of (Fin d → ℂ))
        e W hWe z.val hzW 0 hcenter ≫
        properCycle_product_neighborhood_point_pair (Fin r → ℂ) (TopCat.of (Fin d → ℂ))
          0 (e '' (W : Set X)) ⟨z.val, hzW, hcenter⟩) c =
      properCycle_complex_product_standard_orientation r d)
    (m : ℚ) :
    let degree := eqToIso (congrArg
      (fun n => orientationGroup (TopCat.of W) n ⟨z.val, hzW⟩)
      (show 2*(r+d) = 2*d+2*r by omega))
    relativeHomologyMap ℚ (2*r)
      (properCycle_flat_support_point_pair X S e 0 hflat z (hWe hzW) (congrArg Prod.fst hcenter))
      (C.chart_local_support_cap hS (Fin r → ℂ) (TopCat.of (Fin d → ℂ)) e W hWe hWN hR
        0 hflat z hzW hcenter (2*d) (2*r) (degree.hom.hom c)
        (m • relativeCohomologyMap ℚ (2*d)
          (properCycle_product_support_projection (Fin r → ℂ) (TopCat.of (Fin d → ℂ)) {0})
          (normalizedRelativeCoclass (standardComplexLocalClass ℚ d)
            (standardComplexLocalClass_ne_zero_for_chart d)))) =
      (m * properCycle_standard_complex_cap_scalar r d) • standardComplexLocalClass ℚ r := by
  dsimp only
  rw [C.chart_complex_local_cap hS r d e W hWe hWN hR hflat z hzW hcenter, hc,
    properCycle_complex_product_local_cap_multiplicity]

end HodgeLean.Foundations.QuotientDuality
