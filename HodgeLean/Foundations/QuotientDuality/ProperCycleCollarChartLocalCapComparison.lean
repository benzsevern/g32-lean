import HodgeLean.Foundations.QuotientDuality.ProperCycleCollarChartLocalCap
import HodgeLean.Foundations.QuotientDuality.ProperCycleCollarChartPointInput
import HodgeLean.Foundations.QuotientDuality.ProperCycleNormalProductSupportCap

/-! # Actual collar local caps compared with original normal-product caps
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular TopologicalSpace
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual collar local support cap, in the original tangential support coordinates, equals the original normal-product support cap on exactly the original chart image of its ambient point class.
Source: ProperCycleSupportCollar.chart_cap_naturality; ProperCycleSupportCollar.chart_triad_point_input.
HC no distance; AV milestone no distance. -/
lemma ProperCycleSupportCollar.chart_local_support_cap_comparison
    {X : TopCat.{0}} [T1Space X] {S : Set X} (C : ProperCycleSupportCollar X S) (hS : IsClosed S)
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (Y : TopCat.{0}) [T1Space Y]
    (e : OpenPartialHomeomorph X (E × Y)) (W : Opens X)
    (hWe : (W : Set X) ⊆ e.source) (hWN : (W : Set X) ⊆ C.neighborhood)
    (hR : ∀ (x : X) (hx : x ∈ W), (C.retraction ⟨x, hWN hx⟩).val ∈ e.source)
    (y : Y) (hflat : ∀ x ∈ e.source, x ∈ S ↔ (e x).2 = y)
    (z : S) (hzW : z.val ∈ W) (hcenter : e z.val = (0, y)) (p : ℕ)
    (c : orientationGroup (TopCat.of W) (p + Module.finrank ℝ E) ⟨z.val, hzW⟩)
    (a : RelativeCohomology ℚ (TopPair.ofSubset (X := TopCat.of (E × Y)) (Prod.snd ⁻¹' {y}ᶜ)) p) :
    relativeHomologyMap ℚ (Module.finrank ℝ E)
        (properCycle_flat_support_point_pair X S e y hflat z (hWe hzW) (congrArg Prod.fst hcenter))
      (C.chart_local_support_cap hS E Y e W hWe hWN hR y hflat z hzW hcenter
        p (Module.finrank ℝ E) c a) =
    properCycle_normal_product_support_cap E Y y p
      (relativeHomologyMap ℚ (p + Module.finrank ℝ E)
        (properCycle_chart_image_point_pair X E Y e W hWe z.val hzW y hcenter ≫
          properCycle_product_neighborhood_point_pair E Y y (e '' (W : Set X))
            ⟨z.val, hzW, hcenter⟩) c) a := by
  have h := C.chart_cap_naturality E Y e W hWe hWN hR y hflat z hzW hcenter
    p (Module.finrank ℝ E) a
    ((C.restricted_point_triad_iso hS W hWN z hzW (p + Module.finrank ℝ E)).inv.hom c)
  rw [C.chart_triad_point_input hS E Y e W hWe hWN hR y hflat z hzW hcenter
    (p + Module.finrank ℝ E) c] at h
  exact h

end HodgeLean.Foundations.QuotientDuality
