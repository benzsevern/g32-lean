import HodgeLean.Foundations.QuotientDuality.ProperCycleCollarChartPointInput
import HodgeLean.Foundations.QuotientDuality.ProperCycleCollarChartLocalCap
import HodgeLean.Foundations.QuotientDuality.ProperCycleComplexLocalCapLinearity
import HodgeLean.Foundations.QuotientDuality.ProperCycleTangentProjectionMap

/-! # The actual collar cap in the original complex product degrees
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular TopologicalSpace
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual collar chart cap in the original complex degrees is the original variable-coclass product cap with its ambient input transported by the literal restricted chart point map.
Source: ProperCycleSupportCollar.chart_cap_naturality; ProperCycleSupportCollar.chart_triad_point_input; properCycle_complex_product_local_cap.
HC no distance; AV milestone no distance. -/
lemma ProperCycleSupportCollar.chart_complex_local_cap
    {X : TopCat.{0}} [T1Space X] {S : Set X} (C : ProperCycleSupportCollar X S) (hS : IsClosed S)
    (r d : ℕ) (e : OpenPartialHomeomorph X ((Fin r → ℂ) × (Fin d → ℂ)))
    (W : Opens X) (hWe : (W : Set X) ⊆ e.source) (hWN : (W : Set X) ⊆ C.neighborhood)
    (hR : ∀ (x : X) (hx : x ∈ W), (C.retraction ⟨x, hWN hx⟩).val ∈ e.source)
    (hflat : ∀ x ∈ e.source, x ∈ S ↔ (e x).2 = 0)
    (z : S) (hzW : z.val ∈ W) (hcenter : e z.val = (0, 0))
    (a : RelativeCohomology ℚ (TopPair.ofSubset
      (X := TopCat.of ((Fin r → ℂ) × (Fin d → ℂ))) (Prod.snd ⁻¹' ({0} : Set (Fin d → ℂ))ᶜ)) (2*d))
    (c : orientationGroup (TopCat.of W) (2*(r+d)) ⟨z.val, hzW⟩) :
    let degree := eqToIso (congrArg
      (fun n => orientationGroup (TopCat.of W) n ⟨z.val, hzW⟩)
      (show 2*(r+d) = 2*d+2*r by omega))
    relativeHomologyMap ℚ (2*r)
      (properCycle_flat_support_point_pair X S e 0 hflat z (hWe hzW) (congrArg Prod.fst hcenter))
      (C.chart_local_support_cap hS (Fin r → ℂ) (TopCat.of (Fin d → ℂ)) e W hWe hWN hR
        0 hflat z hzW hcenter (2*d) (2*r) (degree.hom.hom c) a) =
    properCycle_complex_product_local_cap r d a
      (relativeHomologyMap ℚ (2*(r+d))
        (properCycle_chart_image_point_pair X (Fin r → ℂ) (TopCat.of (Fin d → ℂ))
          e W hWe z.val hzW 0 hcenter ≫
          properCycle_product_neighborhood_point_pair (Fin r → ℂ) (TopCat.of (Fin d → ℂ))
            0 (e '' (W : Set X)) ⟨z.val, hzW, hcenter⟩) c) := by
  dsimp only
  let degree := eqToIso (congrArg
    (fun n => orientationGroup (TopCat.of W) n ⟨z.val, hzW⟩)
    (show 2*(r+d) = 2*d+2*r by omega))
  have h := C.chart_cap_naturality (Fin r → ℂ) (TopCat.of (Fin d → ℂ)) e W hWe hWN hR
    0 hflat z hzW hcenter (2*d) (2*r) a
    ((C.restricted_point_triad_iso hS W hWN z hzW (2*d+2*r)).inv.hom (degree.hom.hom c))
  dsimp only at h
  rw [C.chart_triad_point_input hS (Fin r → ℂ) (TopCat.of (Fin d → ℂ)) e W hWe hWN hR
    0 hflat z hzW hcenter (2*d+2*r) (degree.hom.hom c)] at h
  rw [properCycle_relative_homology_degree_iso_map _ (2*(r+d)) (2*d+2*r) (by omega)] at h
  unfold properCycle_complex_product_local_cap
  change _ = (properCycle_product_tangent_local_homology_iso (Fin r → ℂ) (Fin d → ℂ) (2*r)).hom.hom _
  rw [properCycle_product_tangent_local_homology_iso_map]
  exact h

end HodgeLean.Foundations.QuotientDuality
