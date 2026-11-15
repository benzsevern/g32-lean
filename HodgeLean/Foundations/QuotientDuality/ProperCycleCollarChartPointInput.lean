import HodgeLean.Foundations.QuotientDuality.ProperCycleCollarRestrictedPointIso
import HodgeLean.Foundations.QuotientDuality.ProperCycleCollarChartTriadMap
import HodgeLean.Foundations.QuotientDuality.ProperCycleCollarChartPointMap
import HodgeLean.Foundations.QuotientDuality.ProperCycleTriadPointPairComparison
import HodgeLean.Foundations.QuotientDuality.ProperCycleNormalProductLocalCap

/-! # Original ambient point inputs in the actual collar chart cap diagram
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular TopologicalSpace
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual collar chart triad map transports inverse point excision using exactly the original restricted chart point map.
Source: properCycle_triad_point_pair_inverse_comparison; ProperCycleSupportCollar.chart_retraction_point_map_eq.
HC no distance; AV milestone no distance. -/
lemma ProperCycleSupportCollar.chart_triad_point_input
    {X : TopCat.{0}} [T1Space X] {S : Set X} (C : ProperCycleSupportCollar X S) (hS : IsClosed S)
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (Y : TopCat.{0}) [T1Space Y]
    (e : OpenPartialHomeomorph X (E × Y)) (W : Opens X)
    (hWe : (W : Set X) ⊆ e.source) (hWN : (W : Set X) ⊆ C.neighborhood)
    (hR : ∀ (x : X) (hx : x ∈ W), (C.retraction ⟨x, hWN hx⟩).val ∈ e.source)
    (y : Y) (hflat : ∀ x ∈ e.source, x ∈ S ↔ (e x).2 = y)
    (z : S) (hzW : z.val ∈ W) (hcenter : e z.val = (0, y)) (n : ℕ)
    (c : orientationGroup (TopCat.of W) n ⟨z.val, hzW⟩) :
    (HomologicalComplex.homologyMap
      (C.chart_triad_chain_map E Y e W hWe hWN hR y hflat z hzW hcenter) n).hom
      ((C.restricted_point_triad_iso hS W hWN z hzW n).inv.hom c) =
    (properCycle_normal_product_triad_point_iso E Y y n).inv.hom
      (relativeHomologyMap ℚ n
        (properCycle_chart_image_point_pair X E Y e W hWe z.val hzW y hcenter ≫
          properCycle_product_neighborhood_point_pair E Y y (e '' (W : Set X))
            ⟨z.val, hzW, hcenter⟩) c) := by
  let i : TopCat.of W ⟶ TopCat.of C.neighborhood :=
    TopCat.ofHom ⟨fun x => ⟨x.val, hWN x.property⟩, continuous_subtype_val.subtype_mk _⟩
  have hU : (Prod.snd ⁻¹' {y}ᶜ : Set (E × Y)) ∪ ((Prod.fst ⁻¹' {(0 : E)})ᶜ) =
      ({((0 : E), y)} : Set (E × Y))ᶜ := by
    ext u
    change (u.2 ≠ y ∨ u.1 ≠ 0) ↔ u ≠ (0, y)
    constructor
    · rintro (h | h) he
      · exact h (congrArg Prod.snd he)
      · exact h (congrArg Prod.fst he)
    · intro h
      by_cases h1 : u.1 = 0
      · exact Or.inl (fun h2 => h (Prod.ext h1 h2))
      · exact Or.inr h1
  have h := properCycle_triad_point_pair_inverse_comparison
    (X := TopCat.of W) (Y := TopCat.of (E × Y))
    (⟨z.val, hzW⟩ : W) ((0 : E), y)
    (C.chart_retraction_point_pair E Y e W hWe hWN hR y hflat z hzW hcenter)
    (Subtype.val ⁻¹' Sᶜ)
    ((fun x : W => C.retraction ⟨x.val, hWN x.property⟩) ⁻¹' {z}ᶜ)
    (Prod.snd ⁻¹' {y}ᶜ) ((Prod.fst ⁻¹' {(0 : E)})ᶜ)
    (C.chart_retraction_triad_maps E Y e W hWe hWN hR y hflat z hzW hcenter).1
    (C.chart_retraction_triad_maps E Y e W hWe hWN hR y hflat z hzW hcenter).2
    (hS.isOpen_compl.preimage continuous_subtype_val)
    ((isClosed_singleton (x := z)).isOpen_compl.preimage
      (C.retraction.hom.continuous.comp i.hom.continuous))
    (isClosed_singleton.isOpen_compl.preimage continuous_snd)
    ((isClosed_singleton.preimage continuous_fst).isOpen_compl)
    (C.restricted_point_triad_union W hWN z hzW) hU n c
  change _ = (properCycle_normal_product_triad_point_iso E Y y n).inv.hom
    (relativeHomologyMap ℚ n (C.chart_retraction_point_pair E Y e W hWe hWN hR y hflat z hzW hcenter) c) at h
  rw [C.chart_retraction_point_map_eq E Y e W hWe hWN hR y hflat z hzW hcenter n] at h
  exact h

end HodgeLean.Foundations.QuotientDuality
