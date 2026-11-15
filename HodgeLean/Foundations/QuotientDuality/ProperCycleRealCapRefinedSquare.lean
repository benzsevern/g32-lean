import HodgeLean.Foundations.QuotientDuality.ProperCycleRealCapRefinementHomology

/-! # The actual cap square after the specified support excision
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- Actual refinement inverses express the upper normal cap through the two specified half-ray connecting inverses and the lower normal cap.
Source: properCycle_real_cap_inverse_square; properCycle_real_cap_refinement_inverse_recovery.
HC no distance; AV milestone no distance. -/
theorem properCycle_real_cap_refined_inverse_square
    (Y : TopCat.{0}) (S T : Set Y) (hS : IsClosed S) (hT : IsClosed T)
    (p q : ℕ) (hp : Even p)
    (φ : AlgebraicTopology.Simplicial.Cochain ℚ (TopCat.toSSet.obj (TopCat.of (ℝ × Y))) p)
    (hA : AlgebraicTopology.Simplicial.cochainMap ℚ
      (subsetSingularSubcomplex (TopCat.of (ℝ × Y)) (Prod.snd ⁻¹' Sᶜ)).ι p φ = 0)
    (hφ : AlgebraicTopology.Simplicial.coboundary ℚ p φ = 0) :
    let X := TopCat.of (ℝ × Y)
    let A := subsetSingularSubcomplex X (Prod.snd ⁻¹' Sᶜ)
    let P := subsetSingularSubcomplex X {z | 0 ≤ z.1 ∧ z.2 ∈ T}ᶜ
    let Q := subsetSingularSubcomplex X {z | z.1 ≤ 0 ∧ z.2 ∈ T}ᶜ
    letI := properCycle_real_cap_refinement_left_isIso Y S T hS hT (p+q)
    letI := properCycle_real_cap_refinement_right_isIso Y S T hS hT (p+q)
    inv (HomologicalComplex.homologyMap
        (properCycle_real_cap_source_refinement Y S T).τ₃ (p+q+1)) ≫
      properCycle_subcomplex_cap_homology_map A (P ⊔ Q) p (q+1) hp φ hA hφ =
    (properCycle_real_cap_target_connecting_iso Y (S ∩ T) (hS.inter hT) (p+q)).hom ≫
      inv (HomologicalComplex.homologyMap
        (properCycle_real_cap_source_refinement Y S T).τ₁ (p+q)) ≫
      properCycle_subcomplex_cap_homology_map A (P ⊓ Q) p q hp φ hA hφ ≫
      (properCycle_real_cap_target_connecting_iso Y T hT q).inv := by
  dsimp only
  letI := properCycle_real_cap_refinement_left_isIso Y S T hS hT (p+q)
  letI := properCycle_real_cap_refinement_right_isIso Y S T hS hT (p+q)
  have hc := properCycle_real_cap_inverse_square Y S T hS hT p q hp φ hA hφ
  have hr := properCycle_real_cap_refinement_inverse_recovery Y S T hS hT (p+q)
  let eS := properCycle_real_cap_source_adjacent_iso Y S T hS hT (p+q)
  let eR := properCycle_real_cap_target_connecting_iso Y (S ∩ T) (hS.inter hT) (p+q)
  change eS.inv ≫ _ = _ at hc
  change _ ≫ eS.inv = eR.inv ≫ _ at hr
  change _ = eR.hom ≫ _
  apply (cancel_epi eR.inv).mp
  simp only [← Category.assoc, eR.inv_hom_id, Category.id_comp]
  rw [← hr]
  simp only [Category.assoc]
  rw [hc]

end HodgeLean.Foundations.QuotientDuality
