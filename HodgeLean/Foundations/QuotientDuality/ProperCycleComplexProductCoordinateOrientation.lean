import HodgeLean.Foundations.QuotientDuality.ProperCycleComplexLinearOrientation
import HodgeLean.Foundations.QuotientDuality.ProperCycleChartOrientationComparison

/-! # Original complex product orientation in specified linear coordinates
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual origin-complement pair isomorphism of a specified complex linear product coordinate equivalence.
Source: AlgebraicTopology.Singular.TopPair.isoOfSubset; ContinuousLinearEquiv.map_eq_zero_iff.
HC no distance; AV milestone no distance. -/
def properCycle_complex_product_coordinate_pair_iso (r d : ℕ)
    (L : ((Fin r → ℂ) × (Fin d → ℂ)) ≃L[ℂ] (Fin (r+d) → ℂ)) :
    TopPair.ofSubset (X := TopCat.of ((Fin r → ℂ) × (Fin d → ℂ)))
      ({(0,0)} : Set ((Fin r → ℂ) × (Fin d → ℂ)))ᶜ ≅ puncturedPair ℂ (r+d) :=
  TopPair.isoOfSubset L.toHomeomorph (fun _ => not_congr L.map_eq_zero_iff)

/-- The frozen original product orientation is the standard complex class through its specified original linear point-pair coordinates.
Source: properCycle_local_homeomorph_point_identification; properCycle_complex_product_standard_orientation_iso.
HC no distance; AV milestone no distance. -/
theorem properCycle_complex_product_orientation_original_pair (r d : ℕ) :
    let L : ((Fin r → ℂ) × (Fin d → ℂ)) ≃L[ℂ] (Fin (r+d) → ℂ) :=
      ContinuousLinearEquiv.ofFinrankEq
        (by simp only [Module.finrank_prod, Module.finrank_pi, Fintype.card_fin])
    properCycle_complex_product_standard_orientation r d =
      relativeHomologyMap ℚ (2*(r+d)) (properCycle_complex_product_coordinate_pair_iso r d L).inv
        (standardComplexLocalClass ℚ (r+d)) := by
  dsimp only
  let L : ((Fin r → ℂ) × (Fin d → ℂ)) ≃L[ℂ] (Fin (r+d) → ℂ) :=
    ContinuousLinearEquiv.ofFinrankEq
      (by simp only [Module.finrank_prod, Module.finrank_pi, Fintype.card_fin])
  have h0 : L.toHomeomorph (0,0) = 0 := map_zero L
  unfold properCycle_complex_product_standard_orientation properCycle_complex_product_standard_orientation_iso
  rw [properCycle_local_homeomorph_point_identification
    (X := TopCat.of ((Fin r → ℂ) × (Fin d → ℂ))) (Y := TopCat.of (Fin (r+d) → ℂ))
    L.toHomeomorph (0,0) 0 h0]
  rfl

/-- The frozen original product orientation is the specified standard complex class in every actual complex linear product coordinate equivalence.
Source: properCycle_complex_product_orientation_original_pair; properCycle_complex_linear_standard_orientation.
HC no distance; AV milestone no distance. -/
theorem properCycle_complex_product_orientation_coordinates (r d : ℕ)
    (L : ((Fin r → ℂ) × (Fin d → ℂ)) ≃L[ℂ] (Fin (r+d) → ℂ)) :
    properCycle_complex_product_standard_orientation r d =
      relativeHomologyMap ℚ (2*(r+d)) (properCycle_complex_product_coordinate_pair_iso r d L).inv
        (standardComplexLocalClass ℚ (r+d)) := by
  let L₀ : ((Fin r → ℂ) × (Fin d → ℂ)) ≃L[ℂ] (Fin (r+d) → ℂ) :=
    ContinuousLinearEquiv.ofFinrankEq
      (by simp only [Module.finrank_prod, Module.finrank_pi, Fintype.card_fin])
  let E := properCycle_complex_product_coordinate_pair_iso r d L
  let E₀ := properCycle_complex_product_coordinate_pair_iso r d L₀
  let F₀ := (relativeHomologyFunctor ℚ (2*(r+d))).mapIso E₀
  let C := L.symm.trans L₀
  let CE : puncturedPair ℂ (r+d) ≅ puncturedPair ℂ (r+d) :=
    TopPair.isoOfSubset C.toHomeomorph (fun _ => not_congr C.map_eq_zero_iff)
  have hp : E.inv ≫ E₀.hom = CE.hom := by
    ext z : 2 <;> rfl
  have he := congrArg (fun f => relativeHomologyMap ℚ (2*(r+d)) f
    (standardComplexLocalClass ℚ (r+d))) hp
  simp only [relativeHomologyMap_comp, LinearMap.comp_apply] at he
  have hn := properCycle_complex_linear_standard_orientation (r+d) C
  change relativeHomologyMap ℚ (2*(r+d)) CE.hom
    (standardComplexLocalClass ℚ (r+d)) = standardComplexLocalClass ℚ (r+d) at hn
  have h₀ := properCycle_complex_product_orientation_original_pair r d
  change properCycle_complex_product_standard_orientation r d =
    relativeHomologyMap ℚ (2*(r+d)) E₀.inv (standardComplexLocalClass ℚ (r+d)) at h₀
  rw [h₀]
  apply (ConcreteCategory.bijective_of_isIso F₀.hom).1
  change F₀.hom.hom (F₀.inv.hom (standardComplexLocalClass ℚ (r+d))) =
    relativeHomologyMap ℚ (2*(r+d)) E₀.hom
      (relativeHomologyMap ℚ (2*(r+d)) E.inv (standardComplexLocalClass ℚ (r+d)))
  rw [F₀.inv_hom_id_apply]
  exact (he.trans hn).symm

end HodgeLean.Foundations.QuotientDuality
