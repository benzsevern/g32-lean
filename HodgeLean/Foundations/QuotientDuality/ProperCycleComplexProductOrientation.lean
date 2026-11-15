import HodgeLean.Foundations.QuotientDuality.ProperCycleComplexLocalCap

/-! # Actual standard orientations in the complex product cap model -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- Actual complex linear vector coordinates identify the ambient local homology of the product with its original standard complex local homology.
Source: Hatcher, Algebraic Topology, section 3.3, complex orientations in local linear coordinates.
HC no distance; AV milestone no distance. -/
def properCycle_complex_product_standard_orientation_iso (r d : ℕ) :
    orientationGroup (TopCat.of ((Fin r → ℂ) × (Fin d → ℂ))) (2 * (r + d)) (0, 0) ≅
      orientationGroup (TopCat.of (Fin (r + d) → ℂ)) (2 * (r + d)) 0 := by
  let L : ((Fin r → ℂ) × (Fin d → ℂ)) ≃L[ℂ] (Fin (r + d) → ℂ) :=
    ContinuousLinearEquiv.ofFinrankEq
      (by simp only [Module.finrank_prod, Module.finrank_pi, Fintype.card_fin])
  let H := properCycle_local_homology_homeomorph_iso
    (X := TopCat.of ((Fin r → ℂ) × (Fin d → ℂ))) (Y := TopCat.of (Fin (r + d) → ℂ))
    L.toHomeomorph (0, 0) (2 * (r + d))
  have h0 : L.toHomeomorph (0, 0) = 0 := map_zero L
  rw [h0] at H
  exact H

/-- The specified standard complex orientation transported through the actual complex linear product coordinates.
Source: Hatcher, Algebraic Topology, section 3.3, standard complex local orientations.
HC no distance; AV milestone no distance. -/
def properCycle_complex_product_standard_orientation (r d : ℕ) :
    orientationGroup (TopCat.of ((Fin r → ℂ) × (Fin d → ℂ))) (2 * (r + d)) (0, 0) :=
  (properCycle_complex_product_standard_orientation_iso r d).inv.hom
    (standardComplexLocalClass ℚ (r + d))

/-- The actual standard complex product orientation is nonzero in original ambient local homology.
Source: Hatcher, Algebraic Topology, section 3.3, nonzero complex local orientation classes.
HC no distance; AV milestone no distance. -/
lemma properCycle_complex_product_standard_orientation_ne_zero (r d : ℕ) :
    properCycle_complex_product_standard_orientation r d ≠ 0 := by
  intro h
  apply standardComplexLocalClass_ne_zero_for_chart (r + d)
  apply (ConcreteCategory.bijective_of_isIso
    (properCycle_complex_product_standard_orientation_iso r d).inv).1
  change (properCycle_complex_product_standard_orientation_iso r d).inv.hom
      (standardComplexLocalClass ℚ (r + d)) =
    (properCycle_complex_product_standard_orientation_iso r d).inv.hom 0
  rw [map_zero]
  exact h

end HodgeLean.Foundations.QuotientDuality
