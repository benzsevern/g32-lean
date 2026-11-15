import HodgeLean.Foundations.QuotientDuality.ProperCycleComplexNormalProductPairs

/-! # Original normal coclass under actual complex product coordinates
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual complex normal pair coordinates retain the literal original normal-base projection.
Source: properCycle_complex_normal_product_normal_pair_iso; properCycle_real_support_base_pair.
HC no distance; AV milestone no distance. -/
theorem properCycle_complex_normal_product_pair_projection (r d : ℕ) :
    (properCycle_complex_normal_product_normal_pair_iso r d).hom ≫
      properCycle_product_support_projection (Fin r → ℂ) (TopCat.of (Fin d → ℂ)) {0} =
      properCycle_real_support_base_pair (TopCat.of (Fin d → ℂ)) {0} (r*2) := by
  ext z : 2 <;> rfl

/-- The specified product normal coclass pulls back along the actual complex pair coordinates to the original iterated normal coclass.
Source: properCycle_complex_normal_product_pair_projection; properCycle_real_support_coclass_base_projection.
HC no distance; AV milestone no distance. -/
theorem properCycle_complex_normal_coclass_pullback (r d p : ℕ)
    (a : RelativeCohomology ℚ (puncturedPair ℂ d) p) :
    relativeCohomologyMap ℚ p (properCycle_complex_normal_product_normal_pair_iso r d).hom
      (relativeCohomologyMap ℚ p
        (properCycle_product_support_projection (Fin r → ℂ) (TopCat.of (Fin d → ℂ)) {0}) a) =
      properCycle_real_support_coclass (TopCat.of (Fin d → ℂ)) {0} p a (r*2) := by
  rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp,
    properCycle_complex_normal_product_pair_projection]
  exact (properCycle_real_support_coclass_base_projection (TopCat.of (Fin d → ℂ)) {0} p a (r*2)).symm

end HodgeLean.Foundations.QuotientDuality
