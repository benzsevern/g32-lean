import HodgeLean.Foundations.QuotientDuality.ProperCycleOriginalComplexCapStandard
import HodgeLean.Foundations.QuotientDuality.ProperCycleCapCoordinateSupportFactorization
import HodgeLean.Foundations.QuotientDuality.ProperCycleCapCoordinateAbsoluteFactorization

/-! # Intrinsic cap coordinates with the specified complex normalization -/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open HodgeLean.Adapters HodgeLean.Foundations.Program
open scoped BigOperators
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.QuotientDuality

/-- The original support cap is the intrinsic component sum with its literal normalized coordinates. -/
theorem retained_support_cap_intrinsic_coordinates
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (k : ℕ) (hk : 0 < k) (hdim : TopologicalSpace.dim X.left = 2*k)
    (γ : AlgebraicCycle X.left ℚ) (hc : ∀ ξ ∈ γ.support, Order.coheight ξ = k)
    (c : Homology ℚ (a3b4_an X.hom) (2*k+2*k))
    (a : s2e_supportedClass X γ k) :
    properCycle_original_support_cap X γ k c a =
      properCycle_intrinsic_support_sum X k hdim γ hc
        (properCycle_cap_coordinates X k hk hdim γ hc c a) := by
  have hs := (properCycle_standard_complex_cap_scalar_formula k k).trans
    (properCycle_original_complex_cap_standard k k)
  have hscalar : properCycle_standard_complex_cap_scalar k k = (1 : ℚ) :=
    smul_left_injective ℚ (standardComplexLocalClass_ne_zero_for_chart k)
      (hs.trans (one_smul ℚ (standardComplexLocalClass ℚ k)).symm)
  rw [properCycle_cap_coordinates_support_factorization, hscalar, one_smul]

/-- Forgetting support carries the normalized intrinsic coordinate sum to the actual absolute cap. -/
theorem retained_absolute_cap_intrinsic_coordinates
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (k : ℕ) (hk : 0 < k) (hdim : TopologicalSpace.dim X.left = 2*k)
    (γ : AlgebraicCycle X.left ℚ) (hc : ∀ ξ ∈ γ.support, Order.coheight ξ = k)
    (c : Homology ℚ (a3b4_an X.hom) (2*k+2*k))
    (a : s2e_supportedClass X γ k) :
    capCohomologyLinear ℚ (a3b4_an X.hom) (2*k) (2*k)
      ((cochainCohomologyEquiv ℚ (a3b4_an X.hom) (2*k)).symm
        (s2e_classToAbsolute X γ k a)) c =
      ∑ᶠ ξ, properCycle_extend_coordinates X.left γ
        (properCycle_cap_coordinates X k hk hdim γ hc c a) ξ •
          properCycle_intrinsic_component X k ξ := by
  rw [← properCycle_original_support_cap_inclusion,
    retained_support_cap_intrinsic_coordinates,
    properCycle_intrinsic_support_sum_inclusion]

end HodgeLean.Foundations.QuotientDuality
