import HodgeLean.Foundations.QuotientDuality.ProperCycleCapCoordinateSupportFactorization

/-! # Original absolute cap factorization through actual scheme-point coefficients
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular TopologicalSpace
open HodgeLean.Adapters HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

/-- The original absolute cap factors through the actual component coordinates with the original common complex scalar and specified intrinsic component images.
Source: properCycle_cap_coordinates_support_factorization; properCycle_intrinsic_support_sum_inclusion; properCycle_original_support_cap_inclusion.
HC no distance; AV milestone no distance. -/
lemma properCycle_cap_coordinates_absolute_factorization
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (k : ℕ) (hk : 0 < k) (hdim : TopologicalSpace.dim X.left = 2*k)
    (γ : AlgebraicCycle X.left ℚ) (hc : ∀ ξ ∈ γ.support, Order.coheight ξ = k)
    (c : Homology ℚ (a3b4_an X.hom) (2*k+2*k)) (a : s2e_supportedClass X γ k) :
    capCohomologyLinear ℚ (a3b4_an X.hom) (2*k) (2*k)
        ((cochainCohomologyEquiv ℚ (a3b4_an X.hom) (2*k)).symm
          (s2e_classToAbsolute X γ k a)) c =
      properCycle_standard_complex_cap_scalar k k •
        ∑ᶠ ξ, properCycle_extend_coordinates X.left γ
          (properCycle_cap_coordinates X k hk hdim γ hc c a) ξ •
            properCycle_intrinsic_component X k ξ := by
  have hi := congrArg
    (homologyMap ℚ (2*k) (TopPair.ofSubset (X := a3b4_an X.hom)
      (a3b4_cycleSupport X.hom γ)).map)
    (properCycle_cap_coordinates_support_factorization X k hk hdim γ hc c a)
  rw [map_smul, properCycle_intrinsic_support_sum_inclusion] at hi
  exact (properCycle_original_support_cap_inclusion X γ k c a).symm.trans hi

end HodgeLean.Foundations.QuotientDuality
