import HodgeLean.Foundations.QuotientDuality.ProperCycleIntrinsicSupportBasis
import HodgeLean.Foundations.QuotientDuality.ProperCycleOriginalSupportCap
import HodgeLean.Foundations.QuotientDuality.ProperCycleComplexCapScalar

/-! # Actual linear component coordinates of the original supported cap
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular TopologicalSpace
open HodgeLean.Adapters HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

/-- Apply the original support cap, take its specified intrinsic homology coordinates, and divide by the original nonzero complex cap scalar.
Source: properCycle_original_support_cap; properCycle_intrinsic_support_basis; properCycle_standard_complex_cap_scalar_ne_zero.
HC no distance; AV milestone no distance. -/
def properCycle_cap_coordinates
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (k : ℕ) (hk : 0 < k) (hdim : TopologicalSpace.dim X.left = 2*k)
    (γ : AlgebraicCycle X.left ℚ) (hc : ∀ ξ ∈ γ.support, Order.coheight ξ = k)
    (c : Homology ℚ (a3b4_an X.hom) (2*k+2*k)) :
    s2e_supportedClass X γ k →ₗ[ℚ] (γ.support → ℚ) :=
  (properCycle_standard_complex_cap_scalar k k)⁻¹ •
    ((properCycle_intrinsic_support_basis X k hk hdim γ hc).symm.toLinearMap.comp
      (properCycle_original_support_cap X γ k c))

end HodgeLean.Foundations.QuotientDuality
