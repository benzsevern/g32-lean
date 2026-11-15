import HodgeLean.Foundations.QuotientDuality.ProperCycleIntrinsicSupportSumSurjective
import HodgeLean.Foundations.QuotientDuality.ProperCycleIntrinsicSupportSumNaturality

/-! # The specified intrinsic basis of actual pure support homology
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular TopologicalSpace
open HodgeLean.Adapters
namespace HodgeLean.Foundations.QuotientDuality

/-- Actual prime coefficients and specified intrinsic component classes form a linear equivalence with ordinary middle homology of the literal cycle support.
Source: properCycle_intrinsic_support_sum_injective; properCycle_intrinsic_support_sum_surjective.
HC no distance; AV milestone no distance. -/
def properCycle_intrinsic_support_basis
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (k : ℕ) (hk : 0 < k) (hdim : TopologicalSpace.dim X.left = 2*k)
    (γ : AlgebraicCycle X.left ℚ) (hc : ∀ ξ ∈ γ.support, Order.coheight ξ = k) :
    (γ.support → ℚ) ≃ₗ[ℚ] Homology ℚ (TopCat.of (a3b4_cycleSupport X.hom γ)) (2*k) :=
  LinearEquiv.ofBijective (properCycle_intrinsic_support_sum X k hdim γ hc)
    ⟨properCycle_intrinsic_support_sum_injective X k hdim γ hc,
      properCycle_intrinsic_support_sum_surjective X k hk hdim γ hc⟩

end HodgeLean.Foundations.QuotientDuality
