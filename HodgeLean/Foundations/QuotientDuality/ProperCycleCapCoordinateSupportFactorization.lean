import HodgeLean.Foundations.QuotientDuality.ProperCycleCapCoordinates

/-! # Original support cap factorization through its actual intrinsic coefficients
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular TopologicalSpace
open HodgeLean.Adapters HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual support cap is the original complex cap scalar times the intrinsic sum of its constructed component coefficients.
Source: properCycle_intrinsic_support_basis; properCycle_standard_complex_cap_scalar_ne_zero.
HC no distance; AV milestone no distance. -/
lemma properCycle_cap_coordinates_support_factorization
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (k : ℕ) (hk : 0 < k) (hdim : TopologicalSpace.dim X.left = 2*k)
    (γ : AlgebraicCycle X.left ℚ) (hc : ∀ ξ ∈ γ.support, Order.coheight ξ = k)
    (c : Homology ℚ (a3b4_an X.hom) (2*k+2*k)) (a : s2e_supportedClass X γ k) :
    properCycle_original_support_cap X γ k c a =
      properCycle_standard_complex_cap_scalar k k •
        properCycle_intrinsic_support_sum X k hdim γ hc
          (properCycle_cap_coordinates X k hk hdim γ hc c a) := by
  let e := properCycle_intrinsic_support_basis X k hk hdim γ hc
  let s := properCycle_standard_complex_cap_scalar k k
  change properCycle_original_support_cap X γ k c a =
    s • e (s⁻¹ • e.symm (properCycle_original_support_cap X γ k c a))
  rw [map_smul, e.apply_symm_apply, smul_smul,
    mul_inv_cancel₀ (properCycle_standard_complex_cap_scalar_ne_zero k k), one_smul]

end HodgeLean.Foundations.QuotientDuality
