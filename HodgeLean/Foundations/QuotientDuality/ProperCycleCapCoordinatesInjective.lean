import HodgeLean.Foundations.QuotientDuality.ProperCycleOriginalSupportCapInjective
import HodgeLean.Foundations.QuotientDuality.ProperCycleCapCoordinateSupportFactorization

/-! # Injectivity of the original constructed middle support cap coordinates
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular TopologicalSpace
open HodgeLean.Adapters
namespace HodgeLean.Foundations.QuotientDuality

/-- The original constructed component coordinates detect every supported class under the original ambient orientation-line and concentration data.
Source: properCycle_original_support_cap_injective; properCycle_cap_coordinates_support_factorization.
HC no distance; AV milestone no distance. -/
lemma properCycle_cap_coordinates_injective
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (k : ℕ) (hk : 0 < k) (hdim : TopologicalSpace.dim X.left = 2*k)
    (γ : AlgebraicCycle X.left ℚ) (hc : ∀ ξ ∈ γ.support, Order.coheight ξ = k)
    (c : Homology ℚ (a3b4_an X.hom) (2*k+2*k))
    (hlocal : ∀ x, Function.Bijective (orientationLine (a3b4_an X.hom) (2*k+2*k) c x))
    (hvan : ∀ j : ℕ, j ≠ 2*k+2*k → ∀ x : a3b4_an X.hom,
      Subsingleton (orientationGroup (a3b4_an X.hom) j x)) :
    Function.Injective (properCycle_cap_coordinates X k hk hdim γ hc c) := by
  intro a b hab
  apply properCycle_original_support_cap_injective X k hdim γ hc c hlocal hvan
  rw [properCycle_cap_coordinates_support_factorization X k hk hdim γ hc c a,
    properCycle_cap_coordinates_support_factorization X k hk hdim γ hc c b, hab]

end HodgeLean.Foundations.QuotientDuality
