import HodgeLean.Foundations.QuotientDuality.RetainedCyclePrimeCoordinateCapImage
import HodgeLean.Foundations.QuotientDuality.ProperCycleCapCoordinatesInjective

/-! # Detection of supported prime classes by their actual ambient cap image -/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open HodgeLean.Adapters HodgeLean.Foundations.Program
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.QuotientDuality

/-- A nonzero intrinsic prime image makes the actual ambient cap injective on its supported classes. -/
lemma retained_prime_absolute_cap_injective
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (k : ℕ) (hk : 0 < k) (hdim : TopologicalSpace.dim X.left = 2*k)
    (ξ : X.left) (hc : ∀ y ∈ (properPrime ξ).support, Order.coheight y = k)
    (c : Homology ℚ (a3b4_an X.hom) (2*k+2*k))
    (ho : ∀ x, Function.Bijective (orientationLine (a3b4_an X.hom) (2*k+2*k) c x))
    (hv : ∀ j : ℕ, j ≠ 2*k+2*k → ∀ x : a3b4_an X.hom,
      Subsingleton (orientationGroup (a3b4_an X.hom) j x))
    (hn : properCycle_intrinsic_component X k ξ ≠ 0) :
    Function.Injective (fun a : s2e_supportedClass X (properPrime ξ) k =>
      capCohomologyLinear ℚ (a3b4_an X.hom) (2*k) (2*k)
        ((cochainCohomologyEquiv ℚ (a3b4_an X.hom) (2*k)).symm
          (s2e_classToAbsolute X (properPrime ξ) k a)) c) := by
  classical
  intro a b hab
  dsimp only at hab
  rw [retained_prime_cap_image_coordinate X k hk hdim ξ hc c a,
    retained_prime_cap_image_coordinate X k hk hdim ξ hc c b] at hab
  have he := smul_left_injective ℚ hn hab
  apply properCycle_cap_coordinates_injective X k hk hdim (properPrime ξ) hc c ho hv
  ext y
  have hy : y.val = ξ := by
    by_contra h
    exact y.property (by simp [properPrime, h])
  have hy' : y = ⟨ξ, by simp [properPrime]⟩ := Subtype.ext hy
  simpa only [hy'] using he

end HodgeLean.Foundations.QuotientDuality
