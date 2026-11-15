import HodgeLean.Foundations.QuotientDuality.RetainedCycleIntrinsicCapCoordinates

/-! # The actual intrinsic image of literal prime coordinates -/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open HodgeLean.Adapters HodgeLean.Foundations.Program
open scoped BigOperators
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.QuotientDuality

/-- Literal cap coordinates on a prime give its specified intrinsic ambient homology image. -/
lemma retained_prime_cap_image_of_literal_coordinates
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (k : ℕ) (hk : 0 < k) (hdim : TopologicalSpace.dim X.left = 2*k)
    (ξ : X.left) (hc : ∀ y ∈ (properPrime ξ).support, Order.coheight y = k)
    (c : Homology ℚ (a3b4_an X.hom) (2*k+2*k))
    (a : s2e_supportedClass X (properPrime ξ) k)
    (ha : properCycle_cap_coordinates X k hk hdim (properPrime ξ) hc c a =
      (fun y => properPrime ξ y.val)) :
    capCohomologyLinear ℚ (a3b4_an X.hom) (2*k) (2*k)
      ((cochainCohomologyEquiv ℚ (a3b4_an X.hom) (2*k)).symm
        (s2e_classToAbsolute X (properPrime ξ) k a)) c =
      properCycle_intrinsic_component X k ξ := by
  classical
  rw [retained_absolute_cap_intrinsic_coordinates X k hk hdim (properPrime ξ) hc c a,
    ha, properCycle_extend_literal_coordinates]
  rw [finsum_eq_single _ ξ (by intro y hy; simp [properPrime, hy])]
  simp [properPrime]

/-- Every actual prime cap image is its literal prime coordinate times the intrinsic image. -/
lemma retained_prime_cap_image_coordinate
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (k : ℕ) (hk : 0 < k) (hdim : TopologicalSpace.dim X.left = 2*k)
    (ξ : X.left) (hc : ∀ y ∈ (properPrime ξ).support, Order.coheight y = k)
    (c : Homology ℚ (a3b4_an X.hom) (2*k+2*k))
    (a : s2e_supportedClass X (properPrime ξ) k) :
    capCohomologyLinear ℚ (a3b4_an X.hom) (2*k) (2*k)
      ((cochainCohomologyEquiv ℚ (a3b4_an X.hom) (2*k)).symm
        (s2e_classToAbsolute X (properPrime ξ) k a)) c =
      properCycle_cap_coordinates X k hk hdim (properPrime ξ) hc c a
        ⟨ξ, by simp [properPrime]⟩ • properCycle_intrinsic_component X k ξ := by
  classical
  rw [retained_absolute_cap_intrinsic_coordinates X k hk hdim (properPrime ξ) hc c a]
  rw [finsum_eq_single _ ξ (by
    intro y hy
    simp [properCycle_extend_coordinates, properPrime, hy])]
  simp [properCycle_extend_coordinates, properPrime]

end HodgeLean.Foundations.QuotientDuality
