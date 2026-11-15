import HodgeLean.Foundations.QuotientDuality.RetainedCycleZeroPrimeNormalization
import HodgeLean.Foundations.QuotientDuality.RetainedCycleZeroCycleUniqueness
import HodgeLean.Foundations.QuotientDuality.RetainedCycleZeroIntrinsicImage
import HodgeLean.Foundations.QuotientDuality.RetainedCycleIntrinsicCapCriterion
import HodgeLean.Foundations.QuotientDuality.RetainedCycleCapUnit

/-! # Intrinsic supported integration in dimension zero

Consumer: RetainedCycleConsumerSteps.lean:42, through RetainedCycleProofs.lean:249.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open HodgeLean.Adapters HodgeLean.Foundations.Program HodgeLean.Foundations.Analytic
namespace HodgeLean.Foundations.QuotientDuality

/-- Every normalized zero-dimensional prime class has the specified all-class intrinsic integration equation. -/
lemma retained_zero_intrinsic_pairing
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (hdim : TopologicalSpace.dim X.left = 0)
    (c : Homology ℚ (a3b4_an X.hom) 0)
    (hn : ∀ (E : OpenPartialHomeomorph (ComplexPoint X) (Fin 0 → ℂ)),
      (∀ j, (f4_analytification X).IsHolFun (fun u : E.source => E u j)) →
      ∀ x (hx : x ∈ E.source), localOrientation (a3b4_an X.hom) 0 c x =
        localClassOfChart 0 E x hx)
    (ξ : X.left) (hc : Order.coheight ξ = 0)
    (a : s2e_supportedClass X (properPrime ξ) 0)
    (ha : a3b4_IsCycleClass X.hom (properPrime ξ) 0 a) :
    ∀ u : Cohomology ℚ (a3b4_an X.hom) 0,
      properCyclePairing (a3b4_an X.hom) 0 c
        (s2e_classToAbsolute X (properPrime ξ) 0 a) u =
      orientationIntegral (a3b4_an (intrinsicComponent X ξ).hom) 0
        (retainedIntrinsicFundamentalClass X 0 hdim ξ hc)
        (s2e_pullback ℚ (intrinsicComponentInclusion X ξ) 0 u) := by
  apply (retained_intrinsic_integral_iff_cap_image X 0 hdim c ξ hc a).mpr
  rw [retained_zero_prime_absolute_unit X hdim ξ a ha,
    retained_zero_intrinsic_component_image X hdim c hn ξ hc]
  exact retained_cap_with_orientation_unit (a3b4_an X.hom) 0 c

/-- The intrinsic supported class interface in dimension zero, with the specified fundamental class and supported uniqueness. -/
lemma retained_zero_intrinsic_supported_class
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (hdim : TopologicalSpace.dim X.left = 0)
    (c : Homology ℚ (a3b4_an X.hom) 0)
    (hn : ∀ (E : OpenPartialHomeomorph (ComplexPoint X) (Fin 0 → ℂ)),
      (∀ j, (f4_analytification X).IsHolFun (fun u : E.source => E u j)) →
      ∀ x (hx : x ∈ E.source), localOrientation (a3b4_an X.hom) 0 c x =
        localClassOfChart 0 E x hx)
    (ξ : X.left) (hc : Order.coheight ξ = 0) :
    ∃! a : s2e_supportedClass X (properPrime ξ) 0,
      a3b4_IsCycleClass X.hom (properPrime ξ) 0 a ∧
      ∀ u : Cohomology ℚ (a3b4_an X.hom) 0,
        properCyclePairing (a3b4_an X.hom) 0 c
          (s2e_classToAbsolute X (properPrime ξ) 0 a) u =
        orientationIntegral (a3b4_an (intrinsicComponent X ξ).hom) 0
          (retainedIntrinsicFundamentalClass X 0 hdim ξ hc)
          (s2e_pullback ℚ (intrinsicComponentInclusion X ξ) 0 u) := by
  obtain ⟨a, ha, hu⟩ := retained_zero_cycle_normalized_unique X hdim (properPrime ξ)
  exact ⟨a, ⟨ha, retained_zero_intrinsic_pairing X hdim c hn ξ hc a ha⟩,
    fun b hb => hu b hb.1⟩

end HodgeLean.Foundations.QuotientDuality
