import HodgeLean.Foundations.QuotientDuality.RetainedCycleIntrinsicSupportedReduction
import HodgeLean.Foundations.QuotientDuality.RetainedCycleProjectivePrimeImage
import HodgeLean.Foundations.QuotientDuality.RetainedCycleZeroSupportedClass
import HodgeLean.Foundations.QuotientDuality.RetainedCycleRepeatedRealization
import HodgeLean.Foundations.QuotientDuality.RetainedCyclePrimeDetection
import HodgeLean.Foundations.QuotientDuality.RetainedCycleSupportedRepeat
import HodgeLean.Foundations.QuotientDuality.ProperCycleOrientationLineDegree
import HodgeLean.Foundations.QuotientDuality.RetainedCycleWeightedRealization
import HodgeLean.Foundations.QuotientDuality.RetainedCycleOrientationCast
import HodgeLean.Foundations.QuotientDuality.RetainedCycleIntrinsicDegree
import HodgeLean.Foundations.QuotientDuality.RetainedCyclePrimePushforward
import HodgeLean.Foundations.QuotientDuality.RetainedCycleConsumerChecks
import HodgeLean.Foundations.QuotientDuality.RetainedCycleStageEight
import HodgeLean.Foundations.QuotientDuality.RetainedCycleMiddleCapPerfect
import HodgeLean.Foundations.QuotientDuality.RetainedCycleGlobalChecks
import HodgeLean.Foundations.QuotientDuality.RetainedCycleChecks

/-! # General steps for retained supported cycle comparisons

Consumers: s2e-chain-contract.md:675–686, the four P3a review units.
These interfaces distinguish the intrinsic class, supported realization and proper transport.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open HodgeLean.Adapters HodgeLean.Foundations.Program HodgeLean.Foundations.Analytic
open scoped BigOperators Classical
namespace HodgeLean.Foundations.QuotientDuality
namespace ConsumerSteps

/-- The supported class with the specified intrinsic integration normalization
Source: Bredon, Sheaf Theory, second edition, V.9; Kashiwara–Schapira, Sheaves on Manifolds, III.3, duality with support.
HC no distance; AV milestone no distance. -/
theorem intrinsic_supported_class_aux
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (k : ℕ) (hdim : TopologicalSpace.dim X.left = 2 * k)
    (cX : Homology ℚ (a3b4_an X.hom) (2 * (2 * k)))
    (ho : ∀ x, Function.Bijective (orientationLine (a3b4_an X.hom) (2 * (2 * k)) cX x))
    (hv : ∀ j : ℕ, j ≠ 2 * (2 * k) → ∀ x : a3b4_an X.hom,
      Subsingleton (orientationGroup (a3b4_an X.hom) j x))
    (hn : ∀ (E : OpenPartialHomeomorph (ComplexPoint X) (Fin (2 * k) → ℂ)),
      (∀ j, (f4_analytification X).IsHolFun (fun u : E.source => E u j)) →
      ∀ x (hx : x ∈ E.source), localOrientation (a3b4_an X.hom) (2 * (2 * k)) cX x =
        localClassOfChart (2 * k) E x hx)
    (ξ : X.left) (hc : Order.coheight ξ = k) :
    ∃! a : s2e_supportedClass X (properPrime ξ) k,
        a3b4_IsCycleClass X.hom (properPrime ξ) k a ∧
        ∀ u : Cohomology ℚ (a3b4_an X.hom) (2 * k),
          properCyclePairing (a3b4_an X.hom) k cX
            (s2e_classToAbsolute X (properPrime ξ) k a) u =
          orientationIntegral (a3b4_an (intrinsicComponent X ξ).hom) (2 * k) (retainedIntrinsicFundamentalClass X k hdim ξ hc)
            (s2e_pullback ℚ (intrinsicComponentInclusion X ξ) (2 * k) u) := by
  by_cases hk : k = 0
  · subst k
    exact retained_zero_intrinsic_supported_class X hdim cX hn ξ hc
  · exact retained_intrinsic_supported_of_nonzero_image X k (Nat.pos_of_ne_zero hk)
      hdim cX ho hv hn ξ hc (retained_projective_prime_image_ne_zero X k hdim ξ hc)

example := RetainedCycleChecks.check_intrinsic_supported_integration_equation

/-- Realization of the collected normalized weighted sum on its common carrier
Source: Bredon, Sheaf Theory, second edition, V.9; Fulton, Intersection Theory, 19.1.
HC no distance; AV milestone no distance. -/
theorem supported_weighted_realization_aux
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (k : ℕ) {I : Type} [Fintype I] (ξ : I → X.left)
    (hc : ∀ i, Order.coheight (ξ i) = k)
    (cX : Homology ℚ (a3b4_an X.hom) (2 * (2 * k)))
    (hdim : TopologicalSpace.dim X.left = 2 * k)
    (ho : ∀ x, Function.Bijective (orientationLine (a3b4_an X.hom) (2 * (2 * k)) cX x))
    (hv : ∀ j : ℕ, j ≠ 2 * (2 * k) → ∀ x : a3b4_an X.hom,
      Subsingleton (orientationGroup (a3b4_an X.hom) j x))
    (hperfect : Function.Injective (properCyclePairing (a3b4_an X.hom) k cX))
    (cZ : ∀ i, Homology ℚ (a3b4_an (intrinsicComponent X (ξ i)).hom) (2 * k))
    (a : ∀ i, s2e_supportedClass X (properPrime (ξ i)) k)
    (ha : ∀ i, a3b4_IsCycleClass X.hom (properPrime (ξ i)) k (a i))
    (hn : ∀ i (u : Cohomology ℚ (a3b4_an X.hom) (2 * k)),
      properCyclePairing (a3b4_an X.hom) k cX
        (s2e_classToAbsolute X (properPrime (ξ i)) k (a i)) u =
      orientationIntegral (a3b4_an (intrinsicComponent X (ξ i)).hom) (2 * k) (cZ i)
        (s2e_pullback ℚ (intrinsicComponentInclusion X (ξ i)) (2 * k) u))
    (hrepeat : ∀ i j, ξ i = ξ j →
      HEq (cZ i) (cZ j))
    (q : I → ℚ) :
    let Γ : AlgebraicCycle X.left ℚ := ∑ i, (properPrime (ξ i)).mapRange (q i * ·) (mul_zero _)
    let T : Set (ComplexPoint X) := ⋃ i, a3b4_cycleSupport X.hom (properPrime (ξ i))
    ∃ (hΓ : a3b4_cycleSupport X.hom Γ ⊆ T)
      (hi : ∀ i, a3b4_cycleSupport X.hom (properPrime (ξ i)) ⊆ T)
      (b : s2e_supportedClass X Γ k),
      a3b4_IsCycleClass X.hom Γ k b ∧
      enlargeSupport ℚ (a3b4_an X.hom) hΓ (2 * k) b =
        ∑ i, q i • enlargeSupport ℚ (a3b4_an X.hom) (hi i) (2 * k) (a i) := by
  classical
  by_cases hs : Smooth X.hom
  · letI : Smooth X.hom := hs
    apply retained_smooth_weighted_full_carrier X k hdim hv
      (fun i => properPrime (ξ i)) ?_ a ha q
    intro i η hη
    have he : η = ξ i := by
      by_contra hne
      exact hη (by simp [properPrime, hne])
    simpa only [he] using hc i
  · by_cases hk : k = 0
    · exact (hs (properCycle_zero_dimension_smooth X
        (by simpa only [hk, mul_zero] using hdim))).elim
    · let e : 2*(2*k) = 2*k+2*k := by omega
      let c : Homology ℚ (a3b4_an X.hom) (2*k+2*k) :=
        (eqToIso (congrArg (fun j => Homology ℚ (a3b4_an X.hom) j) e)).hom.hom cX
      have ho' : ∀ x, Function.Bijective
          (orientationLine (a3b4_an X.hom) (2*k+2*k) c x) := by
        intro x
        exact properCycle_orientation_line_degree_bijective (a3b4_an X.hom)
          (2*(2*k)) (2*k+2*k) e cX x (ho x)
      have hv' : ∀ j : ℕ, j ≠ 2*k+2*k → ∀ x : a3b4_an X.hom,
          Subsingleton (orientationGroup (a3b4_an X.hom) j x) := by
        intro j hj
        exact hv j (by omega)
      apply retained_weighted_realization_of_supported_repeats X k (Nat.pos_of_ne_zero hk)
        hdim c ho' hv ξ hc a ha ?_ q
      apply retained_repeated_prime_supported_of_detection X k cX hperfect ξ cZ a hn hrepeat
      intro i
      exact retained_prime_forget_injective_of_intrinsic_ne_zero X k (Nat.pos_of_ne_zero hk)
        hdim (ξ i) (hc i) c ho' hv'
        (retained_projective_prime_image_ne_zero X k hdim (ξ i) (hc i))

example := RetainedCycleChecks.check_intrinsic_supported_additivity

variable {W W₀ : Over (Spec ↧ℂ)} [IsIntegral W.left] [IsIntegral W₀.left]
    [IsProjective W.hom] [IsProjective W₀.hom]
    (f : W ⟶ W₀) [IsProper f.left]

/-- Intrinsic integration under the actual prime map with residue degree
Source: Fulton, Intersection Theory, 19.1–19.2; Bredon, Sheaf Theory, second edition, V.9.
HC no distance; AV milestone no distance. -/
theorem intrinsic_degree_aux
    (k : ℕ) (hdimW : TopologicalSpace.dim W.left = 2*k)
    (hdimW₀ : TopologicalSpace.dim W₀.left = 2*k)
    (ξ : W.left) (hc : Order.coheight ξ = k)
    (hd : 0 < a1p_degree f.left ξ) :
    let hcη : Order.coheight (f.left ξ) = k :=
      (retained_positive_degree_coheight f (2*k) hdimW hdimW₀ ξ hd).trans hc
    ∀ u : Cohomology ℚ (a3b4_an W₀.hom) (2*k),
      orientationIntegral (a3b4_an (intrinsicComponent W ξ).hom) (2*k)
        (retainedIntrinsicFundamentalClass W k hdimW ξ hc)
        (s2e_pullback ℚ (intrinsicComponentInclusion W ξ) (2*k)
          (s2e_pullback ℚ f (2*k) u)) =
        (a1p_degree f.left ξ : ℚ) *
          orientationIntegral (a3b4_an (intrinsicComponent W₀ (f.left ξ)).hom) (2*k)
            (retainedIntrinsicFundamentalClass W₀ k hdimW₀ (f.left ξ) hcη)
            (s2e_pullback ℚ (intrinsicComponentInclusion W₀ (f.left ξ)) (2*k) u) := by
  exact retained_intrinsic_degree_integral f k hdimW hdimW₀ ξ hc hd

example := RetainedCycleChecks.check_retained_orbit_coefficients


end ConsumerSteps
end HodgeLean.Foundations.QuotientDuality
