import HodgeLean.Foundations.QuotientDuality.RetainedCycleSupportedVectorExistence
import HodgeLean.Foundations.QuotientDuality.RetainedCyclePrimeCoordinateExistence
import HodgeLean.Foundations.QuotientDuality.RetainedCyclePrimeCapInjection
import HodgeLean.Foundations.QuotientDuality.RetainedCycleIntrinsicCapCriterion
import HodgeLean.Foundations.QuotientDuality.ProperCycleCoordinatesNormalized
import HodgeLean.Foundations.QuotientDuality.RetainedCycleOrientationCast

/-! # Intrinsic supported normalization detected by the actual ambient prime image -/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open HodgeLean.Adapters HodgeLean.Foundations.Program HodgeLean.Foundations.Analytic
open scoped BigOperators
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.QuotientDuality

/-- A nonzero intrinsic ambient image gives the original supported prime with its specified integration normalization. -/
theorem retained_intrinsic_supported_of_nonzero_image
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (k : ℕ) (hk : 0 < k) (hdim : TopologicalSpace.dim X.left = 2*k)
    (cX : Homology ℚ (a3b4_an X.hom) (2*(2*k)))
    (ho : ∀ x, Function.Bijective (orientationLine (a3b4_an X.hom) (2*(2*k)) cX x))
    (hv : ∀ j : ℕ, j ≠ 2*(2*k) → ∀ x : a3b4_an X.hom,
      Subsingleton (orientationGroup (a3b4_an X.hom) j x))
    (hn : ∀ (E : OpenPartialHomeomorph (ComplexPoint X) (Fin (2*k) → ℂ)),
      (∀ j, (f4_analytification X).IsHolFun (fun u : E.source => E u j)) →
      ∀ x (hx : x ∈ E.source), localOrientation (a3b4_an X.hom) (2*(2*k)) cX x =
        localClassOfChart (2*k) E x hx)
    (ξ : X.left) (hc : Order.coheight ξ = k)
    (himage : properCycle_intrinsic_component X k ξ ≠ 0) :
    ∃! a : s2e_supportedClass X (properPrime ξ) k,
      a3b4_IsCycleClass X.hom (properPrime ξ) k a ∧
      ∀ u : Cohomology ℚ (a3b4_an X.hom) (2*k),
        properCyclePairing (a3b4_an X.hom) k cX
          (s2e_classToAbsolute X (properPrime ξ) k a) u =
        orientationIntegral (a3b4_an (intrinsicComponent X ξ).hom) (2*k)
          (retainedIntrinsicFundamentalClass X k hdim ξ hc)
          (s2e_pullback ℚ (intrinsicComponentInclusion X ξ) (2*k) u) := by
  classical
  have hp (y : X.left) (hy : y ∈ (properPrime ξ).support) : y = ξ := by
    by_contra h
    exact hy (by simp [properPrime, h])
  let hc' : ∀ y ∈ (properPrime ξ).support, Order.coheight y = k :=
    fun y hy => by rw [hp y hy]; exact hc
  let hdeg : 2*(2*k) = 2*k+2*k := by omega
  let c := (eqToIso (congrArg (fun j => Homology ℚ (a3b4_an X.hom) j) hdeg)).hom.hom cX
  have ho' := retained_orientation_line_bijective_cast (a3b4_an X.hom) _ _ hdeg cX ho
  have hv' : ∀ j : ℕ, j ≠ 2*k+2*k → ∀ x : a3b4_an X.hom,
      Subsingleton (orientationGroup (a3b4_an X.hom) j x) := by
    intro j hj
    exact hv j (by omega)
  let z := properCycle_intrinsic_support_sum X k hdim (properPrime ξ) hc'
    (fun y => properPrime ξ y.val)
  have hz : homologyMap ℚ (2*k) (TopPair.ofSubset (X := a3b4_an X.hom)
      (a3b4_cycleSupport X.hom (properPrime ξ))).map z ≠ 0 := by
    dsimp only [z]
    rw [properCycle_intrinsic_support_sum_inclusion, properCycle_extend_literal_coordinates]
    rw [finsum_eq_single _ ξ (by intro y hy; simp [properPrime, hy])]
    simpa [properPrime] using himage
  obtain ⟨a0, ha0⟩ := retained_supported_vector_of_nonzero_ambient_image
    X k hk hdim (properPrime ξ) hc' c ho' hv' z hz
  obtain ⟨a, ha⟩ := retained_prime_cap_coordinates_surjective_of_nonzero
    X k hk hdim ξ hc' c ho' hv' a0 ha0 (fun y => properPrime ξ y.val)
  have hnorm := properCycle_coordinates_normalized X k hk hdim cX hv hn
    (properPrime ξ) hc' a ha
  have hcap := retained_prime_cap_image_of_literal_coordinates X k hk hdim ξ hc' c a ha
  have hm (b : s2e_supportedClass X (properPrime ξ) k) :
      capCohomologyLinear ℚ (a3b4_an X.hom) (2*k) (2*k)
        ((cochainCohomologyEquiv ℚ (a3b4_an X.hom) (2*k)).symm
          (s2e_classToAbsolute X (properPrime ξ) k b)) c =
      retainedMiddleCapWithOrientation (a3b4_an X.hom) k cX
        (s2e_classToAbsolute X (properPrime ξ) k b) := by
    dsimp only [c]
    rw [retained_homology_degree_iso_apply]
    rfl
  rw [hm a] at hcap
  have hint := (retained_intrinsic_integral_iff_cap_image X k hdim cX ξ hc a).mpr hcap
  refine ⟨a, ⟨hnorm, hint⟩, ?_⟩
  intro b hb
  apply retained_prime_absolute_cap_injective X k hk hdim ξ hc' c ho' hv' himage
  dsimp only
  rw [hm b, hm a]
  exact ((retained_intrinsic_integral_iff_cap_image X k hdim cX ξ hc b).mp hb.2).trans hcap.symm

end HodgeLean.Foundations.QuotientDuality
