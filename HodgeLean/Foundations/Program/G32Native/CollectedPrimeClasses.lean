import HodgeLean.Foundations.QuotientDuality.RetainedCycleConsumerSteps
import HodgeLean.Foundations.QuotientDuality.RetainedCycleForgetEnlargement

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open HodgeLean.Adapters HodgeLean.Foundations.Program
open HodgeLean.Foundations.QuotientDuality HodgeLean.Foundations.Analytic
open scoped BigOperators Classical
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program.G32Native

/-- The intrinsic prime suppliers and weighted realization retain normalization
and the exact absolute sum, including repeated primes and zero coefficients.
Source: Bredon, Sheaf Theory, second edition, V.9; Fulton, Intersection Theory, 19.1.
-/
theorem collected_prime_classes
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
    (hp : Function.Injective (properCyclePairing (a3b4_an X.hom) k cX))
    {I : Type} [Fintype I] (ξ : I → X.left) (hc : ∀ i, Order.coheight (ξ i) = k) :
    ∃ a : ∀ i, s2e_supportedClass X (properPrime (ξ i)) k,
      (∀ i, a3b4_IsCycleClass X.hom (properPrime (ξ i)) k (a i)) ∧
      (∀ i u, properCyclePairing (a3b4_an X.hom) k cX
        (s2e_classToAbsolute X (properPrime (ξ i)) k (a i)) u =
        orientationIntegral (a3b4_an (intrinsicComponent X (ξ i)).hom) (2*k)
          (retainedIntrinsicFundamentalClass X k hdim (ξ i) (hc i))
          (s2e_pullback ℚ (intrinsicComponentInclusion X (ξ i)) (2*k) u)) ∧
      ∀ q : I → ℚ,
        let Γ := ∑ i, (properPrime (ξ i)).mapRange (q i * ·) (mul_zero _)
        ∃ b : s2e_supportedClass X Γ k,
          a3b4_IsCycleClass X.hom Γ k b ∧
          s2e_classToAbsolute X Γ k b =
            ∑ i, q i • s2e_classToAbsolute X (properPrime (ξ i)) k (a i) := by
  have hex := fun i => ConsumerSteps.intrinsic_supported_class_aux X k hdim cX ho hv hn (ξ i) (hc i)
  choose a ha using fun i => (hex i).exists
  refine ⟨a, fun i => (ha i).1, fun i => (ha i).2, ?_⟩
  intro q
  obtain ⟨hΓ, hi, b, hb, hsum⟩ := ConsumerSteps.supported_weighted_realization_aux
    X k ξ hc cX hdim ho hv hp
    (fun i => retainedIntrinsicFundamentalClass X k hdim (ξ i) (hc i))
    a (fun i => (ha i).1) (fun i => (ha i).2) (by
      intro i j hij
      have he : ∀ (x y : X.left) (hx : Order.coheight x = k)
          (hy : Order.coheight y = k), x = y →
          HEq (retainedIntrinsicFundamentalClass X k hdim x hx)
            (retainedIntrinsicFundamentalClass X k hdim y hy) := by
        intro x y hx hy hxy
        subst y
        rfl
      exact he _ _ _ _ hij) q
  refine ⟨b, hb, ?_⟩
  exact retained_absolute_sum_of_common_support (a3b4_an X.hom)
    (fun i => a3b4_cycleSupport X.hom (properPrime (ξ i))) hΓ hi (2*k) b a q hsum

#print axioms collected_prime_classes
end HodgeLean.Foundations.Program.G32Native
