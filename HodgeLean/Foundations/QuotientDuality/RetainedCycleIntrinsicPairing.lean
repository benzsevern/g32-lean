import HodgeLean.Foundations.QuotientDuality.RetainedCycleDefs

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open HodgeLean.Adapters HodgeLean.Foundations.Program
open scoped BigOperators Classical
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
namespace HodgeLean.Foundations.QuotientDuality

/-- Intrinsic integration determines the absolute representative through an injective pairing. -/
theorem retained_intrinsic_absolute_unique
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (k : ℕ) (cX : Homology ℚ (a3b4_an X.hom) (2 * (2 * k)))
    (hp : Function.Injective (properCyclePairing (a3b4_an X.hom) k cX))
    (ξ : X.left)
    (cZ : Homology ℚ (a3b4_an (intrinsicComponent X ξ).hom) (2 * k))
    (a b : s2e_supportedClass X (properPrime ξ) k)
    (ha : ∀ u, properCyclePairing (a3b4_an X.hom) k cX
      (s2e_classToAbsolute X (properPrime ξ) k a) u =
      orientationIntegral (a3b4_an (intrinsicComponent X ξ).hom) (2 * k) cZ
        (s2e_pullback ℚ (intrinsicComponentInclusion X ξ) (2 * k) u))
    (hb : ∀ u, properCyclePairing (a3b4_an X.hom) k cX
      (s2e_classToAbsolute X (properPrime ξ) k b) u =
      orientationIntegral (a3b4_an (intrinsicComponent X ξ).hom) (2 * k) cZ
        (s2e_pullback ℚ (intrinsicComponentInclusion X ξ) (2 * k) u)) :
    s2e_classToAbsolute X (properPrime ξ) k a =
      s2e_classToAbsolute X (properPrime ξ) k b := by
  apply hp
  ext u
  exact (ha u).trans (hb u).symm

/-- Repeated primes with compatible intrinsic orientations have equal absolute representatives. -/
theorem retained_repeated_prime_absolute
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (k : ℕ) (cX : Homology ℚ (a3b4_an X.hom) (2 * (2 * k)))
    (hp : Function.Injective (properCyclePairing (a3b4_an X.hom) k cX))
    {I : Type} (ξ : I → X.left)
    (cZ : ∀ i, Homology ℚ (a3b4_an (intrinsicComponent X (ξ i)).hom) (2 * k))
    (a : ∀ i, s2e_supportedClass X (properPrime (ξ i)) k)
    (hn : ∀ i u, properCyclePairing (a3b4_an X.hom) k cX
      (s2e_classToAbsolute X (properPrime (ξ i)) k (a i)) u =
      orientationIntegral (a3b4_an (intrinsicComponent X (ξ i)).hom) (2 * k) (cZ i)
        (s2e_pullback ℚ (intrinsicComponentInclusion X (ξ i)) (2 * k) u))
    (hrepeat : ∀ i j, ξ i = ξ j → HEq (cZ i) (cZ j))
    (i j : I) (hij : ξ i = ξ j) :
    s2e_classToAbsolute X (properPrime (ξ i)) k (a i) =
      s2e_classToAbsolute X (properPrime (ξ j)) k (a j) := by
  apply hp
  ext u
  rw [hn i u, hn j u]
  have hf : ∀ (x y : X.left)
      (cx : Homology ℚ (a3b4_an (intrinsicComponent X x).hom) (2 * k))
      (cy : Homology ℚ (a3b4_an (intrinsicComponent X y).hom) (2 * k)),
      x = y → HEq cx cy →
      orientationIntegral (a3b4_an (intrinsicComponent X x).hom) (2 * k) cx
        (s2e_pullback ℚ (intrinsicComponentInclusion X x) (2 * k) u) =
      orientationIntegral (a3b4_an (intrinsicComponent X y).hom) (2 * k) cy
        (s2e_pullback ℚ (intrinsicComponentInclusion X y) (2 * k) u) := by
    intro x y cx cy hxy hcc
    subst y
    cases hcc
    rfl
  exact hf _ _ _ _ hij (hrepeat i j hij)

end HodgeLean.Foundations.QuotientDuality
