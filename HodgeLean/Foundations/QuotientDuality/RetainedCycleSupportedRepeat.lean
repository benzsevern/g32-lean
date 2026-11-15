import HodgeLean.Foundations.QuotientDuality.RetainedCycleIntrinsicPairing

/-! Detection of repeated supported classes through their actual absolute images. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open HodgeLean.Adapters HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

/-- Intrinsically compatible occurrences agree on their prime carrier whenever its forgetful map detects classes. -/
lemma retained_repeated_prime_supported_of_detection
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (k : ℕ) (cX : Homology ℚ (a3b4_an X.hom) (2*(2*k)))
    (hp : Function.Injective (properCyclePairing (a3b4_an X.hom) k cX))
    {I : Type} (ξ : I → X.left)
    (cZ : ∀ i, Homology ℚ (a3b4_an (intrinsicComponent X (ξ i)).hom) (2*k))
    (a : ∀ i, s2e_supportedClass X (properPrime (ξ i)) k)
    (hn : ∀ i u, properCyclePairing (a3b4_an X.hom) k cX
      (s2e_classToAbsolute X (properPrime (ξ i)) k (a i)) u =
      orientationIntegral (a3b4_an (intrinsicComponent X (ξ i)).hom) (2*k) (cZ i)
        (s2e_pullback ℚ (intrinsicComponentInclusion X (ξ i)) (2*k) u))
    (hrepeat : ∀ i j, ξ i = ξ j → HEq (cZ i) (cZ j))
    (hdet : ∀ i, Function.Injective (s2e_classToAbsolute X (properPrime (ξ i)) k)) :
    ∀ i j, ξ i = ξ j → HEq (a i) (a j) := by
  have hd : ∀ (x y : X.left) (e : x = y)
      (ax : s2e_supportedClass X (properPrime x) k)
      (ay : s2e_supportedClass X (properPrime y) k),
      Function.Injective (s2e_classToAbsolute X (properPrime x) k) →
      s2e_classToAbsolute X (properPrime x) k ax =
        s2e_classToAbsolute X (properPrime y) k ay → HEq ax ay := by
    intro x y e ax ay hinj hab
    subst y
    exact heq_of_eq (hinj hab)
  intro i j hij
  exact hd (ξ i) (ξ j) hij (a i) (a j) (hdet i)
    (retained_repeated_prime_absolute X k cX hp ξ cZ a hn hrepeat i j hij)

end HodgeLean.Foundations.QuotientDuality
