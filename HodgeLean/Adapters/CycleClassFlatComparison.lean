import HodgeLean.Adapters.CycleClassFlatComparisonProofs

/-! # Supported-class comparison for smooth flat pullback

The first statement compares the independently constructed supported pullback with
ordinary singular pullback after support is forgotten. The prime-class formula
is an implication from smoothness of the morphism to a generic-length-weighted
equality in supported cohomology. HC no distance;
AV milestone no distance.
-/

noncomputable section

set_option maxRecDepth 2048
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open TopologicalSpace
open HodgeLean.RealDefs

namespace HodgeLean.Adapters

/-- Forgetting support intertwines supported pullback with ordinary pullback.
Source: Voisin, *Hodge Theory and Complex Algebraic Geometry I*, §11. -/
theorem ccm4_forgetSupport_supportedPullback {X Z : Over (Spec ↧ℂ)}
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (f : X ⟶ Z) (S : Closeds (ComplexPoint Z)) (n : ℕ) (u :
      TopCat.Sheaf.supportH (TopCat.of (ComplexPoint Z)) S
        ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint Z))).obj
          (AddCommGrpCat.of ℚ)) n) :
    ComplexPoint.forgetSupport ℚ X (ccm4_inverseAnalyticSupport f S) n
        (ccm4_supportedPullback f S n u) =
      homPullback f n (ComplexPoint.forgetSupport ℚ Z S n u) :=
  ccm4_forgetSupport_supportedPullback_aux f S n u

/-- Every component occurring in the constructed inverse-image cycle lies in the
analytic inverse image of the original component support.
Source: Fulton, *Intersection Theory*, second edition, §1.7. -/
theorem ccm4_flatPullbackPrime_support_le {X Z : Over (Spec ↧ℂ)}
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (f : X ⟶ Z) [Flat f.left] (x : Z.left) (z : X.left)
    (hz : ccm3_flatPullbackPrime f.left x z ≠ 0) :
    cycleComponentAnalyticClosedSupport X z ≤
      ccm4_inverseAnalyticSupport f (cycleComponentAnalyticClosedSupport Z x) :=
  ccm4_flatPullbackPrime_support_le_aux f x z hz

/-- Smooth pullback of a normalized supported prime class is the sum of the
inverse-image component classes, weighted by their generic lengths. The coefficients
are those of `ccm3_flatPullbackPrime`, identified by `ccm3_flatPullbackPrime_coeff`.
Source: Fulton, *Intersection Theory*, second edition, §1.7 and §19.1;
Voisin, *Hodge Theory and Complex Algebraic Geometry I*, §11, smooth pullback of cycle classes. -/
theorem ccm4_supportedPullback_prime {X Z : Over (Spec ↧ℂ)}
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (f : X ⟶ Z) [Smooth f.left] (q : ℕ) (x : Z.left)
    (hx : Order.coheight x = q) :
    ccm4_supportedPullback f (cycleComponentAnalyticClosedSupport Z x) (2 * q)
        (cycleComponentSupportedInjectiveClass Z x hx) =
      ∑ᶠ z : {z : X.left // ccm3_flatPullbackPrime f.left x z ≠ 0},
        ccm3_flatPullbackPrime f.left x z.1 •
          supportEnlarge X (ccm4_flatPullbackPrime_support_le f x z.1 z.2) (2 * q)
            (cycleComponentSupportedInjectiveClass X z.1
              (ccm3_flatPullbackPrime_codimension f q x hx z.1 z.2)) :=
  ccm4_supportedPullback_prime_aux f q x hx

end HodgeLean.Adapters
