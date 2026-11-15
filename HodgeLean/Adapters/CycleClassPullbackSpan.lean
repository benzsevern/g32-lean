import HodgeLean.Adapters.CycleClassPullbackSpanProofs

/-! # From supported prime pullback to the powers span

These statements give the implication from smooth pullback comparison to ordinary
cycle and span compatibility. The endpoint uses the existing abelian power data.
No multiplicativity statement is claimed. HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxRecDepth 2048
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped CategoryTheory.MonObj
open HodgeLean.RealDefs
namespace HodgeLean.Adapters

/-- Forgetting the weighted supported sum gives the constructed cycle class.
Source: Fulton, Intersection Theory, second edition, §19.1; forgetSupport_restrict. -/
theorem ccm6_forgetSupport_sum {X Z : Over (Spec ↧ℂ)}
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (f : X ⟶ Z) [Flat f.left] (q : ℕ) (x : Z.left)
    (hx : Order.coheight x = q) :
    ComplexPoint.forgetSupport ℚ X
      (ccm4_inverseAnalyticSupport f (cycleComponentAnalyticClosedSupport Z x)) (2 * q)
      (∑ᶠ z : {z : X.left // ccm3_flatPullbackPrime f.left x z ≠ 0},
        ccm3_flatPullbackPrime f.left x z.1 •
          supportEnlarge X (ccm4_flatPullbackPrime_support_le f x z.1 z.2) (2 * q)
            (cycleComponentSupportedInjectiveClass X z.1
              (ccm3_flatPullbackPrime_codimension f q x hx z.1 z.2))) =
      ccm3_cycleClass X q (ccm3_flatPullbackPrime f.left x) :=
  ccm6_forgetSupport_sum_aux f q x hx

/-- Ordinary smooth pullback agrees with the inverse-image prime cycle class.
Source: Voisin, Hodge Theory and Complex Algebraic Geometry I, §11; ccm4_supportedPullback_prime. -/
theorem ccm6_homPullback_prime {X Z : Over (Spec ↧ℂ)}
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (f : X ⟶ Z) [Smooth f.left] (q : ℕ) (x : Z.left)
    (hx : Order.coheight x = q) :
    homPullback f (2 * q) (cycleComponentSheafClass Z x hx) =
      ccm3_cycleClass X q (ccm3_flatPullbackPrime f.left x) :=
  ccm6_homPullback_prime_aux f q x hx

/-- Constructed cycle pullback respects rational scaling.
Source: Fulton, Intersection Theory, second edition, §1.7, linear extension. -/
theorem ccm6_flatPullback_smul {X Z : Over (Spec ↧ℂ)}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (f : X ⟶ Z) (a : ℚ) (c : AlgebraicCycle Z.left ℚ) :
    ccm3_flatPullback f.left (c.mapRange (a * ·) (mul_zero a)) =
      (ccm3_flatPullback f.left c).mapRange (a * ·) (mul_zero a) :=
  ccm6_flatPullback_smul_aux f a c

/-- The codimension part of the cycle-class realization is rational linear.
Source: Fulton, Intersection Theory, second edition, §19.1, linear extension. -/
theorem ccm6_cycleClass_linear (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (q : ℕ) (a : ℚ) (c d : AlgebraicCycle X.left ℚ) :
    ccm3_cycleClass X q (c + d) = ccm3_cycleClass X q c + ccm3_cycleClass X q d ∧
      ccm3_cycleClass X q (c.mapRange (a * ·) (mul_zero a)) = a • ccm3_cycleClass X q c :=
  ccm6_cycleClass_linear_aux X q a c d

/-- Smooth pullback comparison for a cycle pure of the specified codimension.
Source: Fulton, Intersection Theory, second edition, §1.7 and §19.1; Voisin, §11. -/
theorem ccm6_homPullback_cycleClass {X Z : Over (Spec ↧ℂ)}
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (f : X ⟶ Z) [Smooth f.left] (q : ℕ)
    (c : AlgebraicCycle Z.left ℚ)
    (hc : ∀ x : Z.left, c x ≠ 0 → Order.coheight x = q) :
    homPullback f (2 * q) (ccm3_cycleClass Z q c) =
      ccm3_cycleClass X q (ccm3_flatPullback f.left c) :=
  ccm6_homPullback_cycleClass_aux f q c hc

/-- Nonzero powers sum maps preserve the algebraic cycle-class span.
Source: ccm3_pwSumMap_smooth_of_ne_zero; Fulton, Intersection Theory, second edition, §19.1. -/
theorem ccm6_pwSumMap_span_of_ne_zero {A Y : Over (Spec ↧ℂ)} [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [GrpObj Y] [IsCommMonObj Y] [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    {L : Type*} [Field L] [Algebra ℚ L] {r : ℕ}
    (P : AbelianPowerData A Y r) (θ : L →ₐ[ℚ] AbelianEnd0 A) (a : Fin r → pwOrder A θ)
    (ha : a ≠ 0) (q : ℕ) :
    (algebraicCycleClassSpan A q).map (homPullback (P.pwSumMap θ a) (2 * q)) ≤
      algebraicCycleClassSpan Y q :=
  ccm6_pwSumMap_span_of_ne_zero_aux P θ a ha q

/-- The exact powers pullback premise, including the zero tuple.
Source: ccm2_hPull_of_zero_or_nonzero; PW v0.3, proof of Theorem 4.2. -/
theorem ccm6_hPull {A Y : Over (Spec ↧ℂ)} [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [GrpObj Y] [IsCommMonObj Y] [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    {L : Type*} [Field L] [Algebra ℚ L] {r : ℕ}
    (P : AbelianPowerData A Y r) (θ : L →ₐ[ℚ] AbelianEnd0 A) :
    ∀ (a : Fin r → pwOrder A θ) (q : ℕ),
      (algebraicCycleClassSpan A q).map (homPullback (P.pwSumMap θ a) (2 * q)) ≤
      algebraicCycleClassSpan Y q :=
  ccm6_hPull_aux P θ

end HodgeLean.Adapters
