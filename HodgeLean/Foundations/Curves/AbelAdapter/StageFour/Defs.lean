import HodgeLean.Foundations.Curves.AbelAdapter.Defs
import HodgeLean.Foundations.Curves.Picard.Defs
import Mathlib.Algebra.BigOperators.Finsupp.Basic

/-! # Divisor sums for principal descent

The free integral sums retain the existing Weil-divisor and class quotients.
HC no distance; AV milestone no distance.
-/
noncomputable section
open CategoryTheory AlgebraicGeometry
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Curves.AbelAdapter.StageFour

/-- Integral extension of a specified point map.
Source: Birkenhake–Lange, Complex Abelian Varieties, §11.4.
HC no distance; AV milestone no distance. -/
def weightedSum {S M : Type*} [AddCommGroup M] (f : S → M) :
    (S →₀ ℤ) →+ M := (Finsupp.linearCombination ℤ f).toAddMonoidHom

example : weightedSum (fun n : ℤ ↦ n) (Finsupp.single (3 : ℤ) (2 : ℤ)) = (6 : ℤ) := by
  simp [weightedSum, Finsupp.linearCombination_single]

/-- The integral degree on actual complex-point sums.
Source: Hartshorne, Algebraic Geometry, II.6, Corollary 6.10.
HC no distance; AV milestone no distance. -/
def pointDegree (X : Over (Spec ↧ℂ)) : (ComplexPoint X →₀ ℤ) →+ ℤ :=
  weightedSum (fun _ ↦ (1 : ℤ))

example (X : Over (Spec ↧ℂ)) (p q : ComplexPoint X) :
    pointDegree X (Finsupp.single p (1 : ℤ) - Finsupp.single q (1 : ℤ)) = 0 := by
  simp [pointDegree, weightedSum, Finsupp.linearCombination_single]

/-- The literal Weil divisor of a finite integral sum of complex points.
Source: Hartshorne, Algebraic Geometry, II.6, prime divisors of curves.
HC no distance; AV milestone no distance. -/
def divisorSum (X : Over (Spec ↧ℂ)) : (ComplexPoint X →₀ ℤ) →+ Divisor X.left :=
  weightedSum (fun p ↦ pointDivisor X.left (p.left (IsLocalRing.closedPoint ℂ)))

example (X : Over (Spec ↧ℂ)) (p : ComplexPoint X) :
    divisorSum X (Finsupp.single p (2 : ℤ)) =
      (2 : ℤ) • pointDivisor X.left (p.left (IsLocalRing.closedPoint ℂ)) := by
  simp [divisorSum, weightedSum, Finsupp.linearCombination_single]

/-- The class sum in the retained Weil-divisor quotient.
Source: Hartshorne, Algebraic Geometry, II.6, Definition before Proposition 6.2.
HC no distance; AV milestone no distance. -/
def classSum (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [IsLocallyNoetherian X.left] : (ComplexPoint X →₀ ℤ) →+ DivisorClass X.left :=
  (DivisorClass.mk X.left).comp (divisorSum X)

example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsLocallyNoetherian X.left]
    (p : ComplexPoint X) : classSum X (Finsupp.single p (2 : ℤ)) =
      (2 : ℤ) • DivisorClass.mk X.left
        (pointDivisor X.left (p.left (IsLocalRing.closedPoint ℂ))) := by
  simp [classSum, divisorSum, weightedSum, Finsupp.linearCombination_single]

end HodgeLean.Foundations.Curves.AbelAdapter.StageFour
