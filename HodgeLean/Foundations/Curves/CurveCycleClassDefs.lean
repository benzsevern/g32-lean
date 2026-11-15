import HodgeLean.Foundations.Curves.CurveDivisorClasses
import HodgeLean.RealDefs.Operations

/-! # Definitions for the divisor cycle-class map (FROZEN)

The cycle class of a Weil divisor in `HQ X 2 = H²(X(ℂ); ℚ)`: a prime divisor with generic point
`P` (a point of coheight one) goes to upstream's `cycleComponentSheafClass X P`, and the map is
extended additively over the finitely many points in the support of a divisor. Given that
principal divisors go to zero, it descends to the divisor class group.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.RealDefs

namespace HodgeLean.Foundations.Curves

/-- The cycle class of the prime divisor with generic point `P`: upstream's
`cycleComponentSheafClass X P` when `P` has coheight one, and `0` otherwise. The fallback branch
makes this unconditional; `divisorCycleClass_pointDivisor` in the frozen spec identifies the
class of `pointDivisor X.left P` with `cycleComponentSheafClass` at coheight one.
Source: Fulton, *Intersection Theory*, 2nd ed., §19.1 (the cycle map); HodgeConjecture
`AlgebraicGeometry.ComplexPoint.cycleComponentSheafClass` (`Cycle/FundamentalClass.lean`). -/
def primeDivisorClass (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (P : X.left) : HQ X 2 := by
  classical
  exact if h : Order.coheight P = 1 then
    cycleComponentSheafClass X P (p := 1) (h.trans Nat.cast_one.symm) else 0

example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (P : X.left) (h : ¬ Order.coheight P = 1) : primeDivisorClass X P = 0 := by
  simp [primeDivisorClass, h]

/-- The divisor cycle-class map `Div(X) → H²(X(ℂ); ℚ)`, `D ↦ ∑_P D(P) · [P]`, where `[P]` is
`primeDivisorClass X P`. A divisor on a quasi-compact scheme has finite support, so the sum is
finite and the map is additive.
Source: Fulton, *Intersection Theory*, 2nd ed., §19.1 (the cycle map on `Z^1(X)`); Mathlib
`AlgebraicGeometry.AlgebraicCycle.degree` (the same finite-sum pattern). -/
def divisorCycleClass (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] [CompactSpace X.left] : Divisor X.left →+ HQ X 2 where
  toFun D := ∑ᶠ P, (D : AlgebraicCycle X.left ℤ) P • primeDivisorClass X P
  map_zero' := by simp
  map_add' D D' := by
    simp only [AddSubgroup.coe_add, Function.locallyFinsuppWithin.coe_add, Pi.add_apply,
      add_smul]
    exact finsum_add_distrib
      ((D : AlgebraicCycle X.left ℤ).finite_support.subset fun x hx h ↦ hx (by simp [h]))
      ((D' : AlgebraicCycle X.left ℤ).finite_support.subset fun x hx h ↦ hx (by simp [h]))

example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [CompactSpace X.left] : divisorCycleClass X 0 = 0 :=
  map_zero _

/-- The cycle-class map on divisor classes, given that principal divisors have class zero. The
hypothesis is an explicit argument; `principalDivisors_le_ker_divisorCycleClass` in the frozen
spec supplies it on a smooth projective curve, as an implication from
`ComplexPointsPreconnected`.
Source: Fulton, *Intersection Theory*, 2nd ed., Corollary 19.2 (the cycle map factors through
rational equivalence); Mathlib `QuotientAddGroup.lift`. -/
def divisorClassCycleClass (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] [IsLocallyNoetherian X.left] [CompactSpace X.left]
    (h : principalDivisors X.left ≤ (divisorCycleClass X).ker) :
    DivisorClass X.left →+ HQ X 2 :=
  QuotientAddGroup.lift (principalDivisors X.left) (divisorCycleClass X) h

example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsLocallyNoetherian X.left] [CompactSpace X.left]
    (h : principalDivisors X.left ≤ (divisorCycleClass X).ker) (D : Divisor X.left) :
    divisorClassCycleClass X h (DivisorClass.mk X.left D) = divisorCycleClass X D :=
  rfl

end HodgeLean.Foundations.Curves
