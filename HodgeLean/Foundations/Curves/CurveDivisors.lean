import HodgeLean.Foundations.Curves.CurveDivisorsProofs

/-! # Divisors, principal divisors, and degree on curves (FROZEN SPEC)

This file freezes the J1 interface for actual integral smooth projective scheme curves over `ℂ`.
It claims the standard consequences of that geometric scope: finite support of local orders,
principal-divisor arithmetic, and the explicit divisor of `x` on the fixed cubic. The product
formula (degree zero of principal divisors) moved to lane J1b; see the spec doc. Every result is an implication from the displayed curve instances and nonvanishing
hypotheses. It does not construct divisor classes, line bundles, Picard schemes, or Jacobians.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace HodgeLean.Foundations.Curves

variable {X : Over (Spec ↧ℂ)} [IsIntegral X.left]
  [SmoothOfRelativeDimension 1 X.hom] [IsProjective X.hom]
  [IsLocallyNoetherian X.left] [CompactSpace X.left]

/-- A divisor on a projective curve is a finite integral linear combination of coheight-one
points (and hence of closed points in this one-dimensional finite-type setting).
Source: Hartshorne, *Algebraic Geometry*, II.6; Mathlib
`Function.locallyFinsupp.finite_support`. -/
theorem divisor_support_finite (D : Divisor X.left) :
    (Function.support (D : X.left → ℤ)).Finite := divisor_support_finite_aux D

example (D : Divisor X.left) : (Function.support (D : X.left → ℤ)).Finite :=
  divisor_support_finite D

/-- Orders of a nonzero rational function on a smooth projective curve are nonzero at only
finitely many points.
Source: Hartshorne, *Algebraic Geometry*, II.6, Proposition 6.5. -/
theorem ord_support_finite (f : X.left.functionField) (hf : f ≠ 0) :
    (Function.support (ordAt X.left f)).Finite := ord_support_finite_aux f hf

example (f : X.left.functionField) (hf : f ≠ 0) :
    (Function.support (ordAt X.left f)).Finite := ord_support_finite f hf

/-- The coefficient of the principal divisor at `P` is the DVR order at `P`.
Source: Hartshorne, *Algebraic Geometry*, II.6, Definition 6.3. -/
theorem principalDivisor_apply (f : X.left.functionField) (hf : f ≠ 0) (P : X.left) :
    (principalDivisor X.left f).1 P = ordAt X.left f P := principalDivisor_apply_aux f hf P

example (f : X.left.functionField) (hf : f ≠ 0) (P : X.left) :
    (principalDivisor X.left f).1 P = ordAt X.left f P := principalDivisor_apply f hf P

/-- The divisor of a product of nonzero rational functions is the sum of their divisors.
Source: Hartshorne, *Algebraic Geometry*, II.6, Proposition 6.5. -/
theorem principalDivisor_mul (f g : X.left.functionField) (hf : f ≠ 0) (hg : g ≠ 0) :
    principalDivisor X.left (f * g) = principalDivisor X.left f + principalDivisor X.left g :=
  principalDivisor_mul_aux f g hf hg

example (f g : X.left.functionField) (hf : f ≠ 0) (hg : g ≠ 0) :
    principalDivisor X.left (f * g) = principalDivisor X.left f + principalDivisor X.left g :=
  principalDivisor_mul f g hf hg

/-- Every nonzero complex constant has zero principal divisor.
Source: Hartshorne, *Algebraic Geometry*, II.6, Proposition 6.5. -/
theorem principalDivisor_constant (c : ℂ) (hc : c ≠ 0) :
    principalDivisor X.left (constantFunction X c) = 0 :=
  principalDivisor_constant_aux c hc

example (c : ℂ) (hc : c ≠ 0) :
    principalDivisor X.left (constantFunction X c) = 0 :=
  principalDivisor_constant c hc

/-- Falsification witness: on `y²z = x³ + xz²`, the coordinate `x` has divisor
`2[(0,0)] - 2[∞]`, hence both zeros and poles and is nonconstant.
Source: Silverman, *The Arithmetic of Elliptic Curves*, III.1 and III.3. -/
theorem cubicX_principalDivisor :
    (principalDivisor E.left cubicX : AlgebraicCycle E.left ℤ) =
      2 • pointCycle E.left (finitePoint.base default) 1 -
        2 • pointCycle E.left (infinity.base default) 1 :=
  cubicX_principalDivisor_aux

example : (principalDivisor E.left cubicX : AlgebraicCycle E.left ℤ) =
    2 • pointCycle E.left (finitePoint.base default) 1 -
      2 • pointCycle E.left (infinity.base default) 1 :=
  cubicX_principalDivisor

end HodgeLean.Foundations.Curves
