import HodgeLean.Foundations.Curves.CurveDivisorClassesProofs

/-! # Divisor classes on curves and the Abel map on the cubic (FROZEN SPEC)

This file freezes the J2 divisor-class interface. It claims the following:
* On an integral smooth projective curve over `ℂ`, principal divisors have degree zero, so the
  degree descends to `Cl(X)`. A divisor has a class in `Cl⁰(X)` exactly when its degree is zero.
  Both are implications from the displayed curve instances.
* On the fixed cubic `E`, closed points give prime divisors, and the Abel map `P ↦ [P] - [∞]` lands
  in `Cl⁰(E)`.
* The Abel map agrees with Mathlib's `Point.toClass` in the sense that the two identify the same
  points of Mathlib's Weierstrass group, and it is additive for Mathlib's group law.
* The class `[(0,0)] - [∞]` is nonzero and has order dividing two.

It does not claim the following: line bundles or invertible sheaves, an isomorphism between
`Cl(E)` and the class group of the affine coordinate ring, surjectivity of the Abel map onto
`Cl⁰(E)`, coherent cohomology, Riemann–Roch, a Picard scheme, a Jacobian, or genus one (the de Rham and
Hodge-filtration dimension statements moved to a later analytic lane; see the spec doc). `Cl(X)` here is the
Weil-divisor class group of the curve, never the Picard group of its ring of global functions.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace HodgeLean.Foundations.Curves

/-- Principal divisors on a smooth projective curve have degree zero, so the degree descends to
divisor classes through `divisorClassDegree`. This is implied by the J1 product formula
`degree_principalDivisor`.
Source: Hartshorne, *Algebraic Geometry*, II.6, Corollary 6.10. -/
theorem principalDivisors_le_ker_degree (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [SmoothOfRelativeDimension 1 X.hom] [IsProjective X.hom]
    [IsLocallyNoetherian X.left] [CompactSpace X.left] :
    principalDivisors X.left ≤ (divisorDegree X).ker :=
  principalDivisors_le_ker_degree_aux X

example : principalDivisors E.left ≤ (divisorDegree E).ker :=
  principalDivisors_le_ker_degree E

/-- `Cl⁰(X)` is the kernel of the degree on classes: a divisor's class has degree zero exactly when
the divisor does.
Source: Hartshorne, *Algebraic Geometry*, II.6, Corollary 6.10 and Example 6.10.2. -/
theorem mk_mem_divisorClassZero_iff (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [SmoothOfRelativeDimension 1 X.hom] [IsProjective X.hom]
    [IsLocallyNoetherian X.left] [CompactSpace X.left] (D : Divisor X.left) :
    DivisorClass.mk X.left D ∈ DivisorClassZero X ↔ divisorDegree X D = 0 :=
  mk_mem_divisorClassZero_iff_aux X D

example (D : Divisor E.left) :
    DivisorClass.mk E.left D ∈ DivisorClassZero E ↔ divisorDegree E D = 0 :=
  mk_mem_divisorClassZero_iff E D

/-- On a curve, a closed point has coheight one, so its prime divisor is the unit point cycle.
Source: Hartshorne, *Algebraic Geometry*, II.6 (prime divisors of a curve are its closed points)
and II, Exercise 3.20. -/
theorem pointDivisor_of_isClosed (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [SmoothOfRelativeDimension 1 X.hom] [IsProjective X.hom]
    (P : X.left) (hP : IsClosed ({P} : Set X.left)) :
    (pointDivisor X.left P : AlgebraicCycle X.left ℤ) = pointCycle X.left P 1 :=
  pointDivisor_of_isClosed_aux X P hP

example (P : E.left) (hP : IsClosed ({P} : Set E.left)) :
    (pointDivisor E.left P : AlgebraicCycle E.left ℤ) = pointCycle E.left P 1 :=
  pointDivisor_of_isClosed E P hP

/-- Every point of Mathlib's Weierstrass group goes to a closed point of `E`.
Source: Silverman, *The Arithmetic of Elliptic Curves*, III.1 and III.2. -/
theorem cubicPointOf_isClosed (P : W.toAffine.Point) :
    IsClosed ({cubicPointOf P} : Set E.left) :=
  cubicPointOf_isClosed_aux P

example : IsClosed ({cubicInfinity} : Set E.left) := cubicPointOf_isClosed 0

/-- The affine origin `(0,0)` of Mathlib's group goes to the named point `finitePoint` of `E`.
Source: Silverman, *The Arithmetic of Elliptic Curves*, III.1, the point `[0:0:1]`. -/
theorem cubicPointOf_origin :
    cubicPointOf (.some 0 0 W_nonsingular_origin) = finitePoint.base default :=
  cubicPointOf_origin_aux

example : cubicPointOf (.some 0 0 W_nonsingular_origin) = finitePoint.base default :=
  cubicPointOf_origin

/-- The Abel map sends closed points of the cubic to degree-zero classes.
Source: Silverman, *The Arithmetic of Elliptic Curves*, III.3.4. -/
theorem cubicAbelMap_mem_divisorClassZero (P : E.left) (hP : IsClosed ({P} : Set E.left)) :
    cubicAbelMap P ∈ DivisorClassZero E :=
  cubicAbelMap_mem_divisorClassZero_aux P hP

example (P : W.toAffine.Point) : cubicAbelMap (cubicPointOf P) ∈ DivisorClassZero E :=
  cubicAbelMap_mem_divisorClassZero _ (cubicPointOf_isClosed P)

/-- Bridge to Mathlib: on points of Mathlib's Weierstrass group, the Abel map into `Cl(E)`
identifies two points exactly when `Point.toClass` into the class group of the affine coordinate
ring does.
Source: Silverman, *The Arithmetic of Elliptic Curves*, III.3.4; Mathlib
`WeierstrassCurve.Affine.Point.toClass_injective`. -/
theorem cubicAbelMap_eq_iff_toClass_eq (P Q : W.toAffine.Point) :
    cubicAbelMap (cubicPointOf P) = cubicAbelMap (cubicPointOf Q) ↔
      WeierstrassCurve.Affine.Point.toClass P = WeierstrassCurve.Affine.Point.toClass Q :=
  cubicAbelMap_eq_iff_toClass_eq_aux P Q

example (P : W.toAffine.Point) :
    cubicAbelMap (cubicPointOf P) = cubicAbelMap (cubicPointOf P) ↔
      WeierstrassCurve.Affine.Point.toClass P = WeierstrassCurve.Affine.Point.toClass P :=
  cubicAbelMap_eq_iff_toClass_eq P P

/-- The Abel map is additive for Mathlib's group law: `[P + Q] - [∞] ~ ([P] - [∞]) + ([Q] - [∞])`.
Source: Silverman, *The Arithmetic of Elliptic Curves*, III.3.4(e). -/
theorem cubicAbelMap_add (P Q : W.toAffine.Point) :
    cubicAbelMap (cubicPointOf (P + Q)) =
      cubicAbelMap (cubicPointOf P) + cubicAbelMap (cubicPointOf Q) :=
  cubicAbelMap_add_aux P Q

example (P : W.toAffine.Point) :
    cubicAbelMap (cubicPointOf (P + 0)) =
      cubicAbelMap (cubicPointOf P) + cubicAbelMap (cubicPointOf 0) :=
  cubicAbelMap_add P 0

/-- Falsification witness: `[(0,0)] - [∞]` is a nonzero class. A degenerate quotient that kills
all degree-zero divisors would fail this.
Source: Silverman, *The Arithmetic of Elliptic Curves*, III.3.4 and III.3.5. -/
theorem cubicAbelMap_finitePoint_ne_zero : cubicAbelMap (finitePoint.base default) ≠ 0 :=
  cubicAbelMap_finitePoint_ne_zero_aux

example : cubicAbelMap (finitePoint.base default) ≠ 0 := cubicAbelMap_finitePoint_ne_zero

/-- Falsification witness: `2([(0,0)] - [∞]) = 0`, coming from the J1 divisor
`div(x) = 2[(0,0)] - 2[∞]` (`cubicX_principalDivisor`).
Source: Silverman, *The Arithmetic of Elliptic Curves*, III.1 and III.3. -/
theorem two_smul_cubicAbelMap_finitePoint : 2 • cubicAbelMap (finitePoint.base default) = 0 :=
  two_smul_cubicAbelMap_finitePoint_aux

example : 2 • cubicAbelMap (finitePoint.base default) = 0 := two_smul_cubicAbelMap_finitePoint

end HodgeLean.Foundations.Curves
