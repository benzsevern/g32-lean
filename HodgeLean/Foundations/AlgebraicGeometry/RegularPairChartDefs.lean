import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.Regular.Flat

noncomputable section

namespace AlgebraicGeometry.RegularPairChart
open Polynomial

/-- The binomial quotient chart, with its original quotient presentation.
Source: Hartshorne, Algebraic Geometry, II.7, affine charts of a blowup. -/
abbrev ring {R : Type*} [CommRing R] (u v : R) :=
  R[X] ⧸ Ideal.span {C u - X * C v}

/-- The coefficient homomorphism into the binomial quotient.
Source: Hartshorne, Algebraic Geometry, II.7, affine charts of a blowup. -/
abbrev coeff {R : Type*} [CommRing R] (u v : R) : R →+* ring u v :=
  (Ideal.Quotient.mk (Ideal.span {C u - X * C v})).comp C

/-- The distinguished ratio in the binomial quotient.
Source: Hartshorne, Algebraic Geometry, II.7, affine charts of a blowup. -/
abbrev ratio {R : Type*} [CommRing R] (u v : R) : ring u v :=
  Ideal.Quotient.mk (Ideal.span {C u - X * C v}) X

example {R : Type*} [CommRing R] (u v : R) :
    ring u v = (R[X] ⧸ Ideal.span {C u - X * C v}) := rfl

example {R : Type*} [CommRing R] (u v : R) :
    coeff u v = (Ideal.Quotient.mk (Ideal.span {C u - X * C v})).comp C := rfl

example {R : Type*} [CommRing R] (u v : R) :
    ratio u v = Ideal.Quotient.mk (Ideal.span {C u - X * C v}) X := rfl

end AlgebraicGeometry.RegularPairChart
