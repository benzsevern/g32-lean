import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.Polynomial.Eval.Defs

/-! # The coefficient-preserving isomorphism of a supplied Rees chart -/
noncomputable section
set_option maxHeartbeats 200000
open Polynomial
namespace HodgeLean.Foundations.Program.G32Native

/-- The exact kernel and surjectivity in the selected Rees chart export
construct its quotient-ring isomorphism.
Source: Hartshorne, Algebraic Geometry, II.7.13. -/
def pairedC3ReesEquationEquiv
    {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (u v : A) (s : B)
    (hsurj : Function.Surjective (eval₂RingHom f s))
    (hker : RingHom.ker (eval₂RingHom f s) = Ideal.span {C u - X * C v}) :
    (A[X] ⧸ Ideal.span {C u - X * C v}) ≃+* B :=
  (Ideal.quotEquivOfEq hker.symm).trans
    ((eval₂RingHom f s).quotientKerEquivOfSurjective hsurj)

/-- Original coefficients are retained by the supplied-chart isomorphism.
Source: Hartshorne, Algebraic Geometry, II.7.13. -/
theorem paired_c3_rees_equation_constants
    {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (u v : A) (s : B)
    (hsurj : Function.Surjective (eval₂RingHom f s))
    (hker : RingHom.ker (eval₂RingHom f s) = Ideal.span {C u - X * C v}) (a : A) :
    pairedC3ReesEquationEquiv f u v s hsurj hker
      (Ideal.Quotient.mk _ (C a)) = f a := by
  change eval₂ f s (C a) = f a
  exact eval₂_C _ _

/-- The original Rees ratio is retained by the supplied-chart isomorphism.
Source: Hartshorne, Algebraic Geometry, II.7.13. -/
theorem paired_c3_rees_equation_ratio
    {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (u v : A) (s : B)
    (hsurj : Function.Surjective (eval₂RingHom f s))
    (hker : RingHom.ker (eval₂RingHom f s) = Ideal.span {C u - X * C v}) :
    pairedC3ReesEquationEquiv f u v s hsurj hker
      (Ideal.Quotient.mk _ X) = s := by
  change eval₂ f s X = s
  exact eval₂_X _ _

#print axioms pairedC3ReesEquationEquiv
#print axioms paired_c3_rees_equation_constants
#print axioms paired_c3_rees_equation_ratio
end HodgeLean.Foundations.Program.G32Native
