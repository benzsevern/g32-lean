import HodgeLean.Foundations.Program.SchoenCycleAdicMapValues
import Mathlib.RingTheory.AdicCompletion.RingHom

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A filtration-preserving actual algebra map extends from its source adic algebra to an adic target algebra.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10. -/
def s2e_adic_algebra_lift
    {k A B : Type*} [CommRing k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    (I : Ideal A) (J : Ideal B) [IsAdicComplete J B] (f : A →ₐ[k] B)
    (h : ∀ n : ℕ, ∀ a ∈ I ^ n, f a ∈ J ^ n) :
    AdicCompletion I A →ₐ[k] B :=
  ((AdicCompletion.ofAlgEquiv J).symm.restrictScalars k).toAlgHom.comp
    (s2e_adic_algebra_map I J f h)

#print axioms s2e_adic_algebra_lift

/-- The actual adic extension retains the original value of every original algebra element.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10. -/
theorem s2e_adic_algebra_lift_of
    {k A B : Type*} [CommRing k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    (I : Ideal A) (J : Ideal B) [IsAdicComplete J B] (f : A →ₐ[k] B)
    (h : ∀ n : ℕ, ∀ a ∈ I ^ n, f a ∈ J ^ n) (a : A) :
    s2e_adic_algebra_lift I J f h (AdicCompletion.of I A a) = f a := by
  change (AdicCompletion.ofAlgEquiv J).symm
    (s2e_adic_algebra_map I J f h (AdicCompletion.of I A a)) = f a
  rw [s2e_adic_algebra_map_of, AdicCompletion.ofAlgEquiv_symm_of]

#print axioms s2e_adic_algebra_lift_of
end HodgeLean.Foundations.Program
