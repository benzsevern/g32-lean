import HodgeLean.Foundations.Program.SchoenCycleAdicAlgebraMap

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- The actual adic algebra map sends every original ring element to the formal value of its original algebra image.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10. -/
theorem s2e_adic_algebra_map_of
    {k A B : Type*} [CommRing k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    (I : Ideal A) (J : Ideal B) (f : A →ₐ[k] B)
    (h : ∀ n a, a ∈ I ^ n → f a ∈ J ^ n) (a : A) :
    s2e_adic_algebra_map I J f h (AdicCompletion.of I A a) =
      AdicCompletion.of J B (f a) := by
  apply AdicCompletion.ext
  intro n
  rfl

#print axioms s2e_adic_algebra_map_of
end HodgeLean.Foundations.Program
