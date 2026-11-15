import HodgeLean.Foundations.Program.SchoenCycleAdicMapFiniteJets
import HodgeLean.Foundations.Program.SchoenCycleAdicMapValues

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A zero formal approximation error pulls back to the specified actual finite-order coefficient error.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10. -/
theorem s2e_formal_pullback_jet_error
    {k A B : Type*} [CommRing k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    (I : Ideal A) (J : Ideal B) (f : A →ₐ[k] B)
    (h : ∀ n a, a ∈ I ^ n → f a ∈ J ^ n)
    (N : ℕ) (a : A) (z : AdicCompletion I A) (b : B)
    (hz : s2e_adic_algebra_map I J f h z = AdicCompletion.of J B b)
    (he : (AdicCompletion.of I A a - z).val N = 0) : f a - b ∈ J ^ N := by
  have hh := s2e_adic_algebra_map_zero_jet I J f h N _ he
  rw [map_sub, s2e_adic_algebra_map_of, hz] at hh
  change Ideal.Quotient.mk (J ^ N • ⊤ : Ideal B) (f a - b) = 0 at hh
  simpa only [smul_eq_mul, Ideal.mul_top, Ideal.Quotient.eq_zero_iff_mem] using hh

#print axioms s2e_formal_pullback_jet_error
end HodgeLean.Foundations.Program
