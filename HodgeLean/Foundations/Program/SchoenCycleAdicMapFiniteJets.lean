import HodgeLean.Foundations.Program.SchoenCycleAdicAlgebraMap

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- The canonical adic map preserves zero finite jets under the actual finite quotient algebra maps.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10. -/
theorem s2e_adic_algebra_map_zero_jet
    {k A B : Type*} [CommRing k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    (I : Ideal A) (J : Ideal B) (f : A →ₐ[k] B)
    (h : ∀ n a, a ∈ I ^ n → f a ∈ J ^ n)
    (N : ℕ) (x : AdicCompletion I A) (hx : x.val N = 0) :
    (s2e_adic_algebra_map I J f h x).val N = 0 := by
  change Ideal.quotientMapₐ (J ^ N • ⊤ : Ideal B) f _ (x.val N) = 0
  rw [hx, map_zero]

#print axioms s2e_adic_algebra_map_zero_jet
end HodgeLean.Foundations.Program
