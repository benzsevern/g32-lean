import HodgeLean.Foundations.Program.SchoenCycleAdicMapBijective

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- An algebra coordinate equivalence induces the canonical equivalence for its mapped adic ideal.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10. -/
def s2e_adic_equiv_map
    {k A B : Type*} [CommRing k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    (I : Ideal A) (f : A ≃ₐ[k] B) :
    AdicCompletion I A ≃ₐ[k] AdicCompletion (I.map f.toRingHom) B := by
  have hf : ∀ n a, a ∈ I ^ n → f a ∈ I.map f.toRingHom ^ n := by
    intro n a ha
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ ha
  apply AlgEquiv.ofBijective (s2e_adic_algebra_map I (I.map f.toRingHom) f.toAlgHom hf)
  apply s2e_adic_algebra_map_bijective
  intro n
  refine ⟨Ideal.quotientEquivAlg (I ^ n) (I.map f.toRingHom ^ n) f (Ideal.map_pow _ _ _).symm, ?_⟩
  intro a
  rfl

end HodgeLean.Foundations.Program
