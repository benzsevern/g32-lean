import HodgeLean.Foundations.Program.SchoenCycleAdicCofinalEquiv

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- The canonical cofinal-ideal comparison intertwines filtered actions on all formal sections.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10. -/
theorem s2e_adic_cofinal_equiv_intertwines
    {k A : Type*} [CommRing k] [CommRing A] [Algebra k A]
    (I J : Ideal A) (hJI : J ≤ I) (c : ℕ) (hc : 1 ≤ c) (hIJ : I ^ c ≤ J)
    (f : A →ₐ[k] A)
    (hI : ∀ n a, a ∈ I ^ n → f a ∈ I ^ n)
    (hJ : ∀ n a, a ∈ J ^ n → f a ∈ J ^ n)
    (x : AdicCompletion I A) :
    s2e_adic_algebra_map J J f hJ (s2e_adic_cofinal_equiv (k := k) I J hJI c hc hIJ x) =
      s2e_adic_cofinal_equiv (k := k) I J hJI c hc hIJ (s2e_adic_algebra_map I I f hI x) := by
  apply AdicCompletion.ext
  intro n
  change Ideal.quotientMapₐ (J ^ n • ⊤ : Ideal A) f _
      (Ideal.quotientMapₐ (J ^ n • ⊤ : Ideal A) (AlgHom.id k A) _ (x.val (c * n))) =
    Ideal.quotientMapₐ (J ^ n • ⊤ : Ideal A) (AlgHom.id k A) _
      (Ideal.quotientMapₐ (I ^ (c * n) • ⊤ : Ideal A) f _ (x.val (c * n)))
  refine Quotient.inductionOn' (x.val (c * n)) (fun a => ?_)
  rfl

end HodgeLean.Foundations.Program
