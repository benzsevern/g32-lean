import HodgeLean.Foundations.Program.SchoenCycleAdicAlgebraMap

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- The actual adic action commutes with projection to a transported formal support factor.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10. -/
theorem s2e_adic_projection_naturality
    {k A : Type*} [CommRing k] [CommRing A] [Algebra k A]
    (J I L : Ideal A) (hJI : J ≤ I) (hJL : J ≤ L)
    (α : A →ₐ[k] A)
    (hJ : ∀ n a, a ∈ J ^ n → α a ∈ J ^ n)
    (hI : ∀ n a, a ∈ I ^ n → α a ∈ L ^ n)
    (x : AdicCompletion J A) :
    s2e_adic_algebra_map J L (AlgHom.id k A)
        (fun n a ha => (Ideal.pow_right_mono hJL n) ha)
        (s2e_adic_algebra_map J J α hJ x) =
      s2e_adic_algebra_map I L α hI
        (s2e_adic_algebra_map J I (AlgHom.id k A)
          (fun n a ha => (Ideal.pow_right_mono hJI n) ha) x) := by
  apply AdicCompletion.ext
  intro n
  change Ideal.quotientMapₐ (L ^ n • ⊤ : Ideal A) (AlgHom.id k A) _
      (Ideal.quotientMapₐ (J ^ n • ⊤ : Ideal A) α _ (x.val n)) =
    Ideal.quotientMapₐ (L ^ n • ⊤ : Ideal A) α _
      (Ideal.quotientMapₐ (I ^ n • ⊤ : Ideal A) (AlgHom.id k A) _ (x.val n))
  refine Quotient.inductionOn' (x.val n) (fun a => ?_)
  rfl

end HodgeLean.Foundations.Program
