import HodgeLean.Foundations.Program.SchoenCycleAdicAlgebraMap

/-! # Composition of actual adic algebra maps -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Adic algebra maps preserve composition with the actual finite quotient actions.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10. -/
theorem s2e_adic_algebra_map_comp
    {k A B C : Type*} [CommRing k] [CommRing A] [CommRing B] [CommRing C]
    [Algebra k A] [Algebra k B] [Algebra k C]
    (I : Ideal A) (J : Ideal B) (K : Ideal C)
    (f : A →ₐ[k] B) (g : B →ₐ[k] C)
    (hf : ∀ n : ℕ, ∀ a ∈ I ^ n, f a ∈ J ^ n)
    (hg : ∀ n : ℕ, ∀ b ∈ J ^ n, g b ∈ K ^ n) :
    (s2e_adic_algebra_map J K g hg).comp (s2e_adic_algebra_map I J f hf) =
      s2e_adic_algebra_map I K (g.comp f) (fun n a ha => hg n (f a) (hf n a ha)) := by
  apply AlgHom.ext
  intro x
  apply AdicCompletion.ext
  intro n
  change Ideal.quotientMapₐ (K ^ n • ⊤ : Ideal C) g _
      (Ideal.quotientMapₐ (J ^ n • ⊤ : Ideal B) f _ (x.val n)) =
    Ideal.quotientMapₐ (K ^ n • ⊤ : Ideal C) (g.comp f) _ (x.val n)
  refine Quotient.inductionOn' (x.val n) (fun a => ?_)
  rfl

#print axioms s2e_adic_algebra_map_comp
end HodgeLean.Foundations.Program
