import HodgeLean.Foundations.Program.SchoenCycleAdicAlgebraMap
import HodgeLean.Foundations.Program.SchoenCycleAdicCoordinateEquiv

/-! # Bijectivity detected in finite adic coordinates -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Actual finite jet isomorphisms make the induced adic algebra map bijective.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10. -/
theorem s2e_adic_algebra_map_bijective
    {k A B : Type*} [CommRing k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    (I : Ideal A) (J : Ideal B) (f : A →ₐ[k] B)
    (h : ∀ n : ℕ, ∀ a ∈ I ^ n, f a ∈ J ^ n)
    (he : ∀ n : ℕ, ∃ e : (A ⧸ I ^ n) ≃ₐ[k] (B ⧸ J ^ n),
      ∀ a, e (Ideal.Quotient.mk (I ^ n) a) = Ideal.Quotient.mk (J ^ n) (f a)) :
    Function.Bijective (s2e_adic_algebra_map I J f h) := by
  classical
  have hp (n : ℕ) : (I ^ n • ⊤ : Ideal A) ≤ (J ^ n • ⊤ : Ideal B).comap f := by
    intro a ha
    simpa using h n a (by simpa using ha)
  let q (n : ℕ) := Ideal.quotientMapₐ (J ^ n • ⊤ : Ideal B) f (hp n)
  have hq (n : ℕ) : Function.Bijective (q n) := by
    obtain ⟨e, he⟩ := he n
    let qA : (A ⧸ (I ^ n • ⊤ : Ideal A)) ≃ₐ[k] (A ⧸ I ^ n) :=
      Ideal.quotientEquivAlgOfEq k (by simp)
    let qB : (B ⧸ (J ^ n • ⊤ : Ideal B)) ≃ₐ[k] (B ⧸ J ^ n) :=
      Ideal.quotientEquivAlgOfEq k (by simp)
    let e' := (qA.trans e).trans qB.symm
    have hqe : e'.toAlgHom = q n := by
      apply AlgHom.ext
      intro z
      refine Quotient.inductionOn' z (fun a => ?_)
      apply qB.injective
      change qB (qB.symm (e (qA (Ideal.Quotient.mk _ a)))) = _
      rw [AlgEquiv.apply_symm_apply]
      change e (qA (Ideal.Quotient.mk _ a)) = qB (Ideal.Quotient.mk _ (f a))
      simp only [qA, qB, Ideal.quotientEquivAlgOfEq_mk, he]
    rw [← hqe]
    exact e'.bijective
  let e (n : ℕ) := AlgEquiv.ofBijective (q n) (hq n)
  have hcompat : ∀ {m n : ℕ} (hmn : m ≤ n) (z : A ⧸ (I ^ n • ⊤ : Ideal A)),
      AdicCompletion.transitionMap J B hmn (e n z) =
        e m (AdicCompletion.transitionMap I A hmn z) := by
    intro m n hmn z
    refine Quotient.inductionOn' z (fun a => ?_)
    rfl
  let E := s2e_adic_coordinate_equiv I J e hcompat
  have hE : E.toAlgHom = s2e_adic_algebra_map I J f h := by
    apply AlgHom.ext
    intro x
    apply AdicCompletion.ext
    intro n
    rfl
  rw [← hE]
  exact E.bijective

#print axioms s2e_adic_algebra_map_bijective
end HodgeLean.Foundations.Program
