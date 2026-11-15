import Mathlib.RingTheory.AdicCompletion.Algebra

/-! # Multiplicative assembly of compatible finite coordinates -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Compatible finite coordinate algebra isomorphisms assemble to an adic algebra isomorphism.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10, inverse limits. -/
def s2e_adic_coordinate_equiv
    {k A B : Type*} [CommRing k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    (I : Ideal A) (J : Ideal B)
    (e : (n : ℕ) → (A ⧸ (I ^ n • ⊤ : Ideal A)) ≃ₐ[k] (B ⧸ (J ^ n • ⊤ : Ideal B)))
    (he : ∀ {m n : ℕ} (hmn : m ≤ n) (z : A ⧸ (I ^ n • ⊤ : Ideal A)),
      AdicCompletion.transitionMap J B hmn (e n z) =
        e m (AdicCompletion.transitionMap I A hmn z)) :
    AdicCompletion I A ≃ₐ[k] AdicCompletion J B where
  toFun x := ⟨fun n => e n (x.val n), fun hmn =>
    (he hmn (x.val _)).trans (congrArg (e _) (x.property hmn))⟩
  invFun y := ⟨fun n => (e n).symm (y.val n), fun hmn => by
    apply (e _).injective
    rw [← he, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply, y.property hmn]⟩
  left_inv x := by
    apply AdicCompletion.ext
    intro n
    exact (e n).symm_apply_apply (x.val n)
  right_inv y := by
    apply AdicCompletion.ext
    intro n
    exact (e n).apply_symm_apply (y.val n)
  map_add' x y := by
    apply AdicCompletion.ext
    intro n
    exact (e n).map_add (x.val n) (y.val n)
  map_mul' x y := by
    apply AdicCompletion.ext
    intro n
    exact (e n).map_mul (x.val n) (y.val n)
  commutes' c := by
    apply AdicCompletion.ext
    intro n
    exact (e n).commutes c

#print axioms s2e_adic_coordinate_equiv
end HodgeLean.Foundations.Program
