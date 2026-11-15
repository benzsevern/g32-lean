import Mathlib.RingTheory.AdicCompletion.Algebra

/-! # Multiplicative maps on adic coordinates -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A filtration-preserving algebra map acts on adic coordinates by its actual finite quotient maps.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10. -/
def s2e_adic_algebra_map
    {k A B : Type*} [CommRing k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    (I : Ideal A) (J : Ideal B) (f : A →ₐ[k] B)
    (h : ∀ n : ℕ, ∀ a ∈ I ^ n, f a ∈ J ^ n) :
    AdicCompletion I A →ₐ[k] AdicCompletion J B := by
  have hp (n : ℕ) : (I ^ n • ⊤ : Ideal A) ≤ (J ^ n • ⊤ : Ideal B).comap f := by
    intro a ha
    have ha' : a ∈ I ^ n := by simpa using ha
    simpa using h n a ha'
  let q (n : ℕ) := Ideal.quotientMapₐ (J ^ n • ⊤ : Ideal B) f (hp n)
  have hcompat {m n : ℕ} (hmn : m ≤ n) (z : A ⧸ (I ^ n • ⊤ : Ideal A)) :
      AdicCompletion.transitionMap J B hmn (q n z) =
        q m (AdicCompletion.transitionMap I A hmn z) := by
    refine Quotient.inductionOn' z (fun a => ?_)
    rfl
  exact
    { toFun := fun x => ⟨fun n => q n (x.val n), fun hmn =>
        (hcompat hmn (x.val _)).trans (congrArg (q _) (x.property hmn))⟩
      map_zero' := AdicCompletion.ext (fun n => (q n).map_zero)
      map_one' := AdicCompletion.ext (fun n => (q n).map_one)
      map_add' := fun x y => AdicCompletion.ext (fun n => (q n).map_add (x.val n) (y.val n))
      map_mul' := fun x y => AdicCompletion.ext (fun n => (q n).map_mul (x.val n) (y.val n))
      commutes' := fun c => AdicCompletion.ext (fun n => (q n).commutes c) }

#print axioms s2e_adic_algebra_map
end HodgeLean.Foundations.Program
