import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Coprime.Lemmas

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Powers of disjoint-support ideals give the multiplicative finite-jet product comparison.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Atiyah–Macdonald, Introduction to Commutative Algebra, Chapters 1 and 10. -/
def s2e_comaximal_finite_jet_equiv
    {k A : Type*} [CommRing k] [CommRing A] [Algebra k A]
    (I J : Ideal A) (h : IsCoprime I J) (n : ℕ) :
    (A ⧸ ((I ⊓ J) ^ n)) ≃ₐ[k] (A ⧸ (I ^ n)) × (A ⧸ (J ^ n)) := by
  have hp : (I ⊓ J) ^ n = I ^ n ⊓ J ^ n := by
    rw [← Ideal.mul_eq_inf_of_isCoprime h, mul_pow,
      Ideal.mul_eq_inf_of_isCoprime (h.pow)]
  let e := (Ideal.quotEquivOfEq hp).trans
    (Ideal.quotientInfEquivQuotientProd (I ^ n) (J ^ n) h.pow)
  exact
    { e with
      commutes' := fun r => by
        change e (Ideal.Quotient.mk _ (algebraMap k A r)) =
          (Ideal.Quotient.mk _ (algebraMap k A r), Ideal.Quotient.mk _ (algebraMap k A r))
        apply Prod.ext <;>
          simp only [e, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
            Ideal.quotientInfEquivQuotientProd_fst, Ideal.quotientInfEquivQuotientProd_snd]
          <;> rfl }

#print axioms s2e_comaximal_finite_jet_equiv
end HodgeLean.Foundations.Program
