import HodgeLean.Foundations.Program.SchoenCycleComaximalJets
import Mathlib.Algebra.Algebra.Pi

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- Pairwise comaximal support ideals separate every finite jet into its finite family of local factors.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Atiyah–Macdonald, Introduction to Commutative Algebra, Chapters 1 and 10. -/
def s2e_finite_support_jet_equiv
    {k A ι : Type*} [CommRing k] [CommRing A] [Algebra k A] [Fintype ι]
    (I : ι → Ideal A) (h : Pairwise (fun i j => IsCoprime (I i) (I j))) (n : ℕ) :
    (A ⧸ ((⨅ i, I i) ^ n)) ≃ₐ[k] (∀ i, A ⧸ (I i ^ n)) := by
  classical
  have hp (j : ℕ) : (∏ i, I i ^ j) = ⨅ i, I i ^ j := by
    have hh : (↑(Finset.univ : Finset ι) : Set ι).Pairwise
        (fun a b => IsCoprime (I a ^ j) (I b ^ j)) := by
      intro a _ b _ hab
      exact (h hab).pow
    simpa using (Ideal.prod_eq_iInf_of_pairwise_isCoprime hh)
  have hp1 : (∏ i, I i) = ⨅ i, I i := by simpa using hp 1
  have he : (⨅ i, I i) ^ n = ⨅ i, I i ^ n := by
    rw [← hp1, ← Finset.prod_pow, hp]
  let e := (Ideal.quotEquivOfEq he).trans
    (Ideal.quotientInfRingEquivPiQuotient (fun i => I i ^ n) (fun _ _ hab => (h hab).pow))
  exact
    { e with
      commutes' := fun r => by
        change e (Ideal.Quotient.mk _ (algebraMap k A r)) =
          (fun i => Ideal.Quotient.mk (I i ^ n) (algebraMap k A r))
        funext i
        simp only [e, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
          Ideal.quotientInfRingEquivPiQuotient_mk_apply]
        rfl }

#print axioms s2e_finite_support_jet_equiv
end HodgeLean.Foundations.Program
