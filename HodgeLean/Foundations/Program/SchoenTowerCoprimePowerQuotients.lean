import HodgeLean.Foundations.Program.SchoenTowerAdicAction
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Coprime.Lemmas

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

namespace HodgeLean.Foundations.Program
open Function

/-- Powers commute with a finite intersection of pairwise coprime ideals. -/
theorem s2t_iInf_coprime_pow {A ι : Type*} [CommRing A] [Fintype ι]
    (I : ι → Ideal A) (hI : Pairwise (IsCoprime on I)) (n : ℕ) :
    (⨅ i, I i) ^ n = ⨅ i, I i ^ n := by
  classical
  have hp (J : ι → Ideal A) (hJ : Pairwise (IsCoprime on J)) :
      ∏ i, J i = ⨅ i, J i := by
    simpa only [Finset.mem_univ, iInf_true] using
      (Ideal.prod_eq_iInf_of_pairwise_isCoprime (s := Finset.univ)
        (J := J) (fun i _ j _ hij => hJ hij))
  rw [← hp I hI, ← hp (fun i => I i ^ n) (fun i j hij => (hI hij).pow)]
  rw [Finset.prod_pow]

/-- The power quotient of a coprime intersection is the product of the power quotients. -/
def s2t_coprimePowerQuotientEquiv {A ι : Type*} [CommRing A] [Fintype ι]
    (I : ι → Ideal A) (hI : Pairwise (IsCoprime on I)) (n : ℕ) :
    (A ⧸ (⨅ i, I i) ^ n) ≃+* ∀ i, A ⧸ I i ^ n :=
  (Ideal.quotEquivOfEq (s2t_iInf_coprime_pow I hI n)).trans
    (Ideal.quotientInfRingEquivPiQuotient (fun i => I i ^ n)
      (fun i j hij => (hI hij).pow))

/-- The product comparison preserves each specified residue representative. -/
theorem s2t_coprimePowerQuotientEquiv_mk {A ι : Type*} [CommRing A] [Fintype ι]
    (I : ι → Ideal A) (hI : Pairwise (IsCoprime on I)) (n : ℕ) (a : A) (i : ι) :
    s2t_coprimePowerQuotientEquiv I hI n (Ideal.Quotient.mk _ a) i =
      Ideal.Quotient.mk (I i ^ n) a := by
  rfl

/-- Coprime power quotient comparisons commute with all adic transitions. -/
theorem s2t_coprimePowerQuotientEquiv_transition {A ι : Type*} [CommRing A] [Fintype ι]
    (I : ι → Ideal A) (hI : Pairwise (IsCoprime on I)) {m n : ℕ} (hmn : m ≤ n)
    (x : A ⧸ (⨅ i, I i) ^ n) (i : ι) :
    s2t_coprimePowerQuotientEquiv I hI m
      (Ideal.Quotient.factorPow (⨅ i, I i) hmn x) i =
      Ideal.Quotient.factorPow (I i) hmn (s2t_coprimePowerQuotientEquiv I hI n x i) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

end HodgeLean.Foundations.Program
