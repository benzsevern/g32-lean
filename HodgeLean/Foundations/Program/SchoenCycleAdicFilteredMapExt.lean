import HodgeLean.Foundations.Program.SchoenCycleAdicIdealPowerValues
import Mathlib.RingTheory.AdicCompletion.Algebra

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Filtered algebra maps between adic algebras are determined by their actual values on the original algebra.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10. -/
theorem s2e_adic_filtered_algHom_ext
    {k R S : Type*} [CommRing k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
    (I : Ideal R) (J : Ideal S) (hI : I.FG) (hJ : J.FG)
    (f g : AdicCompletion I R →ₐ[k] AdicCompletion J S)
    (hf : ∀ n r, r ∈ (I.map (algebraMap R (AdicCompletion I R))) ^ n →
      f r ∈ (J.map (algebraMap S (AdicCompletion J S))) ^ n)
    (hg : ∀ n r, r ∈ (I.map (algebraMap R (AdicCompletion I R))) ^ n →
      g r ∈ (J.map (algebraMap S (AdicCompletion J S))) ^ n)
    (h : ∀ r, f (AdicCompletion.of I R r) = g (AdicCompletion.of I R r)) : f = g := by
  ext z n
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (z.val n)
  have hz : (z - AdicCompletion.of I R r).val n = 0 := by
    change z.val n - Ideal.Quotient.mk (I ^ n • ⊤ : Ideal R) r = 0
    rw [hr, sub_self]
  have hz' := (s2e_adic_extended_power_mem_iff I hI n _).mpr hz
  have hf' := (s2e_adic_extended_power_mem_iff J hJ n _).mp (hf n _ hz')
  have hg' := (s2e_adic_extended_power_mem_iff J hJ n _).mp (hg n _ hz')
  rw [map_sub] at hf' hg'
  change (f z).val n - (f (AdicCompletion.of I R r)).val n = 0 at hf'
  change (g z).val n - (g (AdicCompletion.of I R r)).val n = 0 at hg'
  rw [sub_eq_zero] at hf' hg'
  rw [hf', hg', h r]

#print axioms s2e_adic_filtered_algHom_ext
end HodgeLean.Foundations.Program
