import HodgeLean.Foundations.QuotientDuality.MonomialComponentKernel
import Mathlib.RingTheory.LocalProperties.Basic

/-! Minimal components of a locally normal root cover have idempotent defining ideals. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.QuotientDuality

theorem minimal_prime_idempotent_of_local_domains
    (A : Type*) [CommRing A]
    (hlocal : ∀ (q : Ideal A) [q.IsPrime], IsDomain (Localization.AtPrime q))
    (p : Ideal A) (hp : IsMinimalPrime p) : IsIdempotentElem p := by
  change p * p = p
  apply Ideal.eq_of_localization_maximal
  intro M hM
  letI : M.IsMaximal := hM
  by_cases hpM : p ≤ M
  · letI : IsDomain (Localization.AtPrime M) := hlocal M
    have hker := minimal_prime_eq_localization_kernel A p M hp hpM
    have hz : p.map (algebraMap A (Localization.AtPrime M)) = ⊥ := by
      apply le_antisymm ?_ bot_le
      apply Ideal.map_le_iff_le_comap.mpr
      exact hker.symm.le
    rw [Ideal.map_mul, hz, Ideal.bot_mul]
  · have ht := IsLocalization.AtPrime.map_eq_top_of_not_le
      (S := Localization.AtPrime M) hpM
    rw [Ideal.map_mul, ht, Ideal.top_mul]

#print axioms minimal_prime_idempotent_of_local_domains
end HodgeLean.Foundations.QuotientDuality
