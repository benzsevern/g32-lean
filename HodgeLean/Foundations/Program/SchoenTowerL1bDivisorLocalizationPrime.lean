import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Ideal.Maximal

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A prime element becomes a unit or remains prime under an injective localization. -/
theorem s2v_l1b_divisor_localization_prime_or_unit
    {R T : Type*} [CommRing R] [IsDomain R] [CommRing T] [IsDomain T]
    (M : Submonoid R) [Algebra R T] [IsLocalization M T]
    (hmap : Function.Injective (algebraMap R T)) (p : R) (hp : Prime p) :
    IsUnit (algebraMap R T p) ∨ Prime (algebraMap R T p) := by
  by_cases hu : IsUnit (algebraMap R T p)
  · exact Or.inl hu
  · right
    have hd : Disjoint (M : Set R) (Ideal.span {p} : Ideal R) := by
      rw [Set.disjoint_left]
      intro a ha hpa
      have hdiv : p ∣ a := Ideal.mem_span_singleton.mp hpa
      exact hu (isUnit_of_dvd_unit (map_dvd (algebraMap R T) hdiv)
        (IsLocalization.map_units T (⟨a, ha⟩ : M)))
    have hprime := IsLocalization.isPrime_of_isPrime_disjoint M T
      (Ideal.span {p}) ((Ideal.span_singleton_prime hp.ne_zero).mpr hp) hd
    rw [Ideal.map_span, Set.image_singleton] at hprime
    apply (Ideal.span_singleton_prime (by simpa only [map_zero] using hmap.ne hp.ne_zero)).mp hprime

end HodgeLean.Foundations.Program
