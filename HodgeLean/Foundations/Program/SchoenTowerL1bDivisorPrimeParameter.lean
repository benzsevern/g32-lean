import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Ideal.Maps

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A local parameter stays prime when the extended maximal ideal is prime. -/
theorem s2v_l1b_divisor_prime_of_maximal_ideal_map
    {R T : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing T] [IsDomain T] (φ : R →+* T) (hφ : Function.Injective φ)
    (hI : (Ideal.map φ (IsLocalRing.maximalIdeal R)).IsPrime)
    (π : R) (hπ : Prime π) : Prime (φ π) := by
  rw [hπ.irreducible.maximalIdeal_eq, Ideal.map_span, Set.image_singleton] at hI
  exact (Ideal.span_singleton_prime (by simpa only [map_zero] using hφ.ne hπ.ne_zero)).mp hI

end HodgeLean.Foundations.Program
