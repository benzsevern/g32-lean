import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorDVRParameter
import Mathlib.RingTheory.OrderOfVanishing.Noetherian

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- The fraction-field order of a nonzero DVR element is its prime-parameter multiplicity. -/
theorem s2v_l1b_divisor_dvr_element_order
    {R K : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (p : R) (hp : Prime p) (a : R) (ha : a ≠ 0) :
    Ring.ordFrac R (algebraMap R K a) =
      WithZero.exp ((emultiplicity p a).toNat : ℤ) := by
  have hfin := FiniteMultiplicity.of_prime_left hp ha
  obtain ⟨v, hav, hpv⟩ := hfin.exists_eq_pow_mul_and_not_dvd
  have hvunit : IsUnit v := by
    by_contra hn
    have hm : v ∈ IsLocalRing.maximalIdeal R := hn
    rw [hp.irreducible.maximalIdeal_eq, Ideal.mem_span_singleton] at hm
    exact hpv hm
  have hmap : algebraMap R K a = algebraMap R K p ^ multiplicity p a * algebraMap R K v :=
    (congrArg (algebraMap R K) hav).trans (by rw [map_mul, map_pow])
  rw [hmap, map_mul, map_pow, Ring.ordFrac_irreducible hp.irreducible,
    Ring.ordFrac_of_isUnit hvunit, mul_one, ← WithZero.exp_nsmul,
    nsmul_eq_mul, mul_one, hfin.emultiplicity_eq_multiplicity, ENat.toNat_natCast]

/-- A nonzero DVR fraction has order equal to the difference of its numerator and denominator orders. -/
theorem s2v_l1b_divisor_dvr_fraction_order
    {R K : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (p : R) (hp : Prime p) (a b : R) (ha : a ≠ 0) (hb : b ≠ 0) :
    Ring.ordFrac R (algebraMap R K a / algebraMap R K b) =
      WithZero.exp (((emultiplicity p a).toNat : ℤ) - ((emultiplicity p b).toNat : ℤ)) := by
  rw [map_div₀, s2v_l1b_divisor_dvr_element_order p hp a ha,
    s2v_l1b_divisor_dvr_element_order p hp b hb, WithZero.exp_sub]

end HodgeLean.Foundations.Program
