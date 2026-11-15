import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Multiplicity

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A prime parameter and unit remainders preserve finite multiplicities under pullback. -/
theorem s2v_l1b_divisor_parameter_multiplicity
    {R T : Type*} [CommRing R] [CommRing T] [IsDomain T]
    (φ : R →+* T) (p a : R) (hfin : FiniteMultiplicity p a)
    (hp : Prime (φ p)) (hunit : ∀ v : R, ¬ p ∣ v → IsUnit (φ v)) :
    emultiplicity (φ p) (φ a) = emultiplicity p a := by
  obtain ⟨v, hav, hpv⟩ := hfin.exists_eq_pow_mul_and_not_dvd
  have hφa : φ a = φ p ^ multiplicity p a * φ v := by
    exact (congrArg φ hav).trans (by rw [map_mul, map_pow])
  rw [hφa, emultiplicity_mul hp,
    emultiplicity_pow_self_of_prime hp,
    emultiplicity_of_isUnit_right hp.not_isUnit (hunit v hpv), add_zero,
    hfin.emultiplicity_eq_multiplicity]

/-- A curve DVR parameter that remains prime preserves the orders of every nonzero numerator. -/
theorem s2v_l1b_divisor_dvr_parameter_multiplicity
    {R T : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing T] [IsDomain T]
    (φ : R →+* T) (p : R) (hp : Prime p) (hφp : Prime (φ p))
    (a : R) (ha : a ≠ 0) :
    emultiplicity (φ p) (φ a) = emultiplicity p a := by
  apply s2v_l1b_divisor_parameter_multiplicity φ p a
    (FiniteMultiplicity.of_prime_left hp ha) hφp
  intro v hv
  have hvunit : IsUnit v := by
    by_contra hn
    have hm : v ∈ IsLocalRing.maximalIdeal R := hn
    rw [hp.irreducible.maximalIdeal_eq, Ideal.mem_span_singleton] at hm
    exact hv hm
  exact hvunit.map φ

/-- Prime multiplicities scale by the order of the pulled-back parameter when remainders become units. -/
theorem s2v_l1b_divisor_parameter_order_scaling
    {R T : Type*} [CommRing R] [CommRing T] [IsDomain T]
    (φ : R →+* T) (p a : R) (q : T) (hq : Prime q)
    (hfin : FiniteMultiplicity p a)
    (hunit : ∀ v : R, ¬ p ∣ v → IsUnit (φ v)) :
    emultiplicity q (φ a) = emultiplicity p a * emultiplicity q (φ p) := by
  obtain ⟨v, hav, hpv⟩ := hfin.exists_eq_pow_mul_and_not_dvd
  have hφa : φ a = φ p ^ multiplicity p a * φ v :=
    (congrArg φ hav).trans (by rw [map_mul, map_pow])
  rw [hφa, emultiplicity_mul hq, emultiplicity_pow hq,
    emultiplicity_of_isUnit_right hq.not_isUnit (hunit v hpv), add_zero,
    hfin.emultiplicity_eq_multiplicity]

/-- Signed prime orders scale by the pulled-back parameter order. -/
theorem s2v_l1b_divisor_signed_parameter_order_scaling
    {R T : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    [CommRing T] [IsDomain T]
    (φ : R →+* T) (p : R) (hp : Prime p) (q : T) (hq : Prime q)
    (a b : R) (ha : a ≠ 0) (hb : b ≠ 0)
    (hunit : ∀ v : R, ¬ p ∣ v → IsUnit (φ v)) :
    (((emultiplicity q (φ a)).toNat : ℤ) - ((emultiplicity q (φ b)).toNat : ℤ)) =
      ((emultiplicity q (φ p)).toNat : ℤ) *
        (((emultiplicity p a).toNat : ℤ) - ((emultiplicity p b).toNat : ℤ)) := by
  rw [s2v_l1b_divisor_parameter_order_scaling φ p a q hq
      (FiniteMultiplicity.of_prime_left hp ha) hunit,
    s2v_l1b_divisor_parameter_order_scaling φ p b q hq
      (FiniteMultiplicity.of_prime_left hp hb) hunit,
    ENat.toNat_mul, ENat.toNat_mul, Nat.cast_mul, Nat.cast_mul]
  ring

end HodgeLean.Foundations.Program
