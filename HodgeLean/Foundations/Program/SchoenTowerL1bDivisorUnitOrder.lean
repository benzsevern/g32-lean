import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorDVRFractionOrder

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A fraction that becomes a unit in a DVR over the specified prime has signed prime order zero. -/
theorem s2v_l1b_divisor_unit_fraction_order_zero
    {R T K : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    [Field K] [Algebra T K] [IsFractionRing T K]
    (φ : R →+* T) (hφ : Function.Injective φ) (p : R) (hp : Prime p)
    (hφunit : ∀ r, IsUnit (φ r) ↔ ¬ p ∣ r)
    (a b : R) (ha : a ≠ 0) (hb : b ≠ 0) (u : T) (hu : IsUnit u)
    (heq : algebraMap T K (φ a) / algebraMap T K (φ b) = algebraMap T K u) :
    ((emultiplicity p a).toNat : ℤ) - ((emultiplicity p b).toNat : ℤ) = 0 := by
  obtain ⟨q, hqirr⟩ := IsDiscreteValuationRing.exists_irreducible T
  have hq : Prime q := hqirr.prime
  have hφp0 : φ p ≠ 0 := by simpa only [map_zero] using hφ.ne hp.ne_zero
  have hφa0 : φ a ≠ 0 := by simpa only [map_zero] using hφ.ne ha
  have hφb0 : φ b ≠ 0 := by simpa only [map_zero] using hφ.ne hb
  have hnunit : ¬ IsUnit (φ p) := fun h => (hφunit p).mp h (dvd_refl p)
  have hdiv : q ∣ φ p := by
    have hm : φ p ∈ IsLocalRing.maximalIdeal T := hnunit
    rwa [hqirr.maximalIdeal_eq, Ideal.mem_span_singleton] at hm
  have hfin := FiniteMultiplicity.of_prime_left hq hφp0
  have hepos : 0 < (emultiplicity q (φ p)).toNat := by
    rw [hfin.emultiplicity_eq_multiplicity, ENat.toNat_natCast]
    exact multiplicity_pos_of_dvd hdiv hfin
  have H := congrArg (Ring.ordFrac T) heq
  rw [s2v_l1b_divisor_dvr_fraction_order q hq (φ a) (φ b) hφa0 hφb0,
    Ring.ordFrac_of_isUnit hu] at H
  have hz := WithZero.exp_eq_one.mp H
  rw [s2v_l1b_divisor_signed_parameter_order_scaling φ p hp q hq a b ha hb
    (fun v hv => (hφunit v).mpr hv)] at hz
  exact (mul_eq_zero.mp hz).resolve_left (by exact_mod_cast hepos.ne')

end HodgeLean.Foundations.Program
