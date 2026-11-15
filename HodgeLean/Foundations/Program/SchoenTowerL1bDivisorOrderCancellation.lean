import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorUnitOrder

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Associated pulled-back parameters cancel from an equality of fractions up to a DVR unit. -/
theorem s2v_l1b_divisor_parameter_order_cancellation
    {R S T K : Type*}
    [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    [CommRing S] [IsDomain S] [UniqueFactorizationMonoid S]
    [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    [Field K] [Algebra T K] [IsFractionRing T K]
    (φ : R →+* T) (ψ : S →+* T) (hφ : Function.Injective φ) (hψ : Function.Injective ψ)
    (p : R) (hp : Prime p) (π : S) (hπ : Prime π)
    (hφunit : ∀ r, IsUnit (φ r) ↔ ¬ p ∣ r)
    (hψunit : ∀ s, IsUnit (ψ s) ↔ ¬ π ∣ s)
    (hassoc : Associated (φ p) (ψ π))
    (a b : R) (ha : a ≠ 0) (hb : b ≠ 0)
    (c d : S) (hc : c ≠ 0) (hd : d ≠ 0)
    (u : T) (hu : IsUnit u)
    (heq : algebraMap T K (φ a) / algebraMap T K (φ b) =
      (algebraMap T K (ψ c) / algebraMap T K (ψ d)) * algebraMap T K u) :
    ((emultiplicity p a).toNat : ℤ) - ((emultiplicity p b).toNat : ℤ) =
      ((emultiplicity π c).toNat : ℤ) - ((emultiplicity π d).toNat : ℤ) := by
  obtain ⟨q, hqirr⟩ := IsDiscreteValuationRing.exists_irreducible T
  have hq : Prime q := hqirr.prime
  have hφp0 : φ p ≠ 0 := by simpa only [map_zero] using hφ.ne hp.ne_zero
  have hnunit : ¬ IsUnit (φ p) := fun h => (hφunit p).mp h (dvd_refl p)
  have hdiv : q ∣ φ p := by
    have hm : φ p ∈ IsLocalRing.maximalIdeal T := hnunit
    rwa [hqirr.maximalIdeal_eq, Ideal.mem_span_singleton] at hm
  have hfin := FiniteMultiplicity.of_prime_left hq hφp0
  have hepos : 0 < (emultiplicity q (φ p)).toNat := by
    rw [hfin.emultiplicity_eq_multiplicity, ENat.toNat_natCast]
    exact multiplicity_pos_of_dvd hdiv hfin
  have H := congrArg (Ring.ordFrac T) heq
  rw [map_mul, Ring.ordFrac_of_isUnit hu, mul_one,
    s2v_l1b_divisor_dvr_fraction_order q hq (φ a) (φ b)
      (by simpa only [map_zero] using hφ.ne ha) (by simpa only [map_zero] using hφ.ne hb),
    s2v_l1b_divisor_dvr_fraction_order q hq (ψ c) (ψ d)
      (by simpa only [map_zero] using hψ.ne hc) (by simpa only [map_zero] using hψ.ne hd)] at H
  have H' := WithZero.exp_injective H
  rw [s2v_l1b_divisor_signed_parameter_order_scaling φ p hp q hq a b ha hb
      (fun r hr => (hφunit r).mpr hr),
    s2v_l1b_divisor_signed_parameter_order_scaling ψ π hπ q hq c d hc hd
      (fun s hs => (hψunit s).mpr hs),
    ← emultiplicity_eq_of_associated_right hassoc] at H'
  exact mul_left_cancel₀ (by exact_mod_cast hepos.ne') H'

end HodgeLean.Foundations.Program
