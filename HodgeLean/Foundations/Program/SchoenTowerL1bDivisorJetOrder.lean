import HodgeLean.Foundations.Program.SchoenTowerL1bTransportDvrOrder

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A jet agreeing with the d-th power of the parameter has series order d. -/
theorem s2v_l1b_divisor_parameter_jet_order
    {R K : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K]
    (ι : R →+* PowerSeries K) (p : R) (hp : Irreducible p)
    (hpX : ι p = PowerSeries.X) (v : R) (d : ℕ)
    (hjet : v - p ^ d ∈ IsLocalRing.maximalIdeal R ^ (d + 1)) :
    (ι v).order = d := by
  rw [hp.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hjet
  obtain ⟨w, hw⟩ := hjet
  have hv : v = p ^ d * (1 + p * w) := by
    rw [pow_succ] at hw
    linear_combination hw
  rw [hv, map_mul, map_pow, hpX, PowerSeries.order_mul, PowerSeries.order_X_pow]
  have hunit : IsUnit (ι (1 + p * w)) := by
    apply PowerSeries.isUnit_iff_constantCoeff.mpr
    rw [map_add, map_one, map_mul, hpX, map_add, map_one, map_mul,
      PowerSeries.constantCoeff_X, zero_mul, add_zero]
    exact isUnit_one
  rw [PowerSeries.order_zero_of_isUnit hunit, add_zero]

/-- Agreement to order d+1 preserves an arbitrary finite series order d. -/
theorem s2v_l1b_divisor_equal_jet_order
    {R K : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K]
    (ι : R →+* PowerSeries K) (p : R) (hp : Irreducible p)
    (hpX : ι p = PowerSeries.X) (v r : R) (d : ℕ)
    (hr : (ι r).order = d)
    (hjet : v - r ∈ IsLocalRing.maximalIdeal R ^ (d + 1)) :
    (ι v).order = d := by
  rw [hp.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hjet
  obtain ⟨w, hw⟩ := hjet
  have hh : (d + 1 : ℕ) ≤ (ι (v - r)).order := by
    rw [hw, map_mul, map_pow, hpX, PowerSeries.order_mul, PowerSeries.order_X_pow]
    exact le_self_add
  have hlt : (ι r).order < (ι (v - r)).order := by
    rw [hr]
    exact lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self d) hh
  have hv : ι v = ι r + ι (v - r) := by rw [map_sub]; ring
  rw [hv, PowerSeries.order_add_of_order_ne _ _ (ne_of_lt hlt), min_eq_left hlt.le, hr]

end HodgeLean.Foundations.Program
