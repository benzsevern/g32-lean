import HodgeLean.Foundations.Program.SchoenTowerL1bLocalMultiplicityOrder
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Data.ENat.Monoid

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A discrete valuation ring expansion containing the formal variable sends every uniformizer to order one. -/
theorem s2v_l1b_transport_uniformizer_order
    {R K : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K]
    (ι : R →+* PowerSeries K)
    (hX : ∃ u : R, ι u = PowerSeries.X)
    {p : R} (hp : Irreducible p) : (ι p).order = 1 := by
  obtain ⟨u, hu⟩ := hX
  have hu0 : u ≠ 0 := by
    intro h
    exact PowerSeries.X_ne_zero (hu.symm.trans (by rw [h, map_zero]))
  obtain ⟨n, v, huv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hu0 hp
  have hv : (ι (v : R)).order = 0 := PowerSeries.order_zero_of_isUnit (v.isUnit.map ι)
  have heq : (n : ℕ∞) * (ι p).order = 1 := by
    have ho := congrArg (fun a : R => (ι a).order) huv
    rw [hu, PowerSeries.order_X, map_mul, map_pow, PowerSeries.order_mul,
      PowerSeries.order_pow, hv, zero_add, nsmul_eq_mul] at ho
    exact ho.symm
  have hn : n ≠ 0 := by
    intro h
    simpa only [h, Nat.cast_zero, zero_mul, zero_ne_one] using heq
  have hle : (ι p).order ≤ 1 := by
    calc
      _ ≤ (n : ℕ∞) * (ι p).order :=
        ENat.self_le_mul_left _ (by exact_mod_cast hn)
      _ = 1 := heq
  have hpos : 0 < (ι p).order := by
    by_contra h
    have hz : (ι p).order = 0 := le_antisymm (le_of_not_gt h) zero_le
    simpa only [hz, mul_zero, zero_ne_one] using heq
  exact le_antisymm hle (Order.one_le_iff_ne_zero.mpr (ne_of_gt hpos))

/-- An expansion containing the formal variable preserves the full discrete valuation. -/
theorem s2v_l1b_transport_dvr_order
    {R K : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K]
    (ι : R →+* PowerSeries K) (hX : ∃ u : R, ι u = PowerSeries.X)
    {p : R} (hp : Irreducible p) (a : R) (ha : a ≠ 0) :
    (ι a).order = emultiplicity p a := by
  have hlocal (v : R) (hv : ¬ p ∣ v) : (ι v).constantCoeff ≠ 0 := by
    have hvunit : IsUnit v := by
      by_contra hn
      have hmem : v ∈ IsLocalRing.maximalIdeal R := hn
      rw [hp.maximalIdeal_eq, Ideal.mem_span_singleton] at hmem
      exact hv hmem
    exact (PowerSeries.isUnit_constantCoeff _ (hvunit.map ι)).ne_zero
  rw [s2v_l1b_local_multiplicity_order ι p a
    (FiniteMultiplicity.of_prime_left (irreducible_iff_prime.mp hp) ha) hlocal,
    s2v_l1b_transport_uniformizer_order ι hX hp, mul_one]

end HodgeLean.Foundations.Program
