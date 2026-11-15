import Mathlib.RingTheory.PowerSeries.Expand

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A series in the eth power of the parameter is fixed by rescaling by an
eth root of unity. -/
theorem s2v_l1b_rescale_expanded_series
    {K : Type*} [CommRing K] (e : ℕ) (he : e ≠ 0)
    (ζ : K) (hζ : ζ ^ e = 1) (f : PowerSeries K) :
    PowerSeries.rescale ζ (PowerSeries.expand e he f) = PowerSeries.expand e he f := by
  ext n
  rw [PowerSeries.coeff_rescale]
  by_cases h : e ∣ n
  · obtain ⟨j, rfl⟩ := h
    rw [pow_mul, hζ, one_pow, one_mul]
  · rw [PowerSeries.coeff_expand_of_not_dvd e he f h, mul_zero]

/-- Multiplying an expanded series by a parameter power gives its specified
rescaling character. -/
theorem s2v_l1b_rescale_expanded_monomial
    {K : Type*} [CommRing K] (e : ℕ) (he : e ≠ 0)
    (ζ : K) (hζ : ζ ^ e = 1) (f : PowerSeries K) (n : ℕ) :
    PowerSeries.rescale ζ (PowerSeries.X ^ n * PowerSeries.expand e he f) =
      PowerSeries.C (ζ ^ n) * (PowerSeries.X ^ n * PowerSeries.expand e he f) := by
  rw [map_mul, map_pow, PowerSeries.rescale_X,
    s2v_l1b_rescale_expanded_series e he ζ hζ, mul_pow, ← map_pow]
  ring

end HodgeLean.Foundations.Program
