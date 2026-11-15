import HodgeLean.Foundations.Program.SchoenTowerL1bLocalMultiplicityOrder
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A nonzero invariant series has order divisible by the exact order of the rescaling scalar. -/
theorem s2v_l1b_divisor_invariant_series_order
    {K : Type*} [Field K] {ζ : K} {d : ℕ}
    (hζ : IsPrimitiveRoot ζ d) (F : PowerSeries K) (hF : F ≠ 0)
    (hfixed : PowerSeries.rescale ζ F = F) : d ∣ F.order.toNat := by
  have hc := congrArg (PowerSeries.coeff F.order.toNat) hfixed
  rw [PowerSeries.coeff_rescale] at hc
  apply (hζ.pow_eq_one_iff_dvd _).mp
  exact mul_right_cancel₀ (PowerSeries.coeff_order hF) (hc.trans (one_mul _).symm)

/-- One descended element of order d determines the invariant parameter order. -/
theorem s2v_l1b_divisor_parameter_order_of_descended_element
    {R K : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R] [Field K]
    (β : R →+* PowerSeries K) (hβ : Function.Injective β)
    (p : R) (hp : Prime p)
    (hlocal : ∀ v : R, ¬ p ∣ v → (β v).constantCoeff ≠ 0)
    {ζ : K} {d : ℕ} (hζ : IsPrimitiveRoot ζ d)
    (hfixed : PowerSeries.rescale ζ (β p) = β p)
    (c : R) (hc : (β c).order = d) : (β p).order.toNat = d := by
  have hc0 : c ≠ 0 := by
    intro h
    simp only [h, map_zero, PowerSeries.order_zero] at hc
    exact ENat.top_ne_coe d hc
  have hp0 : β p ≠ 0 := fun h => hp.ne_zero (hβ (h.trans β.map_zero.symm))
  have hde := s2v_l1b_divisor_invariant_series_order hζ (β p) hp0 hfixed
  have ho := congrArg ENat.toNat
    (s2v_l1b_local_multiplicity_order β p c
      (FiniteMultiplicity.of_prime_left hp hc0) hlocal)
  rw [hc, ENat.toNat_natCast, ENat.toNat_mul] at ho
  apply Nat.dvd_antisymm
  · exact ⟨(emultiplicity p c).toNat, by simpa only [mul_comm] using ho⟩
  · exact hde

end HodgeLean.Foundations.Program
