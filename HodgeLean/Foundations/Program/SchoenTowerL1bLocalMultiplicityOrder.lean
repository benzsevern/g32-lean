import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.Multiplicity

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- If elements outside a prime divisor have nonzero constant coefficient,
series order is the prime multiplicity times the order of its image. -/
theorem s2v_l1b_local_multiplicity_order
    {R K : Type*} [CommRing R] [Field K]
    (ι : R →+* PowerSeries K) (p a : R)
    (hfin : FiniteMultiplicity p a)
    (hlocal : ∀ v : R, ¬ p ∣ v → (ι v).constantCoeff ≠ 0) :
    (ι a).order = emultiplicity p a * (ι p).order := by
  obtain ⟨v, hav, hpv⟩ := hfin.exists_eq_pow_mul_and_not_dvd
  have hv : (ι v).order = 0 := by
    by_contra h
    exact hlocal v hpv (PowerSeries.order_ne_zero_iff_constCoeff_eq_zero.mp h)
  calc
    (ι a).order = (ι (p ^ multiplicity p a * v)).order :=
      congrArg (fun b => (ι b).order) hav
    _ = (multiplicity p a : ENat) * (ι p).order := by
      rw [map_mul, map_pow, PowerSeries.order_mul, PowerSeries.order_pow,
        hv, add_zero, nsmul_eq_mul]
    _ = _ := by rw [hfin.emultiplicity_eq_multiplicity]

end HodgeLean.Foundations.Program
