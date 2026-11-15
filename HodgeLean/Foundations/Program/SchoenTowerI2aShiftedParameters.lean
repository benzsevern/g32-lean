import HodgeLean.Foundations.Program.SchoenTowerL1aEtalePointSupport
import Mathlib.Algebra.Polynomial.AlgebraMap

/-! # Shifted etale curve parameters
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Subtracting a scalar from an etale curve parameter preserves its etale polynomial map.
Source: Mathlib, Polynomial.algEquivAevalXAddC and RingHom.Etale.stableUnderComposition. -/
theorem s2v_i2a_shifted_parameter_etale
    {K A : Type} [Field K] [CommRing A] [Algebra K A]
    (z : A) (hz : (Polynomial.aeval (R := K) z).toRingHom.Etale) (a : K) :
    (Polynomial.aeval (R := K) (z - algebraMap K A a)).toRingHom.Etale := by
  let e := Polynomial.algEquivAevalXAddC (-a)
  have H : (Polynomial.aeval (R := K) z).comp e.toAlgHom =
      Polynomial.aeval (R := K) (z - algebraMap K A a) := by
    apply Polynomial.algHom_ext
    simp [e, sub_eq_add_neg]
  have Hhom := congrArg AlgHom.toRingHom H
  rw [← Hhom]
  exact RingHom.Etale.stableUnderComposition e.toRingHom (Polynomial.aeval (R := K) z).toRingHom
    (RingHom.Etale.of_bijective e.bijective) hz

end HodgeLean.Foundations.Program
