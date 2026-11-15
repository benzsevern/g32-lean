import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Field.Basic

/-! Removing an exceptional power from a Kummer equation. -/
noncomputable section
set_option maxHeartbeats 200000
namespace HodgeLean.Foundations.QuotientDuality

theorem rescale_kummer_equation
    {R K : Type*} [CommRing R] [Field K] [Algebra R K]
    (m : ℕ) (v : K) (q ε s E : R)
    (hv : v ^ m = algebraMap R K q)
    (hq : q = ε * (s * E ^ m)) (hE : algebraMap R K E ≠ 0) :
    (v / algebraMap R K E) ^ m = algebraMap R K ε * algebraMap R K s := by
  rw [div_pow]
  apply (div_eq_iff (pow_ne_zero m hE)).mpr
  rw [hv, hq, map_mul, map_mul, map_pow, mul_assoc]

#print axioms rescale_kummer_equation
end HodgeLean.Foundations.QuotientDuality
