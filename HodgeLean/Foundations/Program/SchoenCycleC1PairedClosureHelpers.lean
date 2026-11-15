import HodgeLean.Foundations.Program.SchoenCycleC1DividedPowerBasisHelpers
import HodgeLean.Foundations.Program.SchoenCycleC1KummerClosureHelpers

/-! # Integral-closure cancellation on paired Kummer charts -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Polynomial
namespace HodgeLean.Foundations.Program

/-- Paired exponents summing to the field degree remove exceptional
ramification in the actual integral closure whenever the residual parameters
are units. The exceptional parameter need not be a unit in the chart ring. -/
theorem s2e_c1_paired_integralClosure_etale
    {R K L : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
    [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [Algebra.IsSeparable K L] (B : PowerBasis K L)
    (a b m : ℕ) (hm : 0 < m) (hdim : Module.finrank K L = m)
    (hab : a + b = m) (x : R) (hx : algebraMap R K x ≠ 0)
    (v u d : Rˣ) (hd : (d : R) = (m : R))
    (hz : B.gen ^ m = algebraMap R L (x ^ a * (x * (v : R)) ^ b * (u : R))) :
    Algebra.Etale R (integralClosure R L) := by
  let c : Rˣ := v ^ b * u
  have heq : x ^ a * (x * (v : R)) ^ b * (u : R) = x ^ m * (c : R) := by
    dsimp only [c]
    simp only [Units.val_mul, Units.val_pow_eq_pow_val]
    rw [mul_pow, ← hab, pow_add]
    ring
  have hz' : B.gen ^ m = algebraMap K L
      ((algebraMap R K x) ^ m * algebraMap R K (c : R)) := by
    rw [heq, IsScalarTower.algebraMap_apply R K L] at hz
    simpa only [map_mul, map_pow] using hz
  obtain ⟨B', _, hmin⟩ := s2e_c1_divided_powerBasis B m hm hdim
    (algebraMap R K x) (algebraMap R K (c : R)) hx hz'
  exact s2e_c1_kummer_integralClosure_etale_of_generic_minpoly B' m hm c d hd hmin

end HodgeLean.Foundations.Program
