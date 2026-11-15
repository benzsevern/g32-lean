import HodgeLean.Foundations.Program.SchoenCycleC1PairedClosureHelpers
import HodgeLean.Foundations.Program.SchoenCycleC1SignedExceptionalFactor

/-! # Integral closure cancellation with signed exceptional exponents -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Signed paired orders divisible by the covering degree remove the
exceptional factor in the actual integral closure. Negative orders are
allowed in the fraction field; the residual factor lies in the chart units. -/
theorem s2e_c1_signed_paired_integralClosure_etale
    {R K L : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
    [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [Algebra.IsSeparable K L] (B : PowerBasis K L)
    (a b : ℤ) (m : ℕ) (hm : 0 < m) (hdim : Module.finrank K L = m)
    (hab : (m : ℤ) ∣ a + b) (x : R) (hx : algebraMap R K x ≠ 0)
    (v u d : Rˣ) (hd : (d : R) = (m : R))
    (hz : B.gen ^ m = algebraMap K L
      ((algebraMap R K x) ^ a *
        (algebraMap R K x * algebraMap R K (v : R)) ^ b * algebraMap R K (u : R))) :
    Algebra.Etale R (integralClosure R L) := by
  obtain ⟨q, hq⟩ := hab
  let c : Rˣ := v ^ b * u
  have hv : algebraMap R K ((v ^ b : Rˣ) : R) = (algebraMap R K (v : R)) ^ b := by
    change ((Units.map (algebraMap R K).toMonoidHom (v ^ b) : Kˣ) : K) = _
    rw [map_zpow, Units.val_zpow_eq_zpow_val]
    rfl
  have hc : algebraMap R K (c : R) =
      (algebraMap R K (v : R)) ^ b * algebraMap R K (u : R) := by
    change algebraMap R K (((v ^ b : Rˣ) : R) * (u : R)) = _
    rw [map_mul, hv]
  have hz' : B.gen ^ m = algebraMap K L
      (((algebraMap R K x) ^ q) ^ m * algebraMap R K (c : R)) := by
    rw [s2e_c1_signed_exceptional_factor _ _ _ hx a b q m hq, ← hc] at hz
    exact hz
  obtain ⟨B', _, hmin⟩ := s2e_c1_divided_powerBasis B m hm hdim
    ((algebraMap R K x) ^ q) (algebraMap R K (c : R)) (zpow_ne_zero q hx) hz'
  exact s2e_c1_kummer_integralClosure_etale_of_generic_minpoly B' m hm c d hd hmin

end HodgeLean.Foundations.Program
