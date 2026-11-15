import HodgeLean.Foundations.Program.SchoenCycleU1StationaryPreparation

/-! # Stationary analytic numerators and differential variations -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Filter Topology
namespace HodgeLean.Foundations.Program

/-- A stationary analytic numerator with a unit cofactor forces divisibility
of the first differential variation by its original coefficient.
Source: ACGH, Geometry of Algebraic Curves I, Chapter I, local divisor equations;
Mathlib, the analytic inverse and derivative product rules. -/
theorem s2e_u1_stationary_numerator_factor_divisibility
    (θ δ : ℂ → ℂ) (u F : ℂ × ℂ → ℂ)
    (hu : AnalyticAt ℂ u (0, 0)) (hF : AnalyticAt ℂ F (0, 0))
    (hu0 : u (0, 0) ≠ 0)
    (he : F =ᶠ[𝓝 (0, 0)]
      (fun tz : ℂ × ℂ => u tz * (θ tz.2 + tz.1 * δ tz.2)))
    (hstationary : ∀ᶠ z : ℂ in 𝓝 0, deriv (fun t => F (t, z)) 0 = 0) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧ δ =ᶠ[𝓝 0] (fun z => g z * θ z) := by
  have hv : AnalyticAt ℂ (fun tz => 1 / u tz) (0, 0) := analyticAt_const.div hu hu0
  have hv0 : (1 : ℂ) / u (0, 0) ≠ 0 := div_ne_zero one_ne_zero hu0
  have hunit : ∀ᶠ tz in 𝓝 ((0, 0) : ℂ × ℂ), u tz ≠ 0 :=
    hu.continuousAt.eventually_ne hu0
  have he' : (fun tz : ℂ × ℂ => θ tz.2 + tz.1 * δ tz.2) =ᶠ[𝓝 (0, 0)]
      (fun tz => (1 / u tz) * F tz) := by
    filter_upwards [he, hunit] with tz htz hn
    rw [htz]
    field_simp
  exact s2e_u1_stationary_preparation_analytic_quotient θ δ _ F hv hF hv0 he' hstationary

end HodgeLean.Foundations.Program
