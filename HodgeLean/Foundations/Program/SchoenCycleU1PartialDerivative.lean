import HodgeLean.Foundations.Program.SchoenCycleU1Germs

/-! # Analytic dependence of a parameter derivative -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Filter Topology
namespace HodgeLean.Foundations.Program

/-- The parameter derivative of a jointly analytic coefficient remains analytic
in the curve coordinate, including at a multiple zero of the coefficient.
Source: Mathlib, `AnalyticAt.fderiv` and `HasFDerivAt.comp_hasDerivAt`;
ACGH, Geometry of Algebraic Curves I, Chapter I, local analytic divisor equations. -/
theorem s2e_u1_analyticAt_parameter_derivative
    (u : ℂ × ℂ → ℂ) (hu : AnalyticAt ℂ u (0, 0)) :
    AnalyticAt ℂ (fun z => deriv (fun t => u (t, z)) 0) 0 := by
  let E := ContinuousLinearMap.apply ℂ ℂ ((1, 0) : ℂ × ℂ)
  have hc : AnalyticAt ℂ (fun z : ℂ => fderiv ℂ u (0, z)) 0 :=
    hu.fderiv.comp_of_eq (analyticAt_const.prod analyticAt_id) rfl
  have ha : AnalyticAt ℂ (fun z : ℂ => fderiv ℂ u (0, z) (1, 0)) 0 :=
    (E.analyticAt _).comp hc
  have ht : Tendsto (fun z : ℂ => (0, z)) (𝓝 0) (𝓝 ((0, 0) : ℂ × ℂ)) :=
    (continuousAt_const.prodMk continuousAt_id).tendsto
  have hev : ∀ᶠ z : ℂ in 𝓝 0, AnalyticAt ℂ u (0, z) :=
    ht.eventually hu.eventually_analyticAt
  have heq : (fun z : ℂ => fderiv ℂ u (0, z) (1, 0)) =ᶠ[𝓝 0]
      (fun z => deriv (fun t => u (t, z)) 0) := by
    filter_upwards [hev] with z hz
    exact (hz.differentiableAt.hasFDerivAt.comp_hasDerivAt 0
      ((hasDerivAt_id 0).prodMk (hasDerivAt_const 0 z))).deriv.symm
  exact ha.congr heq

end HodgeLean.Foundations.Program
