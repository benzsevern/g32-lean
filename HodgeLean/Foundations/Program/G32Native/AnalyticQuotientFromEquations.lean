import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-! # Recovering quotient operators from local equation coefficients -/

noncomputable section
open Filter Topology
namespace HodgeLean.Foundations.TubularEuler

/-- If the equations form a basis at the reference point, their analytic
coefficient matrix and analytic covectors determine an analytic quotient
operator, even when that operator was initially specified pointwise.
Source: Mathlib, `contDiffAt_map_inverse` and
`ContinuousLinearMap.IsInvertible`. -/
theorem analyticAt_quotient_of_equation_coefficients
    {𝕜 B E N : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup B] [NormedSpace 𝕜 B]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup N] [NormedSpace 𝕜 N] [CompleteSpace N]
    (C : B → N →L[𝕜] N) (F D : B → E →L[𝕜] N) (b : B)
    (hC : AnalyticAt 𝕜 C b) (hF : AnalyticAt 𝕜 F b)
    (e : N ≃L[𝕜] N) (he : C b = e.toContinuousLinearMap)
    (hCD : ∀ᶠ c in 𝓝 b, (C c).comp (D c) = F c) :
    AnalyticAt 𝕜 D b := by
  have hi : AnalyticAt 𝕜 ContinuousLinearMap.inverse (C b) := by
    rw [he]
    exact (contDiffAt_map_inverse e).analyticAt
  have hInv := hi.comp hC
  have hformula : AnalyticAt 𝕜
      (fun c => (ContinuousLinearMap.inverse (C c)).comp (F c)) b :=
    (hInv.contDiffAt.clm_comp hF.contDiffAt).analyticAt
  have hunit : ∀ᶠ c in 𝓝 b, (C c).IsInvertible := by
    exact hC.continuousAt.eventually
      (ContinuousLinearMap.IsInvertible.eventually_nhds
        (show (C b).IsInvertible from ⟨e, he.symm⟩))
  have heq : D =ᶠ[𝓝 b]
      (fun c => (ContinuousLinearMap.inverse (C c)).comp (F c)) := by
    filter_upwards [hCD, hunit] with c hc hci
    obtain ⟨ec, hec⟩ := hci
    rw [← hc, ← hec]
    ext u
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inverse_equiv,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply]
  exact (hformula.contDiffAt.congr_of_eventuallyEq heq).analyticAt

#print axioms analyticAt_quotient_of_equation_coefficients
end HodgeLean.Foundations.TubularEuler
