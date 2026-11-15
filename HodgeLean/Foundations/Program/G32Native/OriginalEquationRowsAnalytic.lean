import HodgeLean.Foundations.TubularEuler.NormalFrameRegularCoefficientHelpers
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.FDeriv.Prod

/-! # Analytic differential rows of original regular equations -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry Filter Topology
namespace HodgeLean.Foundations.TubularEuler

theorem analyticAt_pi_fderiv_comp
    {B E : Type*} [NormedAddCommGroup B] [NormedSpace ℂ B]
    [NormedAddCommGroup E] [NormedSpace ℂ E] {k : ℕ}
    (f : Fin k → E → ℂ) (σ : B → E) (b : B)
    (hf : ∀ i, AnalyticAt ℂ (f i) (σ b)) (hσ : AnalyticAt ℂ σ b) :
    AnalyticAt ℂ (fun c => ContinuousLinearMap.pi
      (fun i => fderiv ℂ (f i) (σ c))) b := by
  have h := (AnalyticAt.pi hf).fderiv.comp hσ
  apply (h.contDiffAt.congr_of_eventuallyEq ?_).analyticAt
  have hn : ∀ᶠ a in 𝓝 (σ b), ∀ i, AnalyticAt ℂ (f i) a :=
    Filter.eventually_all.mpr (fun i => (hf i).eventually_analyticAt)
  filter_upwards [hσ.continuousAt.eventually hn] with c hc
  exact (fderiv_pi (fun i => (hc i).differentiableAt)).symm

/-- Derivatives of the original regular equations in one fixed ambient
chart vary analytically along every analytic coordinate parameter. -/
theorem original_equation_rows_analyticAt
    {B : Type*} [NormedAddCommGroup B] [NormedSpace ℂ B]
    (X : Over (Spec ↧ℂ)) (d k : ℕ) [SmoothOfRelativeDimension d X.hom]
    (A : X.left.Opens) (u : Fin k → Γ(X.left, A))
    (z : ComplexPoint X) (σ : B → (Fin d → ℂ)) (b : B)
    (hσ : AnalyticAt ℂ σ b)
    (ht : σ b ∈ (chartAt (Fin d → ℂ) z).target)
    (hA : (chartAt (Fin d → ℂ) z).symm (σ b) ∈ Point.overOpen A) :
    AnalyticAt ℂ (fun c => ContinuousLinearMap.pi (fun i : Fin k =>
      fderiv ℂ (fun a : Fin d → ℂ =>
        Point.evaluate A (u i) ((chartAt (Fin d → ℂ) z).symm a)) (σ c))) b := by
  apply analyticAt_pi_fderiv_comp _ σ b _ hσ
  intro i
  exact ComplexPoint.analyticAt_localChart_symm_evaluate X d z ht A (u i) hA

#print axioms analyticAt_pi_fderiv_comp
#print axioms original_equation_rows_analyticAt
end HodgeLean.Foundations.TubularEuler
