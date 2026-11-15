import HodgeLean.Foundations.Curves.AbelTheorem.ProjectedScalarDerivative
import HodgeLean.Foundations.Curves.AbelTheorem.CenteredScalarDifferentiable

noncomputable section
open HodgeLean.Foundations.Program
open Set Filter Manifold
open scoped Topology ContDiff
namespace HodgeLean.Foundations.Curves.AbelTheorem
set_option maxHeartbeats 400000
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace C] [ChartedSpace E C]
  [IsManifold 𝓘(ℂ, E) ω C]
attribute [local instance] b3Forms_isManifold_real

/-- Source: Forster, Lectures on Riemann Surfaces, §2, the complex differential criterion. -/
theorem centered_scalar_hasDerivAt_of_projected_differentials
    (h : Module.finrank ℂ E = 1) (G : C → ℂ)
    (hG : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ G)
    (θ : TangentBundle 𝓘(ℂ, E) C → ℂ) (hθ : HurwitzPrymRR_IsLinear θ) (x : C)
    (hre : b3Forms_d (b3Forms_fun (E := E) (fun y => (G y).re)) x =
      b4c_residue_realForm h θ Complex.reCLM x)
    (him : b3Forms_d (b3Forms_fun (E := E) (fun y => (G y).im)) x =
      b4c_residue_realForm h θ Complex.imCLM x) :
    HasDerivAt (centeredScalar h G x) (θ ⟨x, b4cov_lineEquiv h 1⟩) 0 := by
  have hev (z : ℂ) : fderiv ℝ (centeredScalar h G x) 0 z =
      θ ⟨x, b4cov_lineEquiv h 1⟩ * z := by
    have hr := projected_scalar_differential_apply h G hG Complex.reCLM x z
    have hi := projected_scalar_differential_apply h G hG Complex.imCLM x z
    change b3Forms_d (b3Forms_fun (E := E) (fun y => (G y).re)) x
      (fun _ => b4cov_lineEquiv h z) = (fderiv ℝ (centeredScalar h G x) 0 z).re at hr
    change b3Forms_d (b3Forms_fun (E := E) (fun y => (G y).im)) x
      (fun _ => b4cov_lineEquiv h z) = (fderiv ℝ (centeredScalar h G x) 0 z).im at hi
    rw [hre, b4c_residue_realForm_apply h θ hθ] at hr
    rw [him, b4c_residue_realForm_apply h θ hθ] at hi
    have hl := b4c_residue_linear_value h θ hθ x (b4cov_lineEquiv h z)
    rw [ContinuousLinearEquiv.symm_apply_apply] at hl
    exact (Complex.ext hr.symm hi.symm).trans hl
  have hd := (centered_smooth_scalar h G hG x).differentiableAt (by simp)
  have he : (ContinuousLinearMap.mul ℂ ℂ (θ ⟨x, b4cov_lineEquiv h 1⟩)).restrictScalars ℝ =
      fderiv ℝ (centeredScalar h G x) 0 := by
    ext z
    exact (hev z).symm
  have hc := hasFDerivAt_of_restrictScalars ℝ hd.hasFDerivAt he
  simpa using hc.hasDerivAt

end HodgeLean.Foundations.Curves.AbelTheorem
