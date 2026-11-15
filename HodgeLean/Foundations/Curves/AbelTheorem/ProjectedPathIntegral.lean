import HodgeLean.Foundations.Curves.AbelTheorem.Defs

noncomputable section
open HodgeLean.Foundations.Program
open Set Manifold MeasureTheory
open scoped ContDiff
namespace HodgeLean.Foundations.Curves.AbelTheorem
set_option maxHeartbeats 400000
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace C] [ChartedSpace E C]
  [IsManifold 𝓘(ℂ, E) ω C]
attribute [local instance] b3Forms_isManifold_real

theorem projected_form_path_integral (h : Module.finrank ℂ E = 1)
    (θ : TangentBundle 𝓘(ℂ, E) C → ℂ) (hθ : HurwitzPrymRR_IsLinear θ)
    (P : ℂ →L[ℝ] ℝ) (γ : ℝ → C)
    (hint : IntervalIntegrable (fun t => θ ⟨γ t, b3_velocity E C γ t⟩) volume 0 1) :
    b3Forms_lineIntegral (b4c_residue_realForm h θ P) γ 0 1 =
      P (b3_pathIntegral E C γ θ) := by
  unfold b3Forms_lineIntegral b3_pathIntegral
  rw [← P.intervalIntegral_comp_comm hint]
  apply intervalIntegral.integral_congr
  intro t _
  exact b4c_residue_realForm_apply h θ hθ P (γ t) _

end HodgeLean.Foundations.Curves.AbelTheorem
