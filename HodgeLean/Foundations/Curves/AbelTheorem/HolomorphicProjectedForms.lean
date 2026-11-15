import HodgeLean.Foundations.Curves.AbelTheorem.Defs

noncomputable section
open HodgeLean.Foundations.Program
open Manifold
open scoped ContDiff
namespace HodgeLean.Foundations.Curves.AbelTheorem
set_option maxHeartbeats 400000
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace C] [ChartedSpace E C]
  [IsManifold 𝓘(ℂ, E) ω C]

/-- Source: Forster, Lectures on Riemann Surfaces, §2, real and imaginary projections of a differential. -/
theorem holomorphic_projected_forms (h : Module.finrank ℂ E = 1) (θ : b3_HolForm E C) :
    b4c_residue_realForm h θ.val Complex.reCLM = b3Forms_reForm θ ∧
    b4c_residue_realForm h θ.val Complex.imCLM = b3Forms_imForm θ := by
  constructor
  · funext x
    ext v
    have hv : v = fun _ => v 0 := funext fun i => by fin_cases i; rfl
    rw [hv, b4c_residue_realForm_apply h θ.val θ.property.2, b3Forms_reForm_apply]
    rfl
  · funext x
    ext v
    have hv : v = fun _ => v 0 := funext fun i => by fin_cases i; rfl
    rw [hv, b4c_residue_realForm_apply h θ.val θ.property.2, b3Forms_imForm_apply]
    rfl

end HodgeLean.Foundations.Curves.AbelTheorem
