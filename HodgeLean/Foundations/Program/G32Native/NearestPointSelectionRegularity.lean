import HodgeLean.Foundations.Program.G32Native.NearestPointEquationDerivative
import HodgeLean.Foundations.Program.G32Native.ImplicitSelectionSmoothness

/-! # Analyticity of a common local nearest-point selection

The critical equation and its invertible Gram derivative identify the selection
with one analytic implicit branch. No geodesic equation occurs.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open Filter Topology
namespace HodgeLean.Foundations.TubularEuler

/-- A selection of local squared-distance minima tending to an immersed base
point is analytic there, for an analytic parametrization.
Source: `nearestPoint_critical_equation`,
`nearestPointEquation_base_isInvertible`, and Mathlib's analytic implicit
function theorem `ContDiffAt.contDiffAt_implicitFunction`.
HC no distance; AV milestone no distance. -/
theorem nearestPoint_selection_analytic
    {B F : Type*} [NormedAddCommGroup B] [InnerProductSpace ℝ B]
    [FiniteDimensional ℝ B]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (σ : B → F) (b : B) (p : F → B)
    (hσ : ContDiffAt ℝ ⊤ σ b) (hinj : Function.Injective (fderiv ℝ σ b))
    (hp : Tendsto p (𝓝 (σ b)) (𝓝 b))
    (hmin : ∀ᶠ y in 𝓝 (σ b), IsLocalMin (fun c => ‖σ c - y‖ ^ 2) (p y)) :
    ContDiffAt ℝ ⊤ p (σ b) := by
  apply implicit_selection_contDiffAt (nearestPointEquation σ) (σ b) b p
    (nearestPointEquation_contDiffAt σ b (σ b) hσ)
    (nearestPointEquation_base_isInvertible σ b hσ hinj) hp
  have hreg := hp.eventually (hσ.eventually (by simp))
  filter_upwards [hreg, hmin] with y hy hm
  have hcrit := nearestPoint_critical_equation σ (p y) y (fderiv ℝ σ (p y))
    ((hy.differentiableAt (by simp)).hasFDerivAt) hm
  simpa only [nearestPointEquation, sub_self, map_zero] using hcrit

#print axioms nearestPoint_selection_analytic

end HodgeLean.Foundations.TubularEuler
