import HodgeLean.Foundations.Curves.AbelAdapter.StageFour.RegularSingularExtension
import HodgeLean.Foundations.Curves.AbelAdapter.StageFour.ScalarDivisorNormalization

noncomputable section
open HodgeLean.Foundations.Program
open Manifold Filter Topology
open scoped ContDiff
namespace HodgeLean.Foundations.Curves.AbelAdapter.StageFour

/-- Source: Forster, Lectures on Riemann Surfaces, §§10, 13, 18, divisors of exponential primitives. -/
theorem meromorphicFunction_of_logarithmic_solution
    {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (h : Module.finrank ℂ E = 1) (D : C →₀ ℤ) (w : b4c_MeroForm E C h)
    (hres : ∀ x, b4c_res (hE := h) w x = (D x : ℂ))
    (ho : ∀ x, (-1 : WithTop ℤ) ≤ meromorphicOrderAt (HurwitzPrymRR_loc h w x) 0)
    (f : C → ℂ)
    (hsol : ∀ x, ∀ᶠ z in 𝓝[≠] 0,
      let F := fun t : ℂ => f ((extChartAt 𝓘(ℂ, E) x).symm
        (extChartAt 𝓘(ℂ, E) x x + b4cov_lineEquiv h t))
      F z ≠ 0 ∧ HasDerivAt F (HurwitzPrymRR_loc h w x z * F z) z)
    (p : C) (hp : ContinuousAt f p) (hne : f p ≠ 0) :
    ∃ F : b4c_MeroFun E C, (∃ x, F x ≠ (0 : ℂ)) ∧ b4c_div E F = D := by
  have hlocal (x : C) := meromorphic_extension_of_logarithmic_equation
    (w.property.2 x) (ho x) (D x) (hres x) (hsol x)
  exact meromorphicFunction_of_scalar_local_orders h D f
    (fun x => (hlocal x).1) (fun x => (hlocal x).2) p hp hne

end HodgeLean.Foundations.Curves.AbelAdapter.StageFour
