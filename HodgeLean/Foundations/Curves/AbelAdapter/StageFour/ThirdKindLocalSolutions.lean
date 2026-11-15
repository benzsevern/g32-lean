import HodgeLean.Foundations.Curves.AbelAdapter.StageFour.ThirdKindDivisor
import HodgeLean.Foundations.Curves.AbelAdapter.StageFour.LocalLogarithmicPrimitive

noncomputable section
open HodgeLean.Foundations.Program
open Manifold Filter Topology
open scoped ContDiff
namespace HodgeLean.Foundations.Curves.AbelAdapter.StageFour

/-- Source: Forster, Lectures on Riemann Surfaces, §§10, 18, local primitives of third-kind differentials. -/
theorem thirdKindDifferential_with_localSolutions
    {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (h : Module.finrank ℂ E = 1) (p : C) (D : C →₀ ℤ)
    (hdeg : b4c_deg D = 0) :
    ∃ w : b4c_MeroForm E C h,
      (∀ x, b4c_res (hE := h) w x = (D x : ℂ)) ∧
      (∀ x, x ∉ D.support → AnalyticAt ℂ (HurwitzPrymRR_loc h w x) 0) ∧
      ∀ x, ∃ F : ℂ → ℂ,
        MeromorphicAt F 0 ∧ meromorphicOrderAt F 0 = (D x : WithTop ℤ) ∧
        ∀ᶠ z in 𝓝[≠] 0, F z ≠ 0 ∧
          HasDerivAt F (HurwitzPrymRR_loc h w x z * F z) z := by
  obtain ⟨w, hres, ho, ha⟩ := thirdKindDifferential_supported_on_divisor h p D hdeg
  exact ⟨w, hres, ha, fun x =>
    meromorphic_logarithmicPrimitive_at_integral_residue
      (w.property.2 x) (ho x) (D x) (hres x)⟩

end HodgeLean.Foundations.Curves.AbelAdapter.StageFour
