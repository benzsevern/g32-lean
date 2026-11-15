import HodgeLean.Foundations.Curves.AbelTheorem.ResiduePoleSupport

noncomputable section
open HodgeLean.Foundations.Program
open Manifold
open scoped ContDiff BigOperators
namespace HodgeLean.Foundations.Curves.AbelTheorem
set_option maxHeartbeats 400000
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace C] [ChartedSpace E C]
  [IsManifold 𝓘(ℂ, E) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]

theorem residue_divisor_degree_zero (h : Module.finrank ℂ E = 1)
    (D : C →₀ ℤ) (w : b4c_MeroForm E C h)
    (hr : ∀ x, b4c_res (hE := h) w x = (D x : ℂ))
    (ha : ∀ x, x ∉ D.support → AnalyticAt ℂ (HurwitzPrymRR_loc h w x) 0) :
    b4c_deg D = 0 := by
  have he := b4c_residue_sum h w
  rw [b4c_residue_finsum_eq_poles_sum h w, pole_set_eq_residue_divisor_support h D w hr ha] at he
  simp only [hr] at he
  have hc : (b4c_deg D : ℂ) = 0 := by
    simpa only [b4c_deg, Finsupp.sum, Int.cast_sum] using he
  exact Int.cast_eq_zero.mp hc

end HodgeLean.Foundations.Curves.AbelTheorem
