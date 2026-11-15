import HodgeLean.Foundations.Curves.AbelTheorem.CurveBilinear

noncomputable section
open HodgeLean.Foundations.Program
open Set Filter Manifold ContinuousAlternatingMap MeasureTheory Metric
open scoped Topology ContDiff
namespace HodgeLean.Foundations.Curves.AbelTheorem
set_option maxHeartbeats 400000
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace C] [ChartedSpace E C]
  [IsManifold 𝓘(ℂ, E) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]
  [MeasurableSpace E] [BorelSpace E]
attribute [local instance] b3Forms_isManifold_real

theorem dual_form_period_is_intersection (h : Module.finrank ℂ E = 1)
    (Q : LinearMap.BilinForm ℤ (b3_periodLattice E C)) (hQ : b3_IsIntersectionForm E Q)
    (γ δ : b3_SmoothLoop E C) (η : C → E [⋀^Fin 1]→L[ℝ] ℝ)
    (hη : b3Forms_IsSmooth η)
    (hdual : ∀ α : C → E [⋀^Fin 1]→L[ℝ] ℝ, b3Forms_IsSmooth α → b3Forms_d α = 0 →
      b3Forms_integral (b3Rest_b h) (b3Forms_wedgeForm α η) =
        b3Forms_lineIntegral α γ.val 0 1) :
    b3Forms_lineIntegral η δ.val 0 1 =
      (Q (b3_latticePeriod E C γ) (b3_latticePeriod E C δ) : ℝ) := by
  have he := b3_intersectionForm_unique h Q (b3Rest2_QZ h (b3Rest2_key h)) hQ
    (b3Rest2_isIntersectionForm h (b3Rest2_key h))
  rw [he, b3Rest2_QZ_apply, b3Rest2_Q_eq_lineIntegral h γ δ hη hdual]

end HodgeLean.Foundations.Curves.AbelTheorem
