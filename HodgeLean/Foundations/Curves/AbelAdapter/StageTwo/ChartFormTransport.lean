import HodgeLean.Foundations.Curves.AbelAdapter.StageTwo.AnalyticFormFields

/-! # Fixed-chart normalization of B3 one-forms

HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
open HodgeLean.Foundations.Program
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Curves.AbelAdapter.StageTwo

variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace C] [ChartedSpace E C]
  [IsManifold 𝓘(ℂ, E) ω C]

/-- The fixed-chart covector, transported to the chart at a point, has the original tangent value.
Source: Forster, §9; b3Forms_fderiv_tr_comp_complex.
HC no distance; AV milestone no distance. -/
theorem b3ChartCovector_transport (θ : b3_HolForm E C) (z x : C)
    (hx : x ∈ (chartAt E z).source) (v : E) :
    b3ChartCovector θ z (chartAt E z x)
      (fderiv ℂ (b3Forms_tr x z) (chartAt E x x) v) = θ.val ⟨x, v⟩ := by
  have hdom : chartAt E x x ∈ b3Forms_trDom x z := by
    refine ⟨mem_chart_target E x, ?_⟩
    change (chartAt E x).symm (chartAt E x x) ∈ (chartAt E z).source
    rw [(chartAt E x).left_inv (mem_chart_source E x)]
    exact hx
  have hself : (chartAt E x).symm (chartAt E x x) ∈ (chartAt E x).source := by
    rw [(chartAt E x).left_inv (mem_chart_source E x)]
    exact mem_chart_source E x
  have hc := b3Forms_fderiv_tr_comp_complex (z := x) hdom hself
  rw [b3Forms_fderiv_tr_self_complex (mem_chart_target E x)] at hc
  have hcoord : b3Forms_tr x z (chartAt E x x) = chartAt E z x := by
    change chartAt E z ((chartAt E x).symm (chartAt E x x)) = _
    rw [(chartAt E x).left_inv (mem_chart_source E x)]
  rw [hcoord] at hc
  unfold b3ChartCovector
  rw [(chartAt E z).left_inv hx]
  exact congrArg (b3Forms_holCLM θ x)
    (congrArg (fun L : E →L[ℂ] E ↦ L v) hc.symm)

#print axioms b3ChartCovector_transport

end HodgeLean.Foundations.Curves.AbelAdapter.StageTwo
