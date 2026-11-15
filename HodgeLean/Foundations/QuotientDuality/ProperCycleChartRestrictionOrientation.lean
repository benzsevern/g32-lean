import HodgeLean.RealDefs.Port.AlgebraicTopology.LocalHomology.ChartFundamentalClassInvariance

/-! # Literal chart orientation under original open restrictions -/

noncomputable section
set_option maxHeartbeats 400000
open AlgebraicTopology.Singular Filter Topology
namespace HodgeLean.Foundations.QuotientDuality

/-- Restricting an original chart to an original open neighborhood retains its exact normalized local orientation class.
Source: localClassOfChart_eq_of_analyticAt_transition; OpenPartialHomeomorph.right_inv.
HC no distance; AV milestone no distance. -/
theorem properCycle_chart_restr_open_local_class
    {M : Type} [TopologicalSpace M] (d : ℕ)
    (e : OpenPartialHomeomorph M (Fin d → ℂ)) (V : Set M) (hV : IsOpen V)
    (x : M) (hx : x ∈ e.source) (hxV : x ∈ V) :
    localClassOfChart d (e.restrOpen V hV) x ⟨hx, hxV⟩ = localClassOfChart d e x hx := by
  have ha : AnalyticAt ℂ (fun v => e (e.symm v)) (e x) := by
    apply AnalyticAt.congr analyticAt_id
    filter_upwards [e.open_target.mem_nhds (e.map_source hx)] with v hv
    exact (e.right_inv hv).symm
  exact localClassOfChart_eq_of_analyticAt_transition d (e.restrOpen V hV) e x ⟨hx, hxV⟩ hx ha ha

end HodgeLean.Foundations.QuotientDuality
