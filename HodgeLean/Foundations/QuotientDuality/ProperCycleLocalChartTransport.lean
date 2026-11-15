import HodgeLean.Foundations.QuotientDuality.ProperCycleChartNeighborhood

/-! # Literal compressed charts transported along actual local homeomorphisms -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- Transporting a chart wholly inside a local homeomorphism target retains its actual coordinate radius.
Source: Hatcher, Algebraic Topology, section 3.3, chart-local orientation transport.
HC no distance; AV milestone no distance. -/
lemma properCycle_chart_radius_local_transport
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (d : ℕ)
    (H : OpenPartialHomeomorph X Y) (e : OpenPartialHomeomorph Y (Fin d → ℂ))
    (he : e.source ⊆ H.target) (x : X) (hx : x ∈ H.source) (hxe : H x ∈ e.source) :
    chartRadius d (H.trans e) x (show x ∈ (H.trans e).source from ⟨hx, hxe⟩) =
      chartRadius d e (H x) hxe := by
  have htarget : (H.trans e).target = e.target := by
    ext t
    change t ∈ e.target ∩ e.symm ⁻¹' H.target ↔ t ∈ e.target
    exact ⟨fun h => h.1, fun h => ⟨h, he (e.map_target h)⟩⟩
  simp only [chartRadius, htarget, OpenPartialHomeomorph.trans_apply]

/-- An actual local homeomorphism intertwines the original compressed models of a transported complex chart.
Source: Hatcher, Algebraic Topology, section 3.3, local chart orientation transport.
HC no distance; AV milestone no distance. -/
lemma properCycle_chart_model_local_transport
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (d : ℕ)
    (H : OpenPartialHomeomorph X Y) (e : OpenPartialHomeomorph Y (Fin d → ℂ))
    (he : e.source ⊆ H.target) (x : X) (hx : x ∈ H.source) (hxe : H x ∈ e.source)
    (t : Fin d → ℂ) :
    H (chartModelEmbedding d (H.trans e) x
      (show x ∈ (H.trans e).source from ⟨hx, hxe⟩) t) =
      chartModelEmbedding d e (H x) hxe t := by
  have hr := properCycle_chart_radius_local_transport d H e he x hx hxe
  change H (H.symm (e.symm
    (OpenPartialHomeomorph.univBall ((H.trans e) x)
      (chartRadius d (H.trans e) x ⟨hx, hxe⟩) t))) = _
  rw [hr]
  change H (H.symm (chartModelEmbedding d e (H x) hxe t)) = _
  exact H.right_inv (he (properCycle_chart_model_mem_source d e (H x) hxe t))

end HodgeLean.Foundations.QuotientDuality
