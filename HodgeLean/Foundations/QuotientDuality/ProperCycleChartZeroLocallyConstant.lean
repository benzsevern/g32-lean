import HodgeLean.Foundations.QuotientDuality.ProperCycleChartLocalScalar
import Mathlib.Topology.LocallyConstant.Basic

/-! # Actual top homology point vanishing in an original complex chart
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicTopology.Singular TopologicalSpace
namespace HodgeLean.Foundations.QuotientDuality

/-- Vanishing of an original ordinary top homology class at a point is locally constant on the source of every original complex chart.
Source: properCycle_chart_local_scalar; localClassOfChart_ne_zero; IsLocallyConstant.iff_exists_open.
HC no distance; AV milestone no distance. -/
lemma properCycle_chart_zero_locally_constant
    (X : TopCat.{0}) [T2Space X] (d : ℕ)
    (e : OpenPartialHomeomorph X (Fin d → ℂ)) (c : Homology ℚ X (2*d)) :
    IsLocallyConstant (fun x : e.source => localOrientation X (2*d) c x.val = 0) := by
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro x
  obtain ⟨W, hxW, hW, q, hq⟩ := properCycle_chart_local_scalar X d e c x.val x.property
  have hz (z : X) (hz : z ∈ W) : localOrientation X (2*d) c z = 0 ↔ q = 0 := by
    rw [hq z hz]
    exact smul_eq_zero_iff_left (localClassOfChart_ne_zero d e z (hW hz))
  refine ⟨Subtype.val ⁻¹' (W : Set X), W.isOpen.preimage continuous_subtype_val, hxW, ?_⟩
  intro y hy
  exact propext ((hz y.val hy).trans (hz x.val hxW).symm)

end HodgeLean.Foundations.QuotientDuality
