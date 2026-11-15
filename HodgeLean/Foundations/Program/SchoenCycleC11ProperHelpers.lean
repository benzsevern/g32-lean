import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.Order.Compact

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Topology Filter
open scoped NNReal
namespace HodgeLean.Foundations.Program

/-- Continuous coordinate bounds on a closed function-space model give properness.
Source: Mathlib, isProperMap_iff_ultrafilter_of_t2 and compactness of complex closed balls. -/
theorem s2e_c11_proper_of_coordinate_bounds
    {X Y I : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    (e : X → I → ℂ) (he : IsClosedEmbedding e)
    (f : X → Y) (hf : Continuous f)
    (hbound : ∀ i, ∃ c : Y → ℝ≥0, Continuous c ∧ ∀ x, ‖e x i‖₊ ≤ c (f x)) :
    IsProperMap f := by
  classical
  refine isProperMap_iff_ultrafilter_of_t2.mpr ⟨hf, ?_⟩
  intro 𝒰 y hy
  have hcoord (i : I) : ∃ z : ℂ,
      Tendsto (fun x => e x i) (𝒰 : Filter X) (𝓝 z) := by
    obtain ⟨c, hc, hcb⟩ := hbound i
    have hlim := hc.continuousAt.tendsto.comp hy
    have hlt : ∀ᶠ x in (𝒰 : Filter X), c (f x) < c y + 1 :=
      hlim.eventually_lt_const (lt_add_one (c y))
    have hball : ∀ᶠ x in (𝒰 : Filter X),
        e x i ∈ Metric.closedBall (0 : ℂ) ((c y + 1 : ℝ≥0) : ℝ) := by
      filter_upwards [hlt] with x hx
      rw [Metric.mem_closedBall, dist_zero_right]
      exact_mod_cast (hcb x).trans hx.le
    obtain ⟨z, _, hz⟩ := (isCompact_closedBall (0 : ℂ) ((c y + 1 : ℝ≥0) : ℝ)).ultrafilter_le_nhds'
      (𝒰.map (fun x => e x i)) hball
    exact ⟨z, hz⟩
  choose z hz using hcoord
  have hlim : Tendsto e (𝒰 : Filter X) (𝓝 z) := tendsto_pi_nhds.mpr hz
  have hmem : z ∈ Set.range e := he.isClosed_range.mem_of_tendsto hlim
    (Eventually.of_forall (fun x => ⟨x, rfl⟩))
  obtain ⟨x, hx⟩ := hmem
  refine ⟨x, ?_⟩
  have ht : Tendsto (id : X → X) (𝒰 : Filter X) (𝓝 x) :=
    he.tendsto_nhds_iff.mpr (hx ▸ hlim)
  exact ht

end HodgeLean.Foundations.Program
