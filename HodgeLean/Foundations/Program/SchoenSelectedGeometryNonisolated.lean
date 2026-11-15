import HodgeLean.Foundations.Program.SchoenSelectedGeometryUnramifiedInverse

noncomputable section
open Set Topology Filter
open scoped Topology
namespace HodgeLean.Foundations.Program

/-- Every point of a space homeomorphic to a complex curve is nonisolated.
Source: complex coordinate charts and the nonisolated topology of the complex line. -/
theorem s0_curve_model_punctured_neBot
    {C D : Type*} [TopologicalSpace C] [ChartedSpace ℂ C]
    [TopologicalSpace D] (e : C ≃ₜ D) (y : D) : Filter.NeBot (𝓝[≠] y) := by
  let x := e.symm y
  have hx : Filter.NeBot (𝓝[≠] x) := by
    constructor
    intro hbot
    have hs : IsOpen ({x} : Set C) := (isOpen_singleton_iff_punctured_nhds x).mpr hbot
    let c := chartAt ℂ x
    have hcs : ({x} : Set C) ⊆ c.source := Set.singleton_subset_iff.mpr (mem_chart_source ℂ x)
    have ho := c.isOpen_image_of_subset_source hs hcs
    have hco : IsOpen ({c x} : Set ℂ) := by simpa using ho
    exact not_isOpen_singleton (c x) hco
  letI := hx
  have hm : Filter.NeBot (Filter.map e (𝓝[≠] x)) := inferInstance
  rwa [e.map_punctured_nhds_eq, Homeomorph.apply_symm_apply] at hm

#print axioms s0_curve_model_punctured_neBot
end HodgeLean.Foundations.Program
