import Mathlib.Topology.OpenPartialHomeomorph.Continuity

/-! # The inverse of a sheet expressed in the retained target chart -/
noncomputable section
open Filter
open scoped Topology
namespace HodgeLean.Foundations.Program.G32Native
variable {X Y E : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace E]

/-- A sheet chart equal to the target coordinates has the original target inverse germ. -/
theorem sheet_chart_inverse_germ (f : X → Y) (x : X)
    (e : OpenPartialHomeomorph X E) (C : OpenPartialHomeomorph Y E)
    (he : x ∈ e.source) (hC : f x ∈ C.source) (hf : ContinuousAt f x)
    (hcoord : e =ᶠ[𝓝 x] C ∘ f) :
    f ∘ e.symm =ᶠ[𝓝 (e x)] C.symm := by
  have hex : e x = C (f x) := hcoord.self_of_nhds
  have hi : Tendsto e.symm (𝓝 (e x)) (𝓝 x) := by
    simpa only [e.left_inv he] using (e.continuousAt_symm (e.map_source he)).tendsto
  have htarget := e.open_target.mem_nhds (e.map_source he)
  have hsource := hi (hf (C.open_source.mem_nhds hC))
  filter_upwards [hi hcoord, htarget, hsource] with z hz hze hzC
  change f (e.symm z) = C.symm z
  have hz' : z = C (f (e.symm z)) := (e.right_inv hze).symm.trans hz
  exact ((congrArg C.symm hz').trans (C.left_inv hzC)).symm

#print axioms sheet_chart_inverse_germ
end HodgeLean.Foundations.Program.G32Native
