import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Topology.Separation.Basic

/-! # Derivatives of local lifts with discrete differences -/
set_option maxHeartbeats 200000
open Filter Topology
namespace HodgeLean.Foundations.Program.G32Native

/-- A continuous function whose values locally lie in a specified discrete
subset retains its original point value on a neighborhood. -/
theorem continuousAt_eventually_constant_of_mem_discrete
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} {x : X} {S : Set Y} (hf : ContinuousAt f x) (hS : IsDiscrete S)
    (hm : ∀ᶠ z in 𝓝 x, f z ∈ S) : f =ᶠ[𝓝 x] fun _ => f x := by
  have hx : f x ∈ S := hm.self_of_nhds
  obtain ⟨U, hU, hUS⟩ := isOpen_inter_eq_singleton_of_mem_discrete hS hx
  have hxU : f x ∈ U := by
    have h : f x ∈ U ∩ S := by rw [hUS]; exact Set.mem_singleton _
    exact h.1
  filter_upwards [hf (hU.mem_nhds hxU), hm] with z hzU hzS
  have hz : f z ∈ U ∩ S := ⟨hzU, hzS⟩
  rw [hUS] at hz
  exact Set.mem_singleton_iff.mp hz

/-- Differentiable local lifts whose original difference locally lies in
a specified discrete subset have the same original derivative. -/
theorem fderiv_eq_of_sub_mem_discrete
    {K X E : Type*} [NontriviallyNormedField K]
    [NormedAddCommGroup X] [NormedSpace K X] [NormedAddCommGroup E] [NormedSpace K E]
    {f g : X → E} {x : X} {S : Set E}
    (hf : DifferentiableAt K f x) (hg : DifferentiableAt K g x) (hS : IsDiscrete S)
    (hm : ∀ᶠ z in 𝓝 x, f z - g z ∈ S) : fderiv K f x = fderiv K g x := by
  have he := continuousAt_eventually_constant_of_mem_discrete
    (hf.continuousAt.sub hg.continuousAt) hS hm
  have hd : fderiv K (f - g) x = 0 := by
    rw [he.fderiv_eq, fderiv_const_apply]
  rw [fderiv_sub hf hg] at hd
  exact sub_eq_zero.mp hd

#print axioms fderiv_eq_of_sub_mem_discrete
#print axioms continuousAt_eventually_constant_of_mem_discrete
end HodgeLean.Foundations.Program.G32Native
