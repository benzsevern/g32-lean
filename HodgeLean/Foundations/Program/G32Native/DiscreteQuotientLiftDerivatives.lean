import HodgeLean.Foundations.Program.G32Native.DiscreteLiftDerivatives
import Mathlib.Topology.DiscreteSubset
import Mathlib.GroupTheory.QuotientGroup.Defs

/-! # Original derivatives of local lifts through a discrete quotient -/
set_option maxHeartbeats 200000
open Filter Topology
namespace HodgeLean.Foundations.Program.G32Native

/-- Local lifts through the original discrete quotient have the same
original derivative in every specified continuous injective additive coordinate map. -/
theorem fderiv_eq_of_discrete_quotient_lifts
    {K X E H : Type*} [NontriviallyNormedField K]
    [NormedAddCommGroup X] [NormedSpace K X] [NormedAddCommGroup E] [NormedSpace K E]
    [AddCommGroup H] [TopologicalSpace H]
    (L : E →+ H) (hL : Continuous L) (hLi : Function.Injective L)
    (Λ : AddSubgroup H) [DiscreteTopology Λ]
    {f g : X → E} {x : X} (hf : DifferentiableAt K f x) (hg : DifferentiableAt K g x)
    (hq : (fun z => (QuotientAddGroup.mk (L (f z)) : H ⧸ Λ)) =ᶠ[𝓝 x]
      (fun z => (QuotientAddGroup.mk (L (g z)) : H ⧸ Λ))) :
    fderiv K f x = fderiv K g x := by
  have hΛ : IsDiscrete (Λ : Set H) := isDiscrete_iff_discreteTopology.mpr inferInstance
  have hS : IsDiscrete (L ⁻¹' (Λ : Set H)) := hΛ.preimage hL.continuousOn hLi
  apply fderiv_eq_of_sub_mem_discrete hf hg hS
  filter_upwards [hq] with z hz
  change L (f z - g z) ∈ Λ
  rw [map_sub]
  exact QuotientAddGroup.eq_iff_sub_mem.mp hz

#print axioms fderiv_eq_of_discrete_quotient_lifts
end HodgeLean.Foundations.Program.G32Native
