import Mathlib.Topology.IsLocalHomeomorph

/-! # Locally constant lifts of a fixed quotient value -/
open Filter
open scoped Topology
namespace HodgeLean.Foundations.Program.G32Native

/-- A continuous lift of a fixed value through a local homeomorphism is locally constant. -/
theorem local_homeomorph_lift_eventually_constant
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (q : Y → Z) (hq : IsLocalHomeomorph q) {f : X → Y} {x : X}
    (hf : ContinuousAt f x) (he : ∀ᶠ y in 𝓝 x, q (f y) = q (f x)) :
    ∀ᶠ y in 𝓝 x, f y = f x := by
  obtain ⟨e, hx, hqe⟩ := hq (f x)
  filter_upwards [hf.eventually (e.open_source.mem_nhds hx), he] with y hy hey
  apply e.injOn hy hx
  rwa [← hqe]

#print axioms local_homeomorph_lift_eventually_constant
end HodgeLean.Foundations.Program.G32Native
