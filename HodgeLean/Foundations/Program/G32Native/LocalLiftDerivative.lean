import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Topology.IsLocalHomeomorph

/-! # Derivatives of local lifts through additive local homeomorphisms -/
noncomputable section
open scoped Topology

namespace HodgeLean.Foundations.Program.G32Native

/-- Two continuous lifts through an additive local homeomorphism differ locally by a constant. -/
theorem local_lift_sub_eventually_constant
    {X V T : Type*} [TopologicalSpace X] [TopologicalSpace V]
    [AddCommGroup V] [IsTopologicalAddGroup V] [TopologicalSpace T] [AddCommGroup T]
    (q : V →+ T) (hq : IsLocalHomeomorph q) {f g : X → V} {x : X}
    (hf : ContinuousAt f x) (hg : ContinuousAt g x)
    (he : ∀ᶠ y in 𝓝 x, q (f y) = q (g y)) :
    ∀ᶠ y in 𝓝 x, f y - g y = f x - g x := by
  obtain ⟨e, hx, hqe⟩ := hq (f x - g x)
  have hs := (hf.sub hg).eventually (e.open_source.mem_nhds hx)
  have hxq : q (f x) = q (g x) := he.self_of_nhds
  filter_upwards [hs, he] with y hy hey
  apply e.injOn hy hx
  rw [← hqe]
  simp only [Pi.sub_apply, map_sub, hey, hxq, sub_self]

/-- Equal quotient germs give equal derivatives of differentiable local lifts. -/
theorem local_lift_fderiv_eq
    {𝕜 E V T : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup V] [NormedSpace 𝕜 V]
    [TopologicalSpace T] [AddCommGroup T]
    (q : V →+ T) (hq : IsLocalHomeomorph q) {f g : E → V} {x : E}
    (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x)
    (he : ∀ᶠ y in 𝓝 x, q (f y) = q (g y)) :
    fderiv 𝕜 f x = fderiv 𝕜 g x := by
  have hd := local_lift_sub_eventually_constant q hq hf.continuousAt hg.continuousAt he
  have heq : f =ᶠ[𝓝 x] fun y => g y + (f x - g x) := by
    filter_upwards [hd] with y hy
    exact (sub_eq_iff_eq_add.mp hy).trans (add_comm _ _)
  rw [heq.fderiv_eq, fderiv_add_const]

#print axioms local_lift_sub_eventually_constant
#print axioms local_lift_fderiv_eq
end HodgeLean.Foundations.Program.G32Native
