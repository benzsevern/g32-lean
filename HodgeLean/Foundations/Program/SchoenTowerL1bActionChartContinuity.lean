import HodgeLean.Foundations.Program.SchoenTowerL1bActionCenteredConjugacy

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter Topology
namespace HodgeLean.Foundations.Program

/-- A continuous map fixing a charted point is continuous in coordinates
at every point sufficiently near that coordinate center. -/
theorem s2v_l1b_action_chart_eventually_continuousAt
    {M : Type} [TopologicalSpace M] (C : OpenPartialHomeomorph M ℂ)
    (x : M) (hx : x ∈ C.source) (f : M → M) (hf : Continuous f) (hfix : f x = x) :
    ∀ᶠ z : ℂ in 𝓝 (C x), ContinuousAt (fun w => C (f (C.symm w))) z := by
  have hi := C.continuousAt_symm (C.map_source hx)
  have ht : Tendsto (fun z => f (C.symm z)) (𝓝 (C x)) (𝓝 x) := by
    simpa only [Function.comp_def, C.left_inv hx, hfix] using (hf.continuousAt.comp hi).tendsto
  filter_upwards [C.open_target.mem_nhds (C.map_source hx),
    ht.eventually (C.open_source.mem_nhds hx)] with z hz hzf
  have hfc : ContinuousAt (fun w => f (C.symm w)) z :=
    (show ContinuousAt f (C.symm z) from hf.continuousAt).comp (C.continuousAt_symm hz)
  simpa only [Function.comp_def] using ContinuousAt.comp (f := fun w : ℂ => f (C.symm w)) (g := fun y : M => C y) (C.continuousAt hzf) hfc

end HodgeLean.Foundations.Program
