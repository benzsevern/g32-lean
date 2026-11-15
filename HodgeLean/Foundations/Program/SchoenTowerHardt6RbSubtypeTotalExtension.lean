import Mathlib.Topology.ContinuousOn

/-! Continuous subtype maps have total representatives continuous on their actual domain. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_subtype_total_extension {E F : Type*}
    [TopologicalSpace E] [TopologicalSpace F] [Zero F]
    (S : Set E) (f : S → F) (hf : Continuous f) :
    ∃ g : E → F, ContinuousOn g S ∧ ∀ x : S, g x.val = f x := by
  classical
  let g : E → F := fun x => if hx : x ∈ S then f ⟨x, hx⟩ else 0
  have he : ∀ x : S, g x.val = f x := fun x => dif_pos x.property
  refine ⟨g, ?_, he⟩
  apply continuousOn_iff_continuous_restrict.mpr
  convert hf using 1
  funext x
  exact he x

end HodgeLean.Foundations.Program
