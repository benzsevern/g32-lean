import Mathlib.Topology.Homeomorph.Defs

/-! Recover the actual marked preimage from an exact selected-image equation. -/
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_mark_selection_preimage {E F : Type*}
    [TopologicalSpace E] [TopologicalSpace F]
    (A : Set E) (B M : Set F) (h : A ≃ₜ B) (U : Set A)
    (hsel : B ∩ M = (fun x : A => (h x).val) '' U) (x : A) :
    (h x).val ∈ M ↔ x ∈ U := by
  constructor
  · intro hx
    have him : (h x).val ∈ (fun y : A => (h y).val) '' U := hsel ▸ ⟨(h x).property, hx⟩
    obtain ⟨y, hy, hyx⟩ := him
    have he : y = x := h.injective (Subtype.ext hyx)
    exact he ▸ hy
  · intro hx
    have hm : (h x).val ∈ B ∩ M := hsel.symm ▸ Set.mem_image_of_mem _ hx
    exact hm.2

end HodgeLean.Foundations.Program
