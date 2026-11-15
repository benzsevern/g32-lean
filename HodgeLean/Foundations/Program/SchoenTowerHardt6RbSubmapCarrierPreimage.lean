import Mathlib.Topology.Homeomorph.Defs

/-! A global homeomorphism extending an actual cell homeomorphism has the exact cell carrier preimage. -/
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_submap_carrier_preimage {E F : Type*}
    [TopologicalSpace E] [TopologicalSpace F]
    (A C : Set E) (B T : Set F) (hCA : C ⊆ A)
    (H : A ≃ₜ B) (e : C ≃ₜ T)
    (he : ∀ x : C, (H ⟨x.val, hCA x.property⟩).val = (e x).val) :
    ∀ x : A, x.val ∈ C ↔ (H x).val ∈ T := by
  intro x
  constructor
  · intro hx
    rw [he ⟨x.val, hx⟩]
    exact (e ⟨x.val, hx⟩).property
  · intro hx
    let y := e.symm ⟨(H x).val, hx⟩
    have hey : (H ⟨y.val, hCA y.property⟩).val = (H x).val :=
      (he y).trans (congrArg Subtype.val (e.apply_symm_apply ⟨(H x).val, hx⟩))
    have hyx : y.val = x.val := congrArg Subtype.val (H.injective (Subtype.ext hey))
    exact hyx ▸ y.property

end HodgeLean.Foundations.Program
