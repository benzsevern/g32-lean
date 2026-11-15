import Mathlib.Topology.Homeomorph.Lemmas

/-! Homeomorphisms on the actual marked subsets. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.QuotientDuality

/-- Restrict the specified ambient homeomorphism to its exactly corresponding marked subsets. -/
def persistenceMarkedHomeomorph
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (A : Set X) (B : Set Y) (hmark : ∀ x, e x ∈ B ↔ x ∈ A) : A ≃ₜ B where
  toFun a := ⟨e a.val, (hmark a.val).mpr a.property⟩
  invFun b := ⟨e.symm b.val, (hmark (e.symm b.val)).mp (by
    rw [e.apply_symm_apply]
    exact b.property)⟩
  left_inv a := Subtype.ext (e.symm_apply_apply a.val)
  right_inv b := Subtype.ext (e.apply_symm_apply b.val)
  continuous_toFun := (e.continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (e.symm.continuous.comp continuous_subtype_val).subtype_mk _

end HodgeLean.Foundations.QuotientDuality
