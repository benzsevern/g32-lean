import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Tactic.FunProp

/-! Actual ambient restrictions of homeomorphisms to corresponding subsets. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_ambient_restriction {E F : Type*}
    [TopologicalSpace E] [TopologicalSpace F]
    (A S : Set E) (B T : Set F) (hSA : S ⊆ A) (hTB : T ⊆ B)
    (h : A ≃ₜ B) (hmem : ∀ x : A, x.val ∈ S ↔ (h x).val ∈ T) :
    ∃ e : S ≃ₜ T,
      (∀ x, (e x).val = (h ⟨x.val, hSA x.property⟩).val) ∧
      (∀ y, (e.symm y).val = (h.symm ⟨y.val, hTB y.property⟩).val) := by
  let f : S → T := fun x => ⟨(h ⟨x.val, hSA x.property⟩).val,
    (hmem _).mp x.property⟩
  let g : T → S := fun y => ⟨(h.symm ⟨y.val, hTB y.property⟩).val,
    (hmem _).mpr (by simpa only [h.apply_symm_apply] using y.property)⟩
  have hleft : Function.LeftInverse g f := by
    intro x
    apply Subtype.ext
    change (h.symm (h ⟨x.val, hSA x.property⟩)).val = x.val
    rw [h.symm_apply_apply]
  have hright : Function.RightInverse g f := by
    intro y
    apply Subtype.ext
    change (h (h.symm ⟨y.val, hTB y.property⟩)).val = y.val
    rw [h.apply_symm_apply]
  let e : S ≃ₜ T :=
    { toFun := f, invFun := g, left_inv := hleft, right_inv := hright
      continuous_toFun := by dsimp [f]; fun_prop
      continuous_invFun := by dsimp [g]; fun_prop }
  exact ⟨e, fun _ => rfl, fun _ => rfl⟩

end HodgeLean.Foundations.Program
