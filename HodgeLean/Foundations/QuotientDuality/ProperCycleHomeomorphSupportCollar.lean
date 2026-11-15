import HodgeLean.Foundations.QuotientDuality.ProperCycleCollarRetractionOnSupport

/-! # Actual collar data pulled back through an original ambient homeomorphism
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory TopologicalSpace
namespace HodgeLean.Foundations.QuotientDuality

/-- Pull the actual neighborhood, retraction and deformation back through a support-preserving ambient homeomorphism.
Source: ProperCycleSupportCollar; Hatcher, Algebraic Topology, section 0, conjugation of a deformation retract by a homeomorphism.
HC no distance; AV milestone no distance. -/
def ProperCycleSupportCollar.comapHomeomorph
    {X Y : TopCat.{0}} {S : Set X} {T : Set Y}
    (C : ProperCycleSupportCollar Y T) (e : X ≃ₜ Y)
    (he : ∀ x, x ∈ S ↔ e x ∈ T) : ProperCycleSupportCollar X S := by
  let U : Set X := e ⁻¹' C.neighborhood
  have hSU : S ⊆ U := fun x hx => C.contains ((he x).mp hx)
  let i : TopCat.of S ⟶ TopCat.of U :=
    TopCat.ofHom ⟨fun s => ⟨s.val, hSU s.property⟩, continuous_subtype_val.subtype_mk _⟩
  let u : C(TopCat.of U, C.neighborhood) :=
    ⟨fun x => ⟨e x.val, x.property⟩, (e.continuous.comp continuous_subtype_val).subtype_mk _⟩
  let r : TopCat.of U ⟶ TopCat.of S := TopCat.ofHom
    ⟨fun x => ⟨e.symm (C.retraction (u x)).val, by
      apply (he _).mpr
      rw [e.apply_symm_apply]
      exact (C.retraction (u x)).property⟩, by fun_prop⟩
  have hir : i ≫ r = 𝟙 (TopCat.of S) := by
    ext s : 1
    apply Subtype.ext
    change e.symm (C.retraction (u (i s))).val = s.val
    rw [C.retraction_on_support (u (i s)) ((he s.val).mp s.property)]
    exact e.symm_apply_apply s.val
  let H : TopCat.Homotopy (𝟙 (TopCat.of U)) (r ≫ i) :=
    { toFun := fun tx => ⟨e.symm (C.deformation (tx.1, u tx.2)).val, by
        change e (e.symm (C.deformation (tx.1, u tx.2)).val) ∈ C.neighborhood
        rw [e.apply_symm_apply]
        exact (C.deformation (tx.1, u tx.2)).property⟩
      continuous_toFun := by fun_prop
      map_zero_left := by
        intro x
        apply Subtype.ext
        change e.symm (C.deformation (0, u x)).val = x.val
        exact (congrArg (fun v : C.neighborhood => e.symm v.val)
          (C.deformation.map_zero_left (u x))).trans (e.symm_apply_apply x.val)
      map_one_left := by
        intro x
        apply Subtype.ext
        change e.symm (C.deformation (1, u x)).val = e.symm (C.retraction (u x)).val
        exact (congrArg (fun v : C.neighborhood => e.symm v.val)
          (C.deformation.map_one_left (u x))).trans
            (congrArg e.symm (ConcreteCategory.congr_hom C.inclusion_factor (C.retraction (u x)))) }
  exact ⟨U, C.isOpen.preimage e.continuous, hSU, i, r, by ext s; rfl, hir, H⟩

example {X Y : TopCat.{0}} {S : Set X} {T : Set Y}
    (C : ProperCycleSupportCollar Y T) (e : X ≃ₜ Y)
    (he : ∀ x, x ∈ S ↔ e x ∈ T) (x : X) :
    x ∈ (C.comapHomeomorph e he).neighborhood ↔ e x ∈ C.neighborhood := Iff.rfl

end HodgeLean.Foundations.QuotientDuality
