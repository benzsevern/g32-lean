import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageTwo.Defs

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- Changing the coefficient presentation preserves the integral elements in the original field, with their literal values. -/
def normalizationCoefficientEquiv
    {A B L : Type} [CommRing A] [CommRing B] [Field L]
    (f : A →+* L) (g : B →+* L) (e : A ≃+* B)
    (he : g.comp e.toRingHom = f) : normalizedChart f ≃+* normalizedChart g := by
  letI := f.toAlgebra
  letI := g.toAlgebra
  have hmem (x : L) : x ∈ normalizedChart f ↔ x ∈ normalizedChart g :=
    e.isIntegral_iff he x
  exact {
    toFun := fun x => ⟨x.val, (hmem x.val).mp x.property⟩
    invFun := fun x => ⟨x.val, (hmem x.val).mpr x.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_mul' := fun _ _ => rfl
    map_add' := fun _ _ => rfl }

end AlgebraicGeometry.RamifiedNormalization.StageFour
