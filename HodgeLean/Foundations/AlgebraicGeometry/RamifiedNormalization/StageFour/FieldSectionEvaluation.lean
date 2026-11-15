import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageThree.Defs

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- A literal affine field point evaluates the corresponding global section at its original field value. -/
theorem field_coefficient_spec_map_value
    {A L : Type} [CommRing A] [Field L] (f : A →+* L) (a : A) :
    StageThree.fieldCoeff (Spec.map (CommRingCat.ofHom f)) ((Scheme.ΓSpecIso ↧A).inv a) = f a := by
  have he : (Scheme.ΓSpecIso ↧A).inv ≫ (Spec.map (CommRingCat.ofHom f)).appTop ≫
      (Scheme.ΓSpecIso ↧L).hom = CommRingCat.ofHom f := by
    rw [← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
  exact congrArg (fun q : CommRingCat.of A ⟶ CommRingCat.of L => q.hom a) he

end AlgebraicGeometry.RamifiedNormalization.StageFour
