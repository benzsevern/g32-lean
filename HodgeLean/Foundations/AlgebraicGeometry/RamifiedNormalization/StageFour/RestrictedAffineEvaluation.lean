import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.FieldSectionEvaluation
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.FieldSectionRestriction

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- Evaluation of a restricted affine section is its original affine coordinate evaluation. -/
theorem field_coefficient_restricted_affine_section
    {A L : Type} [CommRing A] [Field L] {Q : Scheme}
    (z : Spec ↧L ⟶ Q) (f : Q ⟶ Spec ↧A) (a : A) :
    StageThree.fieldCoeff z (f.appTop ((Scheme.ΓSpecIso ↧A).inv a)) =
      (Spec.preimage (z ≫ f)).hom a := by
  change ((StageThree.fieldCoeff z).comp f.appTop.hom) _ = _
  rw [← field_coefficient_comp]
  have he := field_coefficient_spec_map_value (Spec.preimage (z ≫ f)).hom a
  simpa only [CommRingCat.ofHom_hom, Spec.map_preimage] using he

end AlgebraicGeometry.RamifiedNormalization.StageFour
