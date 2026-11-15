import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.NormalizationCoefficientEquiv
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageThree.Basic

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- Restriction to an actual affine chart retains the original coefficient ring, the field point and the normalization coefficient square. -/
theorem affine_normalization_restriction
    {A L : Type} [CommRing A] [Field L] {Y : Scheme}
    (η : Spec ↧L ⟶ Y) [QuasiCompact η] [QuasiSeparated η]
    (j : Spec ↧A ⟶ Y) [IsOpenImmersion j]
    (f : A →+* L) (hf : Spec.map (CommRingCat.ofHom f) ≫ j = η) :
    ∃ E : pullback η.fromNormalization j ≅ Spec ↧(normalizedChart f),
      StageThree.restrictedFieldPoint η j (Spec.map (CommRingCat.ofHom f)) hf ≫ E.hom =
        Spec.map (CommRingCat.ofHom (normalizedChart f).subtype) ∧
      E.hom ≫ Spec.map (CommRingCat.ofHom (StageTwo.integralCoeff f)) =
        pullback.snd η.fromNormalization j := by
  let q := Spec.map (CommRingCat.ofHom f)
  let e : Γ(Spec ↧A, ⊤) ≃+* A :=
    (Scheme.ΓSpecIso ↧A).commRingCatIsoToRingEquiv
  have he : f.comp e.toRingHom = StageThree.fieldCoeff q := by
    apply CommRingCat.hom_ext_iff.mp
    apply Spec.map_injective
    change Spec.map (CommRingCat.ofHom (f.comp e.toRingHom)) =
      Spec.map (CommRingCat.ofHom (StageThree.fieldCoeff q))
    rw [StageThree.fieldCoeff_spec]
    change Spec.map ((Scheme.ΓSpecIso ↧A).hom ≫ CommRingCat.ofHom f) = _
    rw [Spec.map_comp, SpecMap_ΓSpecIso_hom, Scheme.toSpecΓ_naturality]
  let eN := normalizationCoefficientEquiv (StageThree.fieldCoeff q) f e he
  obtain ⟨E, hE, hbase, _⟩ := StageThree.affine_restriction_aux η j q hf
  let N := Scheme.Spec.mapIso eN.toCommRingCatIso.op
  refine ⟨E ≪≫ N.symm, ?_, ?_⟩
  · change _ ≫ E.hom ≫ N.inv = _
    rw [← Category.assoc, hE]
    change Spec.map (CommRingCat.ofHom (normalizedChart (StageThree.fieldCoeff q)).subtype) ≫
      Spec.map (CommRingCat.ofHom eN.symm.toRingHom) = _
    rw [← Spec.map_comp]
    rfl
  · change E.hom ≫ N.inv ≫ Spec.map (CommRingCat.ofHom (StageTwo.integralCoeff f)) = _
    have hcoeff : N.inv ≫ Spec.map (CommRingCat.ofHom (StageTwo.integralCoeff f)) =
        Spec.map (CommRingCat.ofHom (StageTwo.integralCoeff (StageThree.fieldCoeff q))) ≫
          Spec.map (Scheme.ΓSpecIso ↧A).inv := by
      change Spec.map (CommRingCat.ofHom eN.symm.toRingHom) ≫ _ = _
      rw [← Spec.map_comp, ← Spec.map_comp]
      congr 1
      ext a
      change f a = StageThree.fieldCoeff q (e.symm a)
      rw [← he]
      exact (congrArg f (e.apply_symm_apply a)).symm
    rw [hcoeff, ← Category.assoc, hbase, Category.assoc]
    rw [← SpecMap_ΓSpecIso_hom]
    rw [← Spec.map_comp]
    simp only [Iso.inv_hom_id, Spec.map_id, Category.comp_id]

end AlgebraicGeometry.RamifiedNormalization.StageFour
