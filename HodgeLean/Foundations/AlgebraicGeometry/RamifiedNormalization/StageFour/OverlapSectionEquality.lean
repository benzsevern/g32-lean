import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.FieldSectionEvaluation
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.FieldSectionRestriction
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- Equal original-field values identify the corresponding actual overlap sections. -/
theorem overlap_sections_eq_of_field_values
    {A B L : Type} [CommRing A] [CommRing B] [Field L]
    (X : Scheme.{0}) [IsIntegral X] (η : Spec ↧L ⟶ X) [IsDominant η] [QuasiCompact η]
    (jA : Spec ↧A ⟶ X) (jB : Spec ↧B ⟶ X) [IsOpenImmersion jA] [IsOpenImmersion jB]
    (f : A →+* L) (g : B →+* L)
    (hf : Spec.map (CommRingCat.ofHom f) ≫ jA = η)
    (hg : Spec.map (CommRingCat.ofHom g) ≫ jB = η)
    (t : A) (s : B) (hts : f t = g s) :
    (pullback.fst jA jB).appTop ((Scheme.ΓSpecIso ↧A).inv t) =
      (pullback.snd jA jB).appTop ((Scheme.ΓSpecIso ↧B).inv s) := by
  let Q := pullback jA jB
  let k := pullback.fst jA jB ≫ jA
  let q : Spec ↧L ⟶ Q := pullback.lift (Spec.map (CommRingCat.ofHom f))
    (Spec.map (CommRingCat.ofHom g)) (hf.trans hg.symm)
  have hqA : q ≫ pullback.fst jA jB = Spec.map (CommRingCat.ofHom f) := pullback.lift_fst _ _ _
  have hqB : q ≫ pullback.snd jA jB = Spec.map (CommRingCat.ofHom g) := pullback.lift_snd _ _ _
  have hqk : q ≫ k = η := by
    change q ≫ pullback.fst jA jB ≫ jA = _
    rw [← Category.assoc, hqA, hf]
  haveI : IsOpenImmersion k := by dsimp [k]; infer_instance
  haveI : IsReduced Q := isReduced_of_isOpenImmersion k
  haveI : IsDominant (q ≫ k) := hqk.symm ▸ inferInstance
  haveI : QuasiCompact (q ≫ k) := hqk.symm ▸ inferInstance
  haveI : IsDominant q := IsDominant.of_comp_of_isOpenImmersion q k
  haveI : QuasiCompact q := QuasiCompact.of_comp q k
  haveI : IsSchemeTheoreticallyDominant q := IsSchemeTheoreticallyDominant.of_isDominant q
  have hinj : Function.Injective (StageThree.fieldCoeff q) :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso ↧L).hom).injective.comp (q.app_injective ⊤)
  have hvalA : StageThree.fieldCoeff q
      ((pullback.fst jA jB).appTop ((Scheme.ΓSpecIso ↧A).inv t)) = f t := by
    change ((StageThree.fieldCoeff q).comp (pullback.fst jA jB).appTop.hom) _ = _
    rw [← field_coefficient_comp, hqA]
    exact field_coefficient_spec_map_value f t
  have hvalB : StageThree.fieldCoeff q
      ((pullback.snd jA jB).appTop ((Scheme.ΓSpecIso ↧B).inv s)) = g s := by
    change ((StageThree.fieldCoeff q).comp (pullback.snd jA jB).appTop.hom) _ = _
    rw [← field_coefficient_comp, hqB]
    exact field_coefficient_spec_map_value g s
  apply hinj
  rw [hvalA, hvalB, hts]

end AlgebraicGeometry.RamifiedNormalization.StageFour
