import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.ActualTwoChartOver
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.OverlapSectionEquality
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.RestrictedAffineEvaluation
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.ReducedPointMorphismExt
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.AffineLineParameter

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- Equal original-field selector values glue their actual affine-line morphisms on the two normal charts. -/
theorem equal_field_affine_parameter_gluing
    {A B L : Type} [CommRing A] [CommRing B] [Algebra ℂ A] [Algebra ℂ B] [Field L]
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [LocallyOfFiniteType X.hom]
    (η : Spec ↧L ⟶ X.left) [IsDominant η] [QuasiCompact η]
    (jA : Over.mk (ComplexPoint.affineSpecStructureMap A) ⟶ X)
    (jB : Over.mk (ComplexPoint.affineSpecStructureMap B) ⟶ X)
    [IsOpenImmersion jA.left] [IsOpenImmersion jB.left]
    (hcover : ∀ x : X.left, (∃ a, jA.left a = x) ∨ ∃ b, jB.left b = x)
    (f : A →+* L) (g : B →+* L)
    (hf : Spec.map (CommRingCat.ofHom f) ≫ jA.left = η)
    (hg : Spec.map (CommRingCat.ofHom g) ≫ jB.left = η)
    (t : A) (s : B) (hts : f t = g s) :
    ∃! F : X ⟶ (Over.mk (ComplexPoint.affineSpecStructureMap (Polynomial ℂ))),
      jA ≫ F = affineLineParameter t ∧ jB ≫ F = affineLineParameter s := by
  have hA : jA.left ≫ X.hom = ComplexPoint.affineSpecStructureMap A := jA.w
  have hB : jB.left ≫ X.hom = ComplexPoint.affineSpecStructureMap B := jB.w
  let Q : Over (Spec ↧ℂ) := Over.mk
    (pullback.fst jA.left jB.left ≫ ComplexPoint.affineSpecStructureMap A)
  let pA : Q ⟶ Over.mk (ComplexPoint.affineSpecStructureMap A) :=
    Over.homMk (pullback.fst jA.left jB.left) rfl
  let pB : Q ⟶ Over.mk (ComplexPoint.affineSpecStructureMap B) :=
    Over.homMk (pullback.snd jA.left jB.left) (by
      have he := congrArg (fun m => m ≫ X.hom)
        (pullback.condition (f := jA.left) (g := jB.left))
      simpa only [Q, Over.left, Over.hom, Over.mk, CostructuredArrow.mk, Category.assoc, hA, hB] using he.symm)
  let k := pullback.fst jA.left jB.left ≫ jA.left
  haveI : IsOpenImmersion k := by dsimp [k]; infer_instance
  haveI : IsReduced Q.left := isReduced_of_isOpenImmersion k
  have hk : k ≫ X.hom = Q.hom := by
    dsimp only [k]
    rw [Category.assoc, hA]
    rfl
  haveI : LocallyOfFiniteType Q.hom :=
    hk ▸ (inferInstance : LocallyOfFiniteType (k ≫ X.hom))
  have hsections := overlap_sections_eq_of_field_values X.left η jA.left jB.left f g hf hg t s hts
  haveI : LocallyOfFiniteType (Over.mk (ComplexPoint.affineSpecStructureMap (Polynomial ℂ))).hom := by
    change LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap ℂ (Polynomial ℂ))))
    apply (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  haveI : IsSeparated (Over.mk (ComplexPoint.affineSpecStructureMap (Polynomial ℂ))).hom := by
    change IsSeparated (Spec.map (CommRingCat.ofHom (algebraMap ℂ (Polynomial ℂ))))
    infer_instance
  have hmaps : pA ≫ affineLineParameter t = pB ≫ affineLineParameter s := by
    apply reduced_complex_morphism_ext Q (Over.mk (ComplexPoint.affineSpecStructureMap (Polynomial ℂ)))
    intro p
    rw [Point.map_comp_apply, Point.map_comp_apply]
    apply (ComplexPoint.affineSpecEquiv (Polynomial ℂ)).injective
    apply Polynomial.algHom_ext
    change ComplexPoint.affineSpecEquiv (Polynomial ℂ) (Point.map (affineLineParameter t) (Point.map pA p)) Polynomial.X =
      ComplexPoint.affineSpecEquiv (Polynomial ℂ) (Point.map (affineLineParameter s) (Point.map pB p)) Polynomial.X
    rw [affineLineParameter_coordinate, affineLineParameter_coordinate]
    have he := congrArg (StageThree.fieldCoeff p.left) hsections
    have heA : StageThree.fieldCoeff p.left
        ((pullback.fst jA.left jB.left).appTop ((Scheme.ΓSpecIso ↧A).inv t)) =
          ComplexPoint.affineSpecEquiv A (Point.map pA p) t :=
      field_coefficient_restricted_affine_section p.left (pullback.fst jA.left jB.left) t
    have heB : StageThree.fieldCoeff p.left
        ((pullback.snd jA.left jB.left).appTop ((Scheme.ΓSpecIso ↧B).inv s)) =
          ComplexPoint.affineSpecEquiv B (Point.map pB p) s :=
      field_coefficient_restricted_affine_section p.left (pullback.snd jA.left jB.left) s
    have hp : StageThree.fieldCoeff p.left
        ((pullback.fst jA.left jB.left).appTop ((Scheme.ΓSpecIso ↧A).inv t)) =
      StageThree.fieldCoeff p.left
        ((pullback.snd jA.left jB.left).appTop ((Scheme.ΓSpecIso ↧B).inv s)) := by
      simpa only [Over.left, Over.mk, CostructuredArrow.mk] using he
    exact heA.symm.trans (hp.trans heB)
  apply glue_two_actual_open_charts_over X _ _ (Over.mk (ComplexPoint.affineSpecStructureMap (Polynomial ℂ))) jA jB hcover
    (affineLineParameter t) (affineLineParameter s)
  exact congrArg (fun m => m.left) hmaps

end AlgebraicGeometry.RamifiedNormalization.StageFour
