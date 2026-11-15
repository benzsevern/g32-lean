import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.ActualTwoChartOver
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.OverlapSectionProduct
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.RestrictedAffineEvaluation
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.ReducedPointMorphismExt
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.ProjectiveLineReciprocalPoints

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- Reciprocal functions in the same original field glue the two actual normal-chart maps to the projective line. -/
theorem reciprocal_projective_chart_gluing
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
    (t : A) (s : B) (hts : f t * g s = 1) :
    ∃! F : X ⟶ projectiveLine,
      jA ≫ F = projectiveLineChart 1 t ∧ jB ≫ F = projectiveLineChart 0 s := by
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
  have hsections := overlap_sections_mul_eq_one X.left η jA.left jB.left f g hf hg t s hts
  have hmaps : pA ≫ projectiveLineChart 1 t = pB ≫ projectiveLineChart 0 s := by
    apply reduced_complex_morphism_ext Q projectiveLine
    intro p
    rw [Point.map_comp_apply, Point.map_comp_apply]
    apply projectiveLineChart_reciprocal_points t s (Point.map pA p) (Point.map pB p)
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
        ((pullback.fst jA.left jB.left).appTop ((Scheme.ΓSpecIso ↧A).inv t)) *
      StageThree.fieldCoeff p.left
        ((pullback.snd jA.left jB.left).appTop ((Scheme.ΓSpecIso ↧B).inv s)) = 1 := by
      simpa only [map_mul, map_one, Over.left, Over.mk, CostructuredArrow.mk] using he
    exact (congrArg₂ (fun a b : ℂ => a * b) heA heB).symm.trans hp
  apply glue_two_actual_open_charts_over X _ _ projectiveLine jA jB hcover
    (projectiveLineChart 1 t) (projectiveLineChart 0 s)
  exact congrArg (fun m => m.left) hmaps

end AlgebraicGeometry.RamifiedNormalization.StageFour
