import HodgeLean.Foundations.Topology.RationalSheafComparisonResolution

/-! Integer-indexed resolution pullback with its augmentation normalization.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace HodgeLean.Topology.RationalSheafComparison

variable {X Y : TopCat.{0}} (f : X ⟶ Y)

/-- Source: Bredon, Sheaf Theory, second edition, II.4. -/
def resolutionPullbackMapInt :
    ((TopCat.Sheaf.pullback AddCommGrpCat.{0} f).mapHomologicalComplex (.up ℤ)).obj
      (resolution Y).cochainComplex ⟶ (resolution X).cochainComplex :=
  (HomologicalComplex.mapExtendCanonicalIso (TopCat.Sheaf.pullback AddCommGrpCat.{0} f)
    (resolution Y).cocomplex ComplexShape.embeddingUpNat).hom ≫
      HomologicalComplex.extendMap (resolutionPullbackMap f) ComplexShape.embeddingUpNat

/-- Source: Bredon, Sheaf Theory, second edition, II.4. -/
theorem resolutionPullbackMapInt_augmentation :
    ((TopCat.Sheaf.pullback AddCommGrpCat.{0} f).mapHomologicalComplex (.up ℤ)).map
        (resolution Y).ι' ≫ resolutionPullbackMapInt f =
      ((TopCat.Sheaf.pullback AddCommGrpCat.{0} f).mapCochainComplexSingleFunctor 0).hom.app
          (constants Y) ≫
        (CochainComplex.singleFunctor _ 0).map (pullbackConstantsIso f (AddCommGrpCat.of ℚ)).hom ≫
          (resolution X).ι' := by
  apply (cancel_epi (((TopCat.Sheaf.pullback AddCommGrpCat.{0} f).mapCochainComplexSingleFunctor 0).inv.app
    (constants Y))).mp
  rw [Iso.inv_hom_id_app_assoc]
  apply HomologicalComplex.Hom.ext
  funext j
  by_cases hj : j = 0
  · subst j
    have hn := congrArg (fun k => k.f 0) (resolutionPullbackMap_augmentation f)
    simp only [resolutionPullbackAugmentation, HomologicalComplex.comp_f,
      Functor.mapHomologicalComplex_map_f,
      HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
      HomologicalComplex.single_map_f_self] at hn
    simp only [resolutionPullbackMapInt, HomologicalComplex.comp_f,
      Functor.mapHomologicalComplex_map_f, InjectiveResolution.ι'_f_zero,
      Functor.mapCochainComplexSingleFunctor,
      HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
      HomologicalComplex.single_map_f_self,
      HomologicalComplex.mapExtendCanonicalIso_hom_f
        (TopCat.Sheaf.pullback AddCommGrpCat.{0} f) (resolution Y).cocomplex
        ComplexShape.embeddingUpNat (i := 0) (j := 0) rfl,
      HomologicalComplex.extendMap_f (resolutionPullbackMap f)
        ComplexShape.embeddingUpNat (i := 0) (i' := 0) rfl,
      InjectiveResolution.cochainComplexXIso, Category.assoc]
    simp only [CochainComplex.singleFunctor, CochainComplex.singleFunctors,
      HomologicalComplex.single_map_f_self, Functor.map_comp, Category.assoc] at hn ⊢
    simp only [← Functor.map_comp_assoc, Iso.inv_hom_id, Iso.inv_hom_id_assoc,
      Iso.hom_inv_id_assoc, CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
    rw [reassoc_of% hn]
    simp [HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq]
  · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0
      ((TopCat.Sheaf.pullback AddCommGrpCat.{0} f).obj (constants Y)) j hj).eq_of_src _ _

end HodgeLean.Topology.RationalSheafComparison
