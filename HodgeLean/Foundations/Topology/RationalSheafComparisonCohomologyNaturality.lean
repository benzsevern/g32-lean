import HodgeLean.Foundations.Topology.RationalSheafComparisonResolutionInt
import HodgeLean.Foundations.Topology.RationalSheafComparisonSectionTransport
import HodgeLean.Foundations.Topology.RationalSheafComparisonExtHomology

/-! The resolution cohomology identification and inverse image on Ext.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CochainComplex CochainComplex.HomComplex
namespace HodgeLean.Topology.RationalSheafComparison

/-- Source: Bredon, Sheaf Theory, second edition, II.4. -/
def globalResolutionPullback {X Y : TopCat.{0}} (f : X ⟶ Y) :
    TopCat.Sheaf.globalSectionsComplexInt Y (resolution Y).cochainComplex ⟶
      TopCat.Sheaf.globalSectionsComplexInt X (resolution X).cochainComplex :=
  globalInverseImageComplexUnit f (resolution Y).cochainComplex ≫
    ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor X).mapHomologicalComplex
      (.up ℤ)).map (resolutionPullbackMapInt f)

/-- Source: Bredon, Sheaf Theory, second edition, II.4. -/
theorem resolutionCohomologyEquiv_naturality {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ)
    (v : (TopCat.Sheaf.globalSectionsComplexInt Y (resolution Y).cochainComplex).homology (n : ℤ)) :
    resolutionCohomologyEquiv X n (HomologicalComplex.homologyMap (globalResolutionPullback f) (n : ℤ) v) =
      sheafPullback f n (resolutionCohomologyEquiv Y n v) := by
  letI : HasDerivedCategory (TopCat.Sheaf AddCommGrpCat.{0} X) := HasDerivedCategory.standard _
  letI : HasDerivedCategory (TopCat.Sheaf AddCommGrpCat.{0} Y) := HasDerivedCategory.standard _
  letI : PreservesFiniteLimits (TopCat.Sheaf.pullback AddCommGrpCat.{0} f) := pullback_preservesFiniteLimits f
  letI : (TopCat.Sheaf.pullback AddCommGrpCat.{0} f).Additive := pullback_additive f
  letI : PreservesFiniteColimits (TopCat.Sheaf.pullback AddCommGrpCat.{0} f) := inferInstance
  let a := (CochainComplex.singleFunctor _ 0).map
      (pullbackConstantsIso f (AddCommGrpCat.of (ULift ℤ))).inv ≫
    (HomologicalComplex.singleMapHomologicalComplex
      (TopCat.Sheaf.pullback AddCommGrpCat.{0} f) (.up ℤ) 0).inv.app
        ((TopCat.Sheaf.constantFunctor Y).obj (AddCommGrpCat.of (ULift ℤ)))
  let T := functorHomTransport (TopCat.Sheaf.pullback AddCommGrpCat.{0} f) a (resolutionPullbackMapInt f)
  have hc := integerHomComplexIso_transport f (resolution Y).cochainComplex
    (resolution X).cochainComplex (resolutionPullbackMapInt f)
  have hn : (integerHomComplexIso Y (resolution Y).cochainComplex).inv ≫ T =
      globalResolutionPullback f ≫ (integerHomComplexIso X (resolution X).cochainComplex).inv := by
    rw [Iso.inv_comp_eq]
    dsimp only [globalResolutionPullback]
    rw [← Category.assoc, ← hc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hp : HomologicalComplex.homologyMap
      (integerHomComplexIso X (resolution X).cochainComplex).inv (n : ℤ)
        (HomologicalComplex.homologyMap (globalResolutionPullback f) (n : ℤ) v) =
      HomologicalComplex.homologyMap T (n : ℤ)
        (HomologicalComplex.homologyMap
          (integerHomComplexIso Y (resolution Y).cochainComplex).inv (n : ℤ) v) := by
    have h := congrArg (fun k => HomologicalComplex.homologyMap k (n : ℤ)) hn
    simp only [HomologicalComplex.homologyMap_comp] at h
    exact (ConcreteCategory.congr_hom h v).symm
  change (resolution X).extEquivCohomologyClass.symm
    (homologyAddEquiv _ _ (n : ℤ) (HomologicalComplex.homologyMap
      (integerHomComplexIso X (resolution X).cochainComplex).inv (n : ℤ)
        (HomologicalComplex.homologyMap (globalResolutionPullback f) (n : ℤ) v))) = _
  rw [hp]
  exact resolutionHomology_transport (TopCat.Sheaf.pullback AddCommGrpCat.{0} f)
    (resolution Y) (resolution X)
    (pullbackConstantsIso f (AddCommGrpCat.of (ULift ℤ))).inv
    (pullbackConstantsIso f (AddCommGrpCat.of ℚ)).hom
    (resolutionPullbackMapInt f) (resolutionPullbackMapInt_augmentation f) n
    (HomologicalComplex.homologyMap (integerHomComplexIso Y (resolution Y).cochainComplex).inv
      (n : ℤ) v)

end HodgeLean.Topology.RationalSheafComparison
