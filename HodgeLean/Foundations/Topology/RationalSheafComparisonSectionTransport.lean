import HodgeLean.Foundations.Topology.RationalSheafComparisonSections
import HodgeLean.Foundations.Topology.RationalSheafComparisonHomTransport

/-! The integer-generator identification and inverse image on sections.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
namespace HodgeLean.Topology.RationalSheafComparison

/-- Source: Bredon, Sheaf Theory, second edition, II.4. -/
def integerHomPullback {X Y : TopCat.{0}} (f : X ⟶ Y) :
    preadditiveCoyoneda.obj (op ((TopCat.Sheaf.constantFunctor Y).obj
      (AddCommGrpCat.of (ULift ℤ)))) ⟶
      TopCat.Sheaf.pullback AddCommGrpCat.{0} f ⋙
        preadditiveCoyoneda.obj (op ((TopCat.Sheaf.constantFunctor X).obj
          (AddCommGrpCat.of (ULift ℤ)))) where
  app I := AddCommGrpCat.ofHom
    { toFun g := (pullbackConstantsIso f (AddCommGrpCat.of (ULift ℤ))).inv ≫
        (TopCat.Sheaf.pullback AddCommGrpCat.{0} f).map g
      map_zero' := by rw [Functor.map_zero, comp_zero]
      map_add' g h := by rw [Functor.map_add, Preadditive.comp_add] }
  naturality {I J} g := by
    ext h
    change (pullbackConstantsIso f (AddCommGrpCat.of (ULift ℤ))).inv ≫
      (TopCat.Sheaf.pullback AddCommGrpCat.{0} f).map (h ≫ g) = _
    rw [Functor.map_comp, ← Category.assoc]
    rfl

/-- Source: Bredon, Sheaf Theory, second edition, II.4. -/
theorem integerHomIso_pullback {X Y : TopCat.{0}} (f : X ⟶ Y) :
    (integerHomIso Y).hom ≫ globalInverseImageUnit f =
      integerHomPullback f ≫ Functor.whiskerLeft (TopCat.Sheaf.pullback AddCommGrpCat.{0} f)
        (integerHomIso X).hom := by
  ext I g
  exact congrArg (fun h => h.hom (ULift.up (1 : ℤ)))
    (constantHomEquiv_pullback f (AddCommGrpCat.of (ULift ℤ)) I g) |>.symm

/-- Source: Bredon, Sheaf Theory, second edition, II.4. -/
def globalInverseImageComplexUnit {X Y : TopCat.{0}} (f : X ⟶ Y)
    (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} Y) ℤ) :
    TopCat.Sheaf.globalSectionsComplexInt Y K ⟶
      TopCat.Sheaf.globalSectionsComplexInt X
        (((TopCat.Sheaf.pullback AddCommGrpCat.{0} f).mapHomologicalComplex (.up ℤ)).obj K) where
  f n := (globalInverseImageUnit f).app (K.X n)
  comm' i j _ := ((globalInverseImageUnit f).naturality (K.d i j)).symm

/-- Source: Bredon, Sheaf Theory, second edition, II.4. -/
theorem integerHomComplexIso_transport {X Y : TopCat.{0}} (f : X ⟶ Y)
    (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} Y) ℤ)
    (L : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} X) ℤ)
    (c : ((TopCat.Sheaf.pullback AddCommGrpCat.{0} f).mapHomologicalComplex (.up ℤ)).obj K ⟶ L) :
    functorHomTransport (TopCat.Sheaf.pullback AddCommGrpCat.{0} f)
        ((CochainComplex.singleFunctor _ 0).map
            (pullbackConstantsIso f (AddCommGrpCat.of (ULift ℤ))).inv ≫
          (HomologicalComplex.singleMapHomologicalComplex
            (TopCat.Sheaf.pullback AddCommGrpCat.{0} f) (.up ℤ) 0).inv.app
              ((TopCat.Sheaf.constantFunctor Y).obj (AddCommGrpCat.of (ULift ℤ)))) c ≫
      (integerHomComplexIso X L).hom =
    (integerHomComplexIso Y K).hom ≫ globalInverseImageComplexUnit f K ≫
      ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor X).mapHomologicalComplex
        (.up ℤ)).map c := by
  apply HomologicalComplex.Hom.ext
  funext n
  ext z
  obtain ⟨g, rfl⟩ := CochainComplex.HomComplex.Cochain.fromSingleMk_surjective z n (zero_add n)
  change (integerHomIso X).hom.app (L.X n)
    (CochainComplex.HomComplex.Cochain.fromSingleEquiv (zero_add n)
      (functorCochainTransport (TopCat.Sheaf.pullback AddCommGrpCat.{0} f) _ c
        (CochainComplex.HomComplex.Cochain.fromSingleMk g (zero_add n)))) = _
  erw [fromSingleEquiv_functorTransport (TopCat.Sheaf.pullback AddCommGrpCat.{0} f) c
    (pullbackConstantsIso f (AddCommGrpCat.of (ULift ℤ))).inv g]
  have hu := congrArg
    (fun k : (preadditiveCoyoneda.obj (op ((TopCat.Sheaf.constantFunctor Y).obj
        (AddCommGrpCat.of (ULift ℤ))))).obj (K.X n) ⟶
      (TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor X).obj
        ((TopCat.Sheaf.pullback AddCommGrpCat.{0} f).obj (K.X n)) => k.hom g)
    (NatTrans.congr_app (integerHomIso_pullback f) (K.X n))
  have hn := congrArg
    (fun k : (preadditiveCoyoneda.obj (op ((TopCat.Sheaf.constantFunctor X).obj
        (AddCommGrpCat.of (ULift ℤ))))).obj
          ((TopCat.Sheaf.pullback AddCommGrpCat.{0} f).obj (K.X n)) ⟶
      (TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor X).obj (L.X n) =>
        k.hom ((pullbackConstantsIso f (AddCommGrpCat.of (ULift ℤ))).inv ≫
          (TopCat.Sheaf.pullback AddCommGrpCat.{0} f).map g))
    ((integerHomIso X).hom.naturality (c.f n))
  convert hn.trans (congrArg
    ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor X).map (c.f n)) hu.symm) using 1
  · rfl
  · simp [integerHomComplexIso, CochainComplex.HomComplex.fromSingleZeroIsoPreadditiveCoyoneda]
    erw [CochainComplex.HomComplex.Cochain.fromSingleEquiv_fromSingleMk]
    rfl

end HodgeLean.Topology.RationalSheafComparison
