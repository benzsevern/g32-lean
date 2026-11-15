import HodgeLean.Foundations.ComplexSheafSingularProofs

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Program

def s2v_openMapNatTrans {X Y : TopCat.{0}} (g : X ⟶ Y) :
    (Opens.map g ⋙ Opens.toTopCat X) ⟶ Opens.toTopCat Y where
  app U := TopCat.ofHom ⟨fun x => ⟨g x.val, x.property⟩,
    (g.hom.continuous.comp continuous_subtype_val).subtype_mk _⟩
  naturality := by
    intro U V i
    ext x
    rfl

def s2v_openChainMap {X Y : TopCat.{0}} (g : X ⟶ Y) :
    (Opens.map g ⋙ openSingularChainComplexFunctor ℂ X) ⟶
      openSingularChainComplexFunctor ℂ Y :=
  Functor.whiskerRight (s2v_openMapNatTrans g)
    ((singularChainComplexFunctor (ModuleCat.{0} ℂ)).obj (ModuleCat.of ℂ ℂ))

def s2v_singularCochainPresheafMap {X Y : TopCat.{0}} (g : X ⟶ Y) (n : ℕ) :
    singularCochainPresheaf ℂ Y n ⟶
      (TopCat.Presheaf.pushforward AddCommGrpCat.{0} g).obj (singularCochainPresheaf ℂ X n) where
  app U := AddCommGrpCat.ofHom
    (((s2v_openChainMap g).app U.unop).f n).hom.dualMap.toAddMonoidHom
  naturality := by
    intro U V i
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro φ
    change OpenCochains ℂ Y U n at φ
    apply LinearMap.ext
    intro c
    let CX := Opens.map g ⋙ openSingularChainComplexFunctor ℂ X
    let CY := openSingularChainComplexFunctor ℂ Y
    let D := s2v_openChainMap g
    change φ (((D.app V.unop ≫ CY.map i.unop).f n).hom c) =
      φ (((CX.map i.unop ≫ D.app U.unop).f n).hom c)
    exact congrArg (fun q : CX.obj V.unop ⟶ CY.obj U.unop => φ ((q.f n).hom c))
      (D.naturality i.unop).symm

theorem s2v_singularCochainPresheafMap_coboundary {X Y : TopCat.{0}}
    (g : X ⟶ Y) (n : ℕ) :
    s2v_singularCochainPresheafMap g n ≫
        (TopCat.Presheaf.pushforward AddCommGrpCat.{0} g).map (singularCochainCoboundary ℂ X n) =
      singularCochainCoboundary ℂ Y n ≫ s2v_singularCochainPresheafMap g (n + 1) := by
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro φ
  change OpenCochains ℂ Y U n at φ
  apply LinearMap.ext
  intro c
  let KX := (openSingularChainComplexFunctor ℂ X).obj ((Opens.map g).obj U.unop)
  let KY := (openSingularChainComplexFunctor ℂ Y).obj U.unop
  let D := (s2v_openChainMap g).app U.unop
  change φ ((KX.d (n + 1) n ≫ D.f n).hom c) =
    φ ((D.f (n + 1) ≫ KY.d (n + 1) n).hom c)
  exact congrArg (fun q : KX.X (n + 1) ⟶ KY.X n => φ (q.hom c))
    (D.comm (n + 1) n).symm

def s2v_singularCochainSheafMap {X Y : TopCat.{0}} (g : X ⟶ Y) (n : ℕ) :
    singularCochainSheaf ℂ Y n ⟶
      (TopCat.Sheaf.pushforward AddCommGrpCat.{0} g).obj (singularCochainSheaf ℂ X n) := by
  let JX := Opens.grothendieckTopology X
  let JY := Opens.grothendieckTopology Y
  let T := (TopCat.Sheaf.pushforward AddCommGrpCat.{0} g).obj (singularCochainSheaf ℂ X n)
  let η := s2v_singularCochainPresheafMap g n ≫
    (TopCat.Presheaf.pushforward AddCommGrpCat.{0} g).map
      (toSheafify JX (singularCochainPresheaf ℂ X n))
  exact ⟨sheafifyLift JY η T.property⟩

theorem s2v_singularCochainSheafMap_unit {X Y : TopCat.{0}} (g : X ⟶ Y) (n : ℕ) :
    toSheafify (Opens.grothendieckTopology Y) (singularCochainPresheaf ℂ Y n) ≫
      (s2v_singularCochainSheafMap g n).hom =
    s2v_singularCochainPresheafMap g n ≫
      (TopCat.Presheaf.pushforward AddCommGrpCat.{0} g).map
        (toSheafify (Opens.grothendieckTopology X) (singularCochainPresheaf ℂ X n)) :=
  toSheafify_sheafifyLift _ _ _

theorem s2v_singularCochainSheafMap_coboundary {X Y : TopCat.{0}}
    (g : X ⟶ Y) (n : ℕ) :
    s2v_singularCochainSheafMap g n ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat.{0} g).map
          (singularCochainSheafCoboundary ℂ X n) =
      singularCochainSheafCoboundary ℂ Y n ≫ s2v_singularCochainSheafMap g (n + 1) := by
  let JX := Opens.grothendieckTopology X
  let JY := Opens.grothendieckTopology Y
  let P := TopCat.Presheaf.pushforward AddCommGrpCat.{0} g
  let T := (TopCat.Sheaf.pushforward AddCommGrpCat.{0} g).obj
    (singularCochainSheaf ℂ X (n + 1))
  apply Sheaf.hom_ext
  apply sheafify_hom_ext JY _ _ T.property
  change toSheafify JY (singularCochainPresheaf ℂ Y n) ≫
      (s2v_singularCochainSheafMap g n).hom ≫
        P.map (sheafifyMap JX (singularCochainCoboundary ℂ X n)) =
    toSheafify JY (singularCochainPresheaf ℂ Y n) ≫
      sheafifyMap JY (singularCochainCoboundary ℂ Y n) ≫
        (s2v_singularCochainSheafMap g (n + 1)).hom
  rw [← Category.assoc, s2v_singularCochainSheafMap_unit, Category.assoc,
    ← P.map_comp, ← toSheafify_naturality, P.map_comp, ← Category.assoc,
    s2v_singularCochainPresheafMap_coboundary]
  rw [Category.assoc, ← s2v_singularCochainSheafMap_unit,
    ← Category.assoc, toSheafify_naturality, Category.assoc]

theorem s2v_singularCochainPresheafMap_augmentation {X Y : TopCat.{0}} (g : X ⟶ Y) :
    constantsToSingularCochainZero ℂ Y ≫ s2v_singularCochainPresheafMap g 0 =
      (TopCat.Presheaf.pushforward AddCommGrpCat.{0} g).map
        (constantsToSingularCochainZero ℂ X) := by
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro r
  change ℂ at r
  apply LinearMap.ext
  intro c
  change r * ((openZeroAugmentation ℂ Y U).hom
      ((((s2v_openChainMap g).app U.unop).f 0).hom c)) =
    r * ((openZeroAugmentation ℂ X (op ((Opens.map g).obj U.unop))).hom c)
  exact congrArg (r * ·) <| congrArg (fun f => f.hom c) <|
    simplicialZeroAugmentation_naturality ℂ
      (TopCat.toSSet.map ((s2v_openMapNatTrans g).app U.unop))

end HodgeLean.Foundations.Program
