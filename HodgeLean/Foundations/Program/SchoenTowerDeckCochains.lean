import HodgeLean.Foundations.Program.SchoenTowerProjectorSections
import HodgeLean.Foundations.Program.SchoenTowerCochainMap
import HodgeLean.Foundations.ComplexSheafSingularProofs

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Program

def s2v_coverOpenDeckNatTrans {X E : TopCat.{0}} (f : X ⟶ E)
    (d : X ⟶ X) (hd : d ≫ f = f) :
    (Opens.map f ⋙ Opens.toTopCat X) ⟶ (Opens.map f ⋙ Opens.toTopCat X) where
  app U := TopCat.ofHom (s2v_coverOpenDeck f d hd U)
  naturality := by
    intro U V i
    ext x
    rfl

def s2v_coverOpenChainDeck {X E : TopCat.{0}} (f : X ⟶ E)
    (d : X ⟶ X) (hd : d ≫ f = f) :
    (Opens.map f ⋙ openSingularChainComplexFunctor ℂ X) ⟶
      (Opens.map f ⋙ openSingularChainComplexFunctor ℂ X) :=
  Functor.whiskerRight (s2v_coverOpenDeckNatTrans f d hd)
    ((singularChainComplexFunctor (ModuleCat.{0} ℂ)).obj (ModuleCat.of ℂ ℂ))

def s2v_coverCochainPresheafDeck {X E : TopCat.{0}} (f : X ⟶ E)
    (d : X ⟶ X) (hd : d ≫ f = f) (n : ℕ) :
    ((Opens.map f).op ⋙ singularCochainPresheaf ℂ X n) ⟶
      ((Opens.map f).op ⋙ singularCochainPresheaf ℂ X n) where
  app U := AddCommGrpCat.ofHom
    (((s2v_coverOpenChainDeck f d hd).app U.unop).f n).hom.dualMap.toAddMonoidHom
  naturality := by
    intro U V i
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro φ
    change OpenCochains ℂ X (op ((Opens.map f).obj U.unop)) n at φ
    apply LinearMap.ext
    intro c
    let C := Opens.map f ⋙ openSingularChainComplexFunctor ℂ X
    let D := s2v_coverOpenChainDeck f d hd
    change φ (((D.app V.unop ≫ C.map i.unop).f n).hom c) =
      φ (((C.map i.unop ≫ D.app U.unop).f n).hom c)
    exact congrArg (fun q : C.obj V.unop ⟶ C.obj U.unop => φ ((q.f n).hom c))
      (D.naturality i.unop).symm

theorem s2v_coverCochainPresheafDeck_coboundary {X E : TopCat.{0}}
    (f : X ⟶ E) (d : X ⟶ X) (hd : d ≫ f = f) (n : ℕ) :
    s2v_coverCochainPresheafDeck f d hd n ≫
        Functor.whiskerLeft (Opens.map f).op (singularCochainCoboundary ℂ X n) =
      Functor.whiskerLeft (Opens.map f).op (singularCochainCoboundary ℂ X n) ≫
        s2v_coverCochainPresheafDeck f d hd (n + 1) := by
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro φ
  change OpenCochains ℂ X (op ((Opens.map f).obj U.unop)) n at φ
  apply LinearMap.ext
  intro c
  let K := (openSingularChainComplexFunctor ℂ X).obj ((Opens.map f).obj U.unop)
  let D := (s2v_coverOpenChainDeck f d hd).app U.unop
  change φ ((K.d (n + 1) n ≫ D.f n).hom c) =
    φ ((D.f (n + 1) ≫ K.d (n + 1) n).hom c)
  exact congrArg (fun q : K.X (n + 1) ⟶ K.X n => φ (q.hom c))
    (D.comm (n + 1) n).symm

theorem s2v_presheafPushforward_additive {X E : TopCat.{0}} (f : X ⟶ E) :
    (TopCat.Presheaf.pushforward AddCommGrpCat.{0} f).Additive := by
  constructor
  intro P Q a b
  rfl

attribute [local instance] s2v_presheafPushforward_additive

def s2v_coverCochainPresheafComplexDeck {X E : TopCat.{0}} (f : X ⟶ E)
    (d : X ⟶ X) (hd : d ≫ f = f) :
    ((TopCat.Presheaf.pushforward AddCommGrpCat.{0} f).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (singularCochainPresheafComplex ℂ X) ⟶
    ((TopCat.Presheaf.pushforward AddCommGrpCat.{0} f).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (singularCochainPresheafComplex ℂ X) where
  f n := s2v_coverCochainPresheafDeck f d hd n
  comm' i j hij := by
    have hj : i + 1 = j := hij
    subst j
    change s2v_coverCochainPresheafDeck f d hd i ≫
        Functor.whiskerLeft (Opens.map f).op ((singularCochainPresheafComplex ℂ X).d i (i + 1)) =
      Functor.whiskerLeft (Opens.map f).op ((singularCochainPresheafComplex ℂ X).d i (i + 1)) ≫
        s2v_coverCochainPresheafDeck f d hd (i + 1)
    rw [singularCochainPresheafComplex_d]
    exact s2v_coverCochainPresheafDeck_coboundary f d hd i


def s2v_globalRawCochainDeck {X : TopCat.{0}} (d : X ⟶ X) :
    globalRawSingularCochainComplex ℂ X ⟶ globalRawSingularCochainComplex ℂ X where
  f n := (s2v_singularCochainPresheafMap d n).app (op ⊤)
  comm' i j hij := by
    have hj : i + 1 = j := hij
    subst j
    change (s2v_singularCochainPresheafMap d i).app (op ⊤) ≫
        ((singularCochainPresheafComplex ℂ X).d i (i + 1)).app (op ⊤) =
      ((singularCochainPresheafComplex ℂ X).d i (i + 1)).app (op ⊤) ≫
        (s2v_singularCochainPresheafMap d (i + 1)).app (op ⊤)
    rw [singularCochainPresheafComplex_d]
    exact congrArg (fun a => a.app (op ⊤))
      (s2v_singularCochainPresheafMap_coboundary d i)


theorem s2v_topOpenChainMap_naturality {X : TopCat.{0}} (d : X ⟶ X) :
    (s2v_openChainMap d).app ⊤ ≫ (topOpenSingularChainComplexIso ℂ X).hom =
      (topOpenSingularChainComplexIso ℂ X).hom ≫ singularChainComplexMap ℂ d := by
  let F := (singularChainComplexFunctor (ModuleCat.{0} ℂ)).obj (ModuleCat.of ℂ ℂ)
  have ht : (s2v_openMapNatTrans d).app ⊤ ≫ (Opens.inclusionTopIso X).hom =
      (Opens.inclusionTopIso X).hom ≫ d := by
    ext x
    rfl
  change F.map ((s2v_openMapNatTrans d).app ⊤) ≫ F.map (Opens.inclusionTopIso X).hom =
    F.map (Opens.inclusionTopIso X).hom ≫ F.map d
  rw [← F.map_comp, ← F.map_comp, ht]


theorem s2v_topOpenCochainIso_naturality {X : TopCat.{0}} (d : X ⟶ X) :
    singularCochainComplexMap ℂ d ≫ (singularCochainComplexIsoTopOpen ℂ X).hom =
      (singularCochainComplexIsoTopOpen ℂ X).hom ≫
        HomologicalComplex.linearDualMap ((s2v_openChainMap d).app ⊤) := by
  have h := congrArg HomologicalComplex.linearDualMap (s2v_topOpenChainMap_naturality d)
  rw [HomologicalComplex.linearDualMap_comp, HomologicalComplex.linearDualMap_comp] at h
  exact h.symm


theorem s2v_globalRawCochainComplexIso_deck {X : TopCat.{0}} (d : X ⟶ X) :
    (globalRawSingularCochainComplexIso ℂ X).inv ≫ s2v_globalRawCochainDeck d =
      ((forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat).mapHomologicalComplex
        (ComplexShape.up ℕ)).map
          (HomologicalComplex.linearDualMap ((s2v_openChainMap d).app ⊤)) ≫
            (globalRawSingularCochainComplexIso ℂ X).inv := by
  apply HomologicalComplex.Hom.ext
  funext n
  rfl


set_option maxHeartbeats 200000 in
theorem s2v_ordinarySingularCohomologyEquivGlobalRaw_deck {X : TopCat.{0}}
    (d : X ⟶ X) (n : ℕ) (x : Cohomology ℂ X n) :
    ordinarySingularCohomologyEquivGlobalRaw ℂ X n (cohomologyMap ℂ n d x) =
      HomologicalComplex.homologyMap (s2v_globalRawCochainDeck d) n
        (ordinarySingularCohomologyEquivGlobalRaw ℂ X n x) := by
  let F := forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat
  let i := singularCochainComplexIsoTopOpen ℂ X
  let u := singularCochainComplexMap ℂ d
  let v := HomologicalComplex.linearDualMap ((s2v_openChainMap d).app ⊤)
  have hi : u ≫ i.hom = i.hom ≫ v := s2v_topOpenCochainIso_naturality d
  have hsq : (globalRawSingularCochainComplexIso ℂ X).inv ≫ s2v_globalRawCochainDeck d =
      (F.mapHomologicalComplex (ComplexShape.up ℕ)).map v ≫
        (globalRawSingularCochainComplexIso ℂ X).inv :=
    s2v_globalRawCochainComplexIso_deck d
  have hmor : F.map (HomologicalComplex.homologyMap u n) ≫
      (F.map (HomologicalComplex.homologyMap i.hom n) ≫
        (topOpenForgottenSingularCochainHomologyIso ℂ X n).inv ≫
          HomologicalComplex.homologyMap (globalRawSingularCochainComplexIso ℂ X).inv n) =
    (F.map (HomologicalComplex.homologyMap i.hom n) ≫
      (topOpenForgottenSingularCochainHomologyIso ℂ X n).inv ≫
        HomologicalComplex.homologyMap (globalRawSingularCochainComplexIso ℂ X).inv n) ≫
          HomologicalComplex.homologyMap (s2v_globalRawCochainDeck d) n := by
    rw [← Category.assoc, ← F.map_comp, ← HomologicalComplex.homologyMap_comp, hi,
      HomologicalComplex.homologyMap_comp, F.map_comp, Category.assoc,
      ← Category.assoc (F.map (HomologicalComplex.homologyMap v n)),
      (topOpenForgottenSingularCochainHomologyIso_inv_naturality ℂ X n v)]
    simp only [Category.assoc]
    exact congrArg (fun g => F.map (HomologicalComplex.homologyMap i.hom n) ≫
      (topOpenForgottenSingularCochainHomologyIso ℂ X n).inv ≫ g)
        (homologyMap_comp_of_comm hsq.symm n)
  exact ConcreteCategory.congr_hom hmor x


theorem s2v_extendHomologyIso_inv_naturality
    (G : CochainComplex AddCommGrpCat.{0} ℕ) (a : G ⟶ G) (n : ℕ) :
    HomologicalComplex.homologyMap a n ≫
        (G.extendHomologyIso ComplexShape.embeddingUpNat (j := n) rfl).inv =
      (G.extendHomologyIso ComplexShape.embeddingUpNat (j := n) rfl).inv ≫
        HomologicalComplex.homologyMap
          (HomologicalComplex.extendMap a ComplexShape.embeddingUpNat) (n : ℤ) :=
  (inv_comp_eq_of_comp_hom
    (G.extendHomologyIso ComplexShape.embeddingUpNat (j := n) rfl)
    (HomologicalComplex.extendHomologyIso_hom_naturality a
      ComplexShape.embeddingUpNat (j := n) rfl)).symm

end HodgeLean.Foundations.Program
