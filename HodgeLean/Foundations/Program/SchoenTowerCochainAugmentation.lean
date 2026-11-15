import HodgeLean.Foundations.Program.SchoenTowerCochainComplexMap
import HodgeLean.Foundations.Program.SchoenTowerConstantCover
import HodgeLean.Foundations.Program.SchoenTowerComparisonScalar
import HodgeLean.Foundations.Program.SchoenTowerDeckCochains
import HodgeConjecture.Lemmas.AlgebraicTopology.Sheaf.FlasqueExtendNat

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Program

def s2v_constantSheafContinuousMap {X Y : TopCat.{0}} (g : X ⟶ Y) :
    (TopCat.Sheaf.constantFunctor Y).obj (AddCommGrpCat.of ℂ) ⟶
      (TopCat.Sheaf.pushforward AddCommGrpCat.{0} g).obj
        ((TopCat.Sheaf.constantFunctor X).obj (AddCommGrpCat.of ℂ)) := by
  let T := (TopCat.Sheaf.pushforward AddCommGrpCat.{0} g).obj
    ((TopCat.Sheaf.constantFunctor X).obj (AddCommGrpCat.of ℂ))
  exact ⟨sheafifyLift (Opens.grothendieckTopology Y)
    ((TopCat.Presheaf.pushforward AddCommGrpCat.{0} g).map
      (toSheafify (Opens.grothendieckTopology X)
        ((Functor.const (Opens X)ᵒᵖ).obj (AddCommGrpCat.of ℂ)))) T.property⟩

theorem s2v_constantSheafContinuousMap_unit {X Y : TopCat.{0}} (g : X ⟶ Y) :
    toSheafify (Opens.grothendieckTopology Y)
        ((Functor.const (Opens Y)ᵒᵖ).obj (AddCommGrpCat.of ℂ)) ≫
      (s2v_constantSheafContinuousMap g).hom =
    (TopCat.Presheaf.pushforward AddCommGrpCat.{0} g).map
      (toSheafify (Opens.grothendieckTopology X)
        ((Functor.const (Opens X)ᵒᵖ).obj (AddCommGrpCat.of ℂ))) :=
  toSheafify_sheafifyLift _ _ _

theorem s2v_singularCochainSheafMap_augmentation {X Y : TopCat.{0}} (g : X ⟶ Y) :
    constantsToSingularCochainZeroSheaf ℂ Y ≫ s2v_singularCochainSheafMap g 0 =
      s2v_constantSheafContinuousMap g ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat.{0} g).map
          (constantsToSingularCochainZeroSheaf ℂ X) := by
  let JX := Opens.grothendieckTopology X
  let JY := Opens.grothendieckTopology Y
  let P := TopCat.Presheaf.pushforward AddCommGrpCat.{0} g
  let T := (TopCat.Sheaf.pushforward AddCommGrpCat.{0} g).obj
    (singularCochainSheaf ℂ X 0)
  apply Sheaf.hom_ext
  apply sheafify_hom_ext JY _ _ T.property
  change toSheafify JY ((Functor.const (Opens Y)ᵒᵖ).obj (AddCommGrpCat.of ℂ)) ≫
      sheafifyMap JY (constantsToSingularCochainZero ℂ Y) ≫
        (s2v_singularCochainSheafMap g 0).hom =
    toSheafify JY ((Functor.const (Opens Y)ᵒᵖ).obj (AddCommGrpCat.of ℂ)) ≫
      (s2v_constantSheafContinuousMap g).hom ≫
        P.map (sheafifyMap JX (constantsToSingularCochainZero ℂ X))
  rw [← Category.assoc, ← toSheafify_naturality, Category.assoc,
    s2v_singularCochainSheafMap_unit, ← Category.assoc,
    s2v_singularCochainPresheafMap_augmentation]
  rw [← Category.assoc, s2v_constantSheafContinuousMap_unit,
    ← P.map_comp, ← P.map_comp, toSheafify_naturality]

attribute [local instance] s2v_sheafPushforward_additive

def s2v_constantSheafComplexContinuousMap {X Y : TopCat.{0}} (g : X ⟶ Y) :
    (CochainComplex.single₀ (TopCat.Sheaf AddCommGrpCat.{0} Y)).obj
        ((TopCat.Sheaf.constantFunctor Y).obj (AddCommGrpCat.of ℂ)) ⟶
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} g).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj
          ((CochainComplex.single₀ (TopCat.Sheaf AddCommGrpCat.{0} X)).obj
            ((TopCat.Sheaf.constantFunctor X).obj (AddCommGrpCat.of ℂ))) :=
  (CochainComplex.single₀ (TopCat.Sheaf AddCommGrpCat.{0} Y)).map
      (s2v_constantSheafContinuousMap g) ≫
    (HomologicalComplex.singleMapHomologicalComplex
      (TopCat.Sheaf.pushforward AddCommGrpCat.{0} g) (ComplexShape.up ℕ) 0).inv.app
        ((TopCat.Sheaf.constantFunctor X).obj (AddCommGrpCat.of ℂ))

theorem s2v_singularCochainSheafComplexMap_augmentation {X Y : TopCat.{0}}
    (g : X ⟶ Y) :
    constantsToSingularCochainSheafComplex ℂ Y ≫ s2v_singularCochainSheafComplexMap g =
      s2v_constantSheafComplexContinuousMap g ≫
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} g).mapHomologicalComplex
          (ComplexShape.up ℕ)).map (constantsToSingularCochainSheafComplex ℂ X) := by
  apply HomologicalComplex.from_single_hom_ext
  simpa [constantsToSingularCochainSheafComplex, s2v_singularCochainSheafComplexMap,
    s2v_constantSheafComplexContinuousMap] using s2v_singularCochainSheafMap_augmentation g


def s2v_pushforwardDeck {X Y : TopCat.{0}} (f : X ⟶ Y) (d : X ⟶ X)
    (hd : d ≫ f = f) (F : TopCat.Sheaf AddCommGrpCat.{0} X)
    (a : F ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{0} d).obj F) :
    (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).obj F ⟶
      (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).obj F :=
  (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).map a ≫ eqToHom (by
    change (TopCat.Sheaf.pushforward AddCommGrpCat.{0} (d ≫ f)).obj F = _
    rw [hd])


theorem s2v_pushforwardDeck_naturality {X Y : TopCat.{0}} (f : X ⟶ Y) (d : X ⟶ X)
    (hd : d ≫ f = f) {F G : TopCat.Sheaf AddCommGrpCat.{0} X}
    (a : F ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{0} d).obj F)
    (b : G ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{0} d).obj G)
    (u : F ⟶ G)
    (hu : u ≫ b = a ≫ (TopCat.Sheaf.pushforward AddCommGrpCat.{0} d).map u) :
    (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).map u ≫
        s2v_pushforwardDeck f d hd G b =
      s2v_pushforwardDeck f d hd F a ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).map u := by
  let P := TopCat.Sheaf.pushforward AddCommGrpCat.{0} f
  unfold s2v_pushforwardDeck
  rw [← Category.assoc, ← P.map_comp, hu, P.map_comp, Category.assoc]
  exact congrArg (fun q => P.map a ≫ q) (eqToHom_naturality
    (fun t : X ⟶ Y => (TopCat.Sheaf.pushforward AddCommGrpCat.{0} t).map u) hd)


theorem s2v_pushedSingularAugmentation_deck {X Y : TopCat.{0}}
    (f : X ⟶ Y) (d : X ⟶ X) (hd : d ≫ f = f) :
    (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).map
        (constantsToSingularCochainZeroSheaf ℂ X) ≫
      s2v_pushforwardDeck f d hd (singularCochainSheaf ℂ X 0)
        (s2v_singularCochainSheafMap d 0) =
    s2v_pushforwardDeck f d hd
        ((TopCat.Sheaf.constantFunctor X).obj (AddCommGrpCat.of ℂ))
        (s2v_constantSheafContinuousMap d) ≫
      (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).map
        (constantsToSingularCochainZeroSheaf ℂ X) :=
  s2v_pushforwardDeck_naturality f d hd _ _ _
    (s2v_singularCochainSheafMap_augmentation d)


def s2v_identityCoverContinuousMap {X Y : TopCat.{0}} (g : X ⟶ Y) :
    (⟨s2c_coverPresheaf (𝟙 Y), s2v_coverPresheaf_isSheaf (𝟙 Y)⟩ :
      TopCat.Sheaf AddCommGrpCat.{0} Y) ⟶
    (TopCat.Sheaf.pushforward AddCommGrpCat.{0} g).obj
      (⟨s2c_coverPresheaf (𝟙 X), s2v_coverPresheaf_isSheaf (𝟙 X)⟩ :
        TopCat.Sheaf AddCommGrpCat.{0} X) :=
  ⟨{
    app U := AddCommGrpCat.ofHom (LocallyConstant.comapAddMonoidHom (Z := ℂ)
      (show C({x : X // g x ∈ U.unop}, {y : Y // y ∈ U.unop}) from
        ⟨fun x => ⟨g x.val, x.property⟩, by fun_prop⟩))
    naturality := by
      intro U V i
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro s
      rfl }⟩


theorem s2v_constantIdentityCoverIso_unit (X : TopCat.{0}) :
    toSheafify (Opens.grothendieckTopology X)
        ((Functor.const (Opens X)ᵒᵖ).obj (AddCommGrpCat.of ℂ)) ≫
      (s2v_constantIdentityCoverIso X).hom.hom =
        s2v_constantToIdentityCoverPresheaf X := by
  let J := Opens.grothendieckTopology X
  let η := s2v_constantToIdentityCoverPresheaf X
  let L : TopCat.Sheaf AddCommGrpCat.{0} X :=
    ⟨s2c_coverPresheaf (𝟙 X), s2v_coverPresheaf_isSheaf (𝟙 X)⟩
  change toSheafify J _ ≫ sheafifyMap J η ≫
    ((sheafificationAdjunction J AddCommGrpCat.{0}).counit.app L).hom = η
  rw [← Category.assoc, ← toSheafify_naturality, Category.assoc,
    sheafificationAdjunction_counit_app_val, toSheafify_sheafifyLift, Category.comp_id]


theorem s2v_constantIdentityCoverIso_naturality {X Y : TopCat.{0}} (g : X ⟶ Y) :
    s2v_constantSheafContinuousMap g ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat.{0} g).map
          (s2v_constantIdentityCoverIso X).hom =
      (s2v_constantIdentityCoverIso Y).hom ≫ s2v_identityCoverContinuousMap g := by
  let J := Opens.grothendieckTopology Y
  let P := TopCat.Presheaf.pushforward AddCommGrpCat.{0} g
  let T := (TopCat.Sheaf.pushforward AddCommGrpCat.{0} g).obj
    (⟨s2c_coverPresheaf (𝟙 X), s2v_coverPresheaf_isSheaf (𝟙 X)⟩ :
      TopCat.Sheaf AddCommGrpCat.{0} X)
  apply Sheaf.hom_ext
  apply sheafify_hom_ext J _ _ T.property
  change toSheafify J _ ≫ (s2v_constantSheafContinuousMap g).hom ≫
      P.map (s2v_constantIdentityCoverIso X).hom.hom =
    toSheafify J _ ≫ (s2v_constantIdentityCoverIso Y).hom.hom ≫
      (s2v_identityCoverContinuousMap g).hom
  rw [← Category.assoc, s2v_constantSheafContinuousMap_unit,
    ← P.map_comp, s2v_constantIdentityCoverIso_unit,
    ← Category.assoc, s2v_constantIdentityCoverIso_unit]
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro a
  rfl


theorem s2v_pushforwardIdentityCoverDeck_hom {X Y : TopCat.{0}}
    (f : X ⟶ Y) (d : X ⟶ X) (hd : d ≫ f = f) :
    (s2v_pushforwardDeck f d hd
      (⟨s2c_coverPresheaf (𝟙 X), s2v_coverPresheaf_isSheaf (𝟙 X)⟩ :
        TopCat.Sheaf AddCommGrpCat.{0} X)
      (s2v_identityCoverContinuousMap d)).hom = s2c_coverPresheafDeck f d hd := by
  let L : TopCat.Sheaf AddCommGrpCat.{0} X :=
    ⟨s2c_coverPresheaf (𝟙 X), s2v_coverPresheaf_isSheaf (𝟙 X)⟩
  have hgen (g : X ⟶ Y) (hg : d ≫ f = g) :
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).map
        (s2v_identityCoverContinuousMap d) ≫
        eqToHom (show (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).obj
          ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} d).obj L) =
            (TopCat.Sheaf.pushforward AddCommGrpCat.{0} g).obj L from by
          change (TopCat.Sheaf.pushforward AddCommGrpCat.{0} (d ≫ f)).obj L = _
          rw [hg])).hom =
      (show s2c_coverPresheaf f ⟶ s2c_coverPresheaf g from {
        app U := AddCommGrpCat.ofHom (LocallyConstant.comapAddMonoidHom (Z := ℂ)
          (show C({x : X // g x ∈ U.unop}, {x : X // f x ∈ U.unop}) from
            ⟨fun x => ⟨d x.val, by
                have he : f (d x.val) = g x.val :=
                  congrArg (fun q : X ⟶ Y => q x.val) hg
                rw [he]; exact x.property⟩, by fun_prop⟩))
        naturality := by
          intro U V i
          apply AddCommGrpCat.hom_ext
          apply AddMonoidHom.ext
          intro s
          rfl }) := by
    subst g
    apply NatTrans.ext
    funext U
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro s
    rfl
  exact hgen f hd


theorem s2v_coverSheaf_pushforwardConstantIso_deck {X Y : TopCat.{0}}
    (f : X ⟶ Y) (d : X ⟶ X) (hd : d ≫ f = f) :
    s2c_coverSheafDeck f d hd ≫ (s2v_coverSheaf_pushforwardConstantIso f).hom =
      (s2v_coverSheaf_pushforwardConstantIso f).hom ≫
        s2v_pushforwardDeck f d hd
          ((TopCat.Sheaf.constantFunctor X).obj (AddCommGrpCat.of ℂ))
          (s2v_constantSheafContinuousMap d) := by
  let L : TopCat.Sheaf AddCommGrpCat.{0} X :=
    ⟨s2c_coverPresheaf (𝟙 X), s2v_coverPresheaf_isSheaf (𝟙 X)⟩
  let C := (TopCat.Sheaf.constantFunctor X).obj (AddCommGrpCat.of ℂ)
  let P := TopCat.Sheaf.pushforward AddCommGrpCat.{0} f
  let D := TopCat.Sheaf.pushforward AddCommGrpCat.{0} d
  let i := s2v_constantIdentityCoverIso X
  let b := s2v_identityCoverContinuousMap d
  let a := s2v_constantSheafContinuousMap d
  let q := s2v_pushforwardDeck f d hd L b
  let c := s2v_pushforwardDeck f d hd C a
  let J := Opens.grothendieckTopology Y
  let S := presheafToSheaf J AddCommGrpCat.{0}
  let ε := (sheafificationAdjunction J AddCommGrpCat.{0}).counit
  have hInv : i.inv ≫ a = b ≫ D.map i.inv := by
    apply (cancel_mono (D.map i.hom)).mp
    rw [Category.assoc, s2v_constantIdentityCoverIso_naturality,
      i.inv_hom_id_assoc, Category.assoc, ← D.map_comp,
      i.inv_hom_id, D.map_id, Category.comp_id]
  have hi : q ≫ P.map i.inv = P.map i.inv ≫ c :=
    (s2v_pushforwardDeck_naturality f d hd b a i.inv hInv).symm
  have hε : s2c_coverSheafDeck f d hd ≫ ε.app (P.obj L) =
      ε.app (P.obj L) ≫ q := by
    have h := ε.naturality q
    change S.map q.hom ≫ ε.app (P.obj L) = ε.app (P.obj L) ≫ q at h
    rw [s2v_pushforwardIdentityCoverDeck_hom f d hd] at h
    exact h
  change s2c_coverSheafDeck f d hd ≫ (ε.app (P.obj L) ≫ P.map i.inv) =
    (ε.app (P.obj L) ≫ P.map i.inv) ≫ c
  rw [← Category.assoc, hε, Category.assoc, hi, Category.assoc]


theorem s2v_coverSheaf_pushforwardConstantIso_inv_deck {X Y : TopCat.{0}}
    (f : X ⟶ Y) (d : X ⟶ X) (hd : d ≫ f = f) :
    s2v_pushforwardDeck f d hd
        ((TopCat.Sheaf.constantFunctor X).obj (AddCommGrpCat.of ℂ))
        (s2v_constantSheafContinuousMap d) ≫
      (s2v_coverSheaf_pushforwardConstantIso f).inv =
    (s2v_coverSheaf_pushforwardConstantIso f).inv ≫ s2c_coverSheafDeck f d hd := by
  let i := s2v_coverSheaf_pushforwardConstantIso f
  apply i.comp_inv_eq.mpr
  rw [Category.assoc, s2v_coverSheaf_pushforwardConstantIso_deck f d hd,
    i.inv_hom_id_assoc]


def s2v_pushedConstantAugmentation {X Y : TopCat.{0}} (f : X ⟶ Y) :
    (CochainComplex.single₀ (TopCat.Sheaf AddCommGrpCat.{0} Y)).obj
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).obj
        ((TopCat.Sheaf.constantFunctor X).obj (AddCommGrpCat.of ℂ))) ⟶
    ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (singularCochainSheafComplex ℂ X) :=
  (HomologicalComplex.singleMapHomologicalComplex
      (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f) (ComplexShape.up ℕ) 0).inv.app
        ((TopCat.Sheaf.constantFunctor X).obj (AddCommGrpCat.of ℂ)) ≫
    ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).mapHomologicalComplex
      (ComplexShape.up ℕ)).map (constantsToSingularCochainSheafComplex ℂ X)


theorem s2v_pushedConstantAugmentation_deck {X Y : TopCat.{0}}
    (f : X ⟶ Y) (d : X ⟶ X) (hd : d ≫ f = f) :
    s2v_pushedConstantAugmentation f ≫
        (s2v_pushedSingularCochainSheafComplexDeck f d hd).asHom =
      (CochainComplex.single₀ (TopCat.Sheaf AddCommGrpCat.{0} Y)).map
        (s2v_pushforwardDeck f d hd
          ((TopCat.Sheaf.constantFunctor X).obj (AddCommGrpCat.of ℂ))
          (s2v_constantSheafContinuousMap d)) ≫ s2v_pushedConstantAugmentation f := by
  apply HomologicalComplex.from_single_hom_ext
  simpa [s2v_pushedConstantAugmentation, s2v_pushedSingularCochainSheafComplexDeck,
    s2v_pushforwardDeck, s2v_singularCochainSheafComplexMap,
    constantsToSingularCochainSheafComplex,
    HomologicalComplex.eqToHom_f, HomologicalComplex.singleObjXSelf,
    HomologicalComplex.singleObjXIsoOfEq] using s2v_pushedSingularAugmentation_deck f d hd


open AlgebraicGeometry ComplexPoint

theorem s2v_pushedConstantAugmentation_quasiIso
    {W B E : Over (Spec ↧ℂ)}
    [IsProjective W.hom] [IsProjective B.hom] [IsProjective E.hom]
    (β : W ⟶ B) [IsFinite β.left] (j : E ⟶ B)
    (hX : ∀ (x : ComplexPoint (s2b_preimage β j))
      (U : Opens (ComplexPoint (s2b_preimage β j))), x ∈ U →
      ∃ V : Opens (ComplexPoint (s2b_preimage β j)),
        x ∈ V ∧ ContractibleSpace V ∧ V ≤ U) :
    QuasiIso (s2v_pushedConstantAugmentation (s2c_points.map (s2b_toExceptional β j))) := by
  let : PreservesFiniteColimits (TopCat.Sheaf.pushforward AddCommGrpCat.{0}
      (s2c_points.map (s2b_toExceptional β j))) :=
    s2v_preimage_pushforward_preservesFiniteColimits β j
  let : QuasiIso (constantsToSingularCochainSheafComplex ℂ
      (s2c_points.obj (s2b_preimage β j))) :=
    constantsToSingularCochainSheafComplex_quasiIso_of_contractibleOpenBasis ℂ hX
  unfold s2v_pushedConstantAugmentation
  infer_instance


attribute [local implicit_reducible] TopCat.Sheaf TopCat.instCategorySheaf._aux_1
  TopCat.instCategorySheaf._aux_3 TopCat.instCategorySheaf._aux_5

set_option maxHeartbeats 200000 in
theorem s2v_preimage_pushedSingularNat_isFlasque
    {W B E : Over (Spec ↧ℂ)}
    [IsProjective W.hom] [IsProjective B.hom] [IsProjective E.hom]
    (β : W ⟶ B) (j : E ⟶ B) (n : ℕ) :
    TopCat.Sheaf.IsFlasque
      ((((TopCat.Sheaf.pushforward AddCommGrpCat.{0}
        (s2c_points.map (s2b_toExceptional β j))).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj
            (singularCochainSheafComplex ℂ (s2c_points.obj (s2b_preimage β j)))).X n) := by
  let : T2Space (ComplexPoint (s2b_preimage β j)) := s2v_pullback_points_t2 β j
  let : ∀ U : Opens (ComplexPoint (s2b_preimage β j)), ParacompactSpace U :=
    s2v_projective_preimage_openParacompactSpace β j
  let : TopCat.Sheaf.IsFlasque (singularCochainSheaf ℂ
      (TopCat.of (ComplexPoint (s2b_preimage β j))) n) := by infer_instance
  change TopCat.Sheaf.IsFlasque
    ((TopCat.Sheaf.pushforward AddCommGrpCat.{0}
      (s2c_points.map (s2b_toExceptional β j))).obj
        (singularCochainSheaf ℂ (TopCat.of (ComplexPoint (s2b_preimage β j))) n))
  exact TopCat.Sheaf.IsFlasque.pushforward_isFlasque _ _


def s2v_pushedConstantAugmentationInt {X Y : TopCat.{0}} (f : X ⟶ Y) :
    (CochainComplex.singleFunctor (TopCat.Sheaf AddCommGrpCat.{0} Y) 0).obj
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).obj
        ((TopCat.Sheaf.constantFunctor X).obj (AddCommGrpCat.of ℂ))) ⟶
    (((TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (singularCochainSheafComplex ℂ X)).extend
        ComplexShape.embeddingUpNat :=
  (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).obj
        ((TopCat.Sheaf.constantFunctor X).obj (AddCommGrpCat.of ℂ))) 0 0 rfl).inv ≫
    HomologicalComplex.extendMap (s2v_pushedConstantAugmentation f)
      ComplexShape.embeddingUpNat


theorem s2v_pushedConstantAugmentationInt_deck {X Y : TopCat.{0}}
    (f : X ⟶ Y) (d : X ⟶ X) (hd : d ≫ f = f) :
    s2v_pushedConstantAugmentationInt f ≫
        HomologicalComplex.extendMap
          (s2v_pushedSingularCochainSheafComplexDeck f d hd).asHom
          ComplexShape.embeddingUpNat =
      (CochainComplex.singleFunctor (TopCat.Sheaf AddCommGrpCat.{0} Y) 0).map
        (s2v_pushforwardDeck f d hd
          ((TopCat.Sheaf.constantFunctor X).obj (AddCommGrpCat.of ℂ))
          (s2v_constantSheafContinuousMap d)) ≫ s2v_pushedConstantAugmentationInt f := by
  let C := (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).obj
    ((TopCat.Sheaf.constantFunctor X).obj (AddCommGrpCat.of ℂ))
  let c := s2v_pushforwardDeck f d hd
    ((TopCat.Sheaf.constantFunctor X).obj (AddCommGrpCat.of ℂ))
    (s2v_constantSheafContinuousMap d)
  let i := HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat C 0 0 rfl
  have hi := inv_comp_eq_of_comp_hom i
    (HomologicalComplex.extendSingleIso_hom_naturality ComplexShape.embeddingUpNat c 0 0 rfl)
  change (i.inv ≫ HomologicalComplex.extendMap (s2v_pushedConstantAugmentation f)
      ComplexShape.embeddingUpNat) ≫ _ = _ ≫
    (i.inv ≫ HomologicalComplex.extendMap (s2v_pushedConstantAugmentation f)
      ComplexShape.embeddingUpNat)
  rw [Category.assoc, ← HomologicalComplex.extendMap_comp,
    s2v_pushedConstantAugmentation_deck, HomologicalComplex.extendMap_comp,
    ← Category.assoc, hi, Category.assoc]


theorem s2v_pushedConstantAugmentationInt_quasiIso
    {W B E : Over (Spec ↧ℂ)}
    [IsProjective W.hom] [IsProjective B.hom] [IsProjective E.hom]
    (β : W ⟶ B) [IsFinite β.left] (j : E ⟶ B)
    (hX : ∀ (x : ComplexPoint (s2b_preimage β j))
      (U : Opens (ComplexPoint (s2b_preimage β j))), x ∈ U →
      ∃ V : Opens (ComplexPoint (s2b_preimage β j)),
        x ∈ V ∧ ContractibleSpace V ∧ V ≤ U) :
    QuasiIso (s2v_pushedConstantAugmentationInt
      (s2c_points.map (s2b_toExceptional β j))) := by
  let f := s2c_points.map (s2b_toExceptional β j)
  let : QuasiIso (s2v_pushedConstantAugmentation f) :=
    s2v_pushedConstantAugmentation_quasiIso β j hX
  let : QuasiIso (HomologicalComplex.extendMap (s2v_pushedConstantAugmentation f)
      ComplexShape.embeddingUpNat) :=
    (HomologicalComplex.quasiIso_extendMap_iff (s2v_pushedConstantAugmentation f)
      ComplexShape.embeddingUpNat).mpr inferInstance
  unfold s2v_pushedConstantAugmentationInt
  infer_instance


theorem s2v_preimage_pushedSingularInt_isFlasque
    {W B E : Over (Spec ↧ℂ)}
    [IsProjective W.hom] [IsProjective B.hom] [IsProjective E.hom]
    (β : W ⟶ B) (j : E ⟶ B) (q : ℤ) :
    TopCat.Sheaf.IsFlasque
      (((((TopCat.Sheaf.pushforward AddCommGrpCat.{0}
        (s2c_points.map (s2b_toExceptional β j))).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj
            (singularCochainSheafComplex ℂ (s2c_points.obj (s2b_preimage β j)))).extend
              ComplexShape.embeddingUpNat).X q) :=
  TopCat.Sheaf.extendNat_term_isFlasque _
    (fun n => s2v_preimage_pushedSingularNat_isFlasque β j n) q


def s2v_preimageResolutionCohomologyEquiv
    {W B E : Over (Spec ↧ℂ)}
    [IsProjective W.hom] [IsProjective B.hom] [IsProjective E.hom]
    (β : W ⟶ B) [IsFinite β.left] (j : E ⟶ B)
    (hX : ∀ (x : ComplexPoint (s2b_preimage β j))
      (U : Opens (ComplexPoint (s2b_preimage β j))), x ∈ U →
      ∃ V : Opens (ComplexPoint (s2b_preimage β j)),
        x ∈ V ∧ ContractibleSpace V ∧ V ≤ U) (n : ℕ) :
    (TopCat.Sheaf.globalSectionsComplexInt (s2c_points.obj E)
      ((((TopCat.Sheaf.pushforward AddCommGrpCat.{0}
        (s2c_points.map (s2b_toExceptional β j))).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj
            (singularCochainSheafComplex ℂ (s2c_points.obj (s2b_preimage β j)))).extend
              ComplexShape.embeddingUpNat)).homology (n : ℤ) ≃+
      Sheaf.H (s2c_coverSheaf (s2c_points.map (s2b_toExceptional β j))) n := by
  let f := s2c_points.map (s2b_toExceptional β j)
  let P := TopCat.Sheaf.pushforward AddCommGrpCat.{0} f
  let C : AnalyticAdditiveSheaf E :=
    P.obj ((TopCat.Sheaf.constantFunctor (s2c_points.obj (s2b_preimage β j))).obj
      (AddCommGrpCat.of ℂ))
  let S : CochainComplex (AnalyticAdditiveSheaf E) ℤ :=
    ((P.mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (singularCochainSheafComplex ℂ (s2c_points.obj (s2b_preimage β j)))).extend
        ComplexShape.embeddingUpNat
  let a : (CochainComplex.singleFunctor (AnalyticAdditiveSheaf E) 0).obj C ⟶ S :=
    s2v_pushedConstantAugmentationInt f
  let : S.IsStrictlyGE 0 := by dsimp only [S]; infer_instance
  let : QuasiIso a := s2v_pushedConstantAugmentationInt_quasiIso β j hX
  let e := s2v_resolutionCohomologyEquiv E C S a
    (fun q => s2v_preimage_pushedSingularInt_isFlasque β j q) n
  exact e.trans (((Sheaf.functorH (Opens.grothendieckTopology (s2c_points.obj E)) n).mapIso
    (s2v_coverSheaf_pushforwardConstantIso f).symm).addCommGroupIsoToAddEquiv)


theorem s2v_preimageResolutionCohomologyEquiv_deck
    {W B E : Over (Spec ↧ℂ)}
    [IsProjective W.hom] [IsProjective B.hom] [IsProjective E.hom]
    (β : W ⟶ B) [IsFinite β.left] (j : E ⟶ B)
    (hX : ∀ (x : ComplexPoint (s2b_preimage β j))
      (U : Opens (ComplexPoint (s2b_preimage β j))), x ∈ U →
      ∃ V : Opens (ComplexPoint (s2b_preimage β j)),
        x ∈ V ∧ ContractibleSpace V ∧ V ≤ U)
    (δ : s2c_points.obj (s2b_preimage β j) ⟶ s2c_points.obj (s2b_preimage β j))
    (hδ : δ ≫ s2c_points.map (s2b_toExceptional β j) =
      s2c_points.map (s2b_toExceptional β j)) (n : ℕ)
    (x : (TopCat.Sheaf.globalSectionsComplexInt (s2c_points.obj E)
      ((((TopCat.Sheaf.pushforward AddCommGrpCat.{0}
        (s2c_points.map (s2b_toExceptional β j))).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj
            (singularCochainSheafComplex ℂ (s2c_points.obj (s2b_preimage β j)))).extend
              ComplexShape.embeddingUpNat)).homology (n : ℤ)) :
    s2v_preimageResolutionCohomologyEquiv β j hX n
        (HomologicalComplex.homologyMap
          (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
            (s2c_points.obj E)).mapHomologicalComplex ℤᵘᵖ).map
              (HomologicalComplex.extendMap
                (s2v_pushedSingularCochainSheafComplexDeck
                  (s2c_points.map (s2b_toExceptional β j)) δ hδ).asHom
                ComplexShape.embeddingUpNat)) n x) =
      Sheaf.H.map.{0} (s2c_coverSheafDeck
        (s2c_points.map (s2b_toExceptional β j)) δ hδ) n
          (s2v_preimageResolutionCohomologyEquiv β j hX n x) := by
  let f := s2c_points.map (s2b_toExceptional β j)
  let P := TopCat.Sheaf.pushforward AddCommGrpCat.{0} f
  let C : AnalyticAdditiveSheaf E :=
    P.obj ((TopCat.Sheaf.constantFunctor (s2c_points.obj (s2b_preimage β j))).obj
      (AddCommGrpCat.of ℂ))
  let S : CochainComplex (AnalyticAdditiveSheaf E) ℤ :=
    ((P.mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (singularCochainSheafComplex ℂ (s2c_points.obj (s2b_preimage β j)))).extend
        ComplexShape.embeddingUpNat
  let a : (CochainComplex.singleFunctor (AnalyticAdditiveSheaf E) 0).obj C ⟶ S :=
    s2v_pushedConstantAugmentationInt f
  let : S.IsStrictlyGE 0 := by dsimp only [S]; infer_instance
  let : QuasiIso a := s2v_pushedConstantAugmentationInt_quasiIso β j hX
  let c := s2v_pushforwardDeck f δ hδ
    ((TopCat.Sheaf.constantFunctor (s2c_points.obj (s2b_preimage β j))).obj
      (AddCommGrpCat.of ℂ)) (s2v_constantSheafContinuousMap δ)
  let v := HomologicalComplex.extendMap
    (s2v_pushedSingularCochainSheafComplexDeck f δ hδ).asHom ComplexShape.embeddingUpNat
  let hS := fun q => s2v_preimage_pushedSingularInt_isFlasque β j q
  let e := s2v_resolutionCohomologyEquiv E C S a hS n
  let i := s2v_coverSheaf_pushforwardConstantIso f
  have h := s2v_resolutionCohomologyEquiv_map E C S a hS c v
    (s2v_pushedConstantAugmentationInt_deck f δ hδ) n x
  change e (HomologicalComplex.homologyMap
      (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
        (s2c_points.obj E)).mapHomologicalComplex ℤᵘᵖ).map v) n x) =
    Sheaf.H.map.{0} c n (e x) at h
  change Sheaf.H.map.{0} i.inv n (e (HomologicalComplex.homologyMap
      (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
        (s2c_points.obj E)).mapHomologicalComplex ℤᵘᵖ).map v) n x)) =
    Sheaf.H.map.{0} (s2c_coverSheafDeck f δ hδ) n (Sheaf.H.map.{0} i.inv n (e x))
  rw [h, ← Sheaf.H.map_comp_apply, ← Sheaf.H.map_comp_apply]
  exact congrArg (fun q => Sheaf.H.map.{0} q n (e x))
    (s2v_coverSheaf_pushforwardConstantIso_inv_deck f δ hδ)


def s2v_pushforwardGlobalSectionsNatIso {X Y : TopCat.{0}} (f : X ⟶ Y)
    (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} X) ℕ) :
    (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj
        (((TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj K)) ≅
    (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor X).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj K) := Iso.refl _


theorem s2v_pushforwardGlobalSectionsNatIso_deck {X Y : TopCat.{0}}
    (f : X ⟶ Y) (d : X ⟶ X) (hd : d ≫ f = f) :
    (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y).mapHomologicalComplex
      (ComplexShape.up ℕ)).map
        (s2v_pushedSingularCochainSheafComplexDeck f d hd).asHom) ≫
      (s2v_pushforwardGlobalSectionsNatIso f (singularCochainSheafComplex ℂ X)).hom =
    (s2v_pushforwardGlobalSectionsNatIso f (singularCochainSheafComplex ℂ X)).hom ≫
      (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor X).mapHomologicalComplex
        (ComplexShape.up ℕ)).map (s2v_singularCochainSheafComplexMap d)) ≫
      (s2v_pushforwardGlobalSectionsNatIso d (singularCochainSheafComplex ℂ X)).hom := by
  dsimp only [s2v_pushforwardGlobalSectionsNatIso, Iso.refl_hom]
  simp only [Category.comp_id, Category.id_comp]
  unfold s2v_pushedSingularCochainSheafComplexDeck
  simp only [Functor.map_comp, eqToHom_map, eqToHom_refl, Category.comp_id]
  all_goals rfl


def s2v_globalSheafCochainDeck {X : TopCat.{0}} (d : X ⟶ X) :
    globalSingularCochainSheafComplex ℂ X ⟶ globalSingularCochainSheafComplex ℂ X :=
  (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor X).mapHomologicalComplex
      (ComplexShape.up ℕ)).map (s2v_singularCochainSheafComplexMap d)) ≫
    (s2v_pushforwardGlobalSectionsNatIso d (singularCochainSheafComplex ℂ X)).hom


theorem s2v_topOpenToGlobalSingularCochainSheafComplex_deck {X : TopCat.{0}}
    (d : X ⟶ X) :
    topOpenToGlobalSingularCochainSheafComplex ℂ X ≫ s2v_globalSheafCochainDeck d =
      s2v_globalRawCochainDeck d ≫ topOpenToGlobalSingularCochainSheafComplex ℂ X := by
  apply HomologicalComplex.Hom.ext
  funext n
  simp only [HomologicalComplex.comp_f, topOpenToGlobalSingularCochainSheafComplex_f]
  change (toSheafify (Opens.grothendieckTopology X)
      (singularCochainPresheaf ℂ X n)).app (op ⊤) ≫
        (s2v_singularCochainSheafMap d n).hom.app (op ⊤) =
    (s2v_singularCochainPresheafMap d n).app (op ⊤) ≫
      (toSheafify (Opens.grothendieckTopology X)
        (singularCochainPresheaf ℂ X n)).app (op ⊤)
  exact congrArg (fun a => a.app (op ⊤)) (s2v_singularCochainSheafMap_unit d n)


def s2v_singularToGlobalPushedResolutionEquiv {X Y : TopCat.{0}}
    [T2Space X] [ParacompactSpace X] (f : X ⟶ Y) (n : ℕ) :
    Cohomology ℂ X n ≃+
      (TopCat.Sheaf.globalSectionsComplexInt Y
        ((((TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj (singularCochainSheafComplex ℂ X)).extend
            ComplexShape.embeddingUpNat)).homology (n : ℤ) := by
  let Γ := TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y
  let K := ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj (singularCochainSheafComplex ℂ X)
  let G := (Γ.mapHomologicalComplex (ComplexShape.up ℕ)).obj K
  let : QuasiIso (topOpenToGlobalSingularCochainSheafComplex ℂ X) :=
    spec_topOpenToGlobalSingularCochainSheafComplex_quasiIso_aux ℂ X
  let t := asIso (HomologicalComplex.homologyMap
    (topOpenToGlobalSingularCochainSheafComplex ℂ X) n)
  let g := s2v_pushforwardGlobalSectionsNatIso f (singularCochainSheafComplex ℂ X)
  let j := G.extendHomologyIso ComplexShape.embeddingUpNat (j := n) rfl
  let i := HomologicalComplex.mapExtendCanonicalIso Γ K ComplexShape.embeddingUpNat
  exact (ordinarySingularCohomologyEquivGlobalRaw ℂ X n).trans
    (t.addCommGroupIsoToAddEquiv.trans
      (((HomologicalComplex.homologyMapIso g.symm n).addCommGroupIsoToAddEquiv).trans
        (j.symm.addCommGroupIsoToAddEquiv.trans
          (HomologicalComplex.homologyMapIso i.symm (n : ℤ)).addCommGroupIsoToAddEquiv)))

theorem s2v_singularToGlobalPushedResolutionEquiv_deck {X Y : TopCat.{0}}
    [T2Space X] [ParacompactSpace X] (f : X ⟶ Y) (d : X ⟶ X)
    (hd : d ≫ f = f) (n : ℕ) (x : Cohomology ℂ X n) :
    s2v_singularToGlobalPushedResolutionEquiv f n (cohomologyMap ℂ n d x) =
      HomologicalComplex.homologyMap
        (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y).mapHomologicalComplex (ComplexShape.up ℤ)).map
            (HomologicalComplex.extendMap
              (s2v_pushedSingularCochainSheafComplexDeck f d hd).asHom
                ComplexShape.embeddingUpNat)) (n : ℤ)
          (s2v_singularToGlobalPushedResolutionEquiv f n x) := by
  let Γ := TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y
  let K := ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj (singularCochainSheafComplex ℂ X)
  let G := (Γ.mapHomologicalComplex (ComplexShape.up ℕ)).obj K
  let p := (s2v_pushedSingularCochainSheafComplexDeck f d hd).asHom
  let pΓ := (Γ.mapHomologicalComplex (ComplexShape.up ℕ)).map p
  let g := s2v_pushforwardGlobalSectionsNatIso f (singularCochainSheafComplex ℂ X)
  let j := G.extendHomologyIso ComplexShape.embeddingUpNat (j := n) rfl
  let i := HomologicalComplex.mapExtendCanonicalIso Γ K ComplexShape.embeddingUpNat
  have hp : pΓ ≫ g.hom = g.hom ≫ s2v_globalSheafCochainDeck d :=
    s2v_pushforwardGlobalSectionsNatIso_deck f d hd
  have ht (w) := (homologyMap_apply_of_comm'
    (s2v_topOpenToGlobalSingularCochainSheafComplex_deck d) n w).symm
  have hg (w) := homologyMap_apply_of_comm'
    (inv_comp_eq_of_comp_hom g hp).symm n w
  have hj (w : G.homology n) :
      j.inv (HomologicalComplex.homologyMap pΓ n w) =
        HomologicalComplex.homologyMap
          (HomologicalComplex.extendMap pΓ ComplexShape.embeddingUpNat) (n : ℤ) (j.inv w) := by
    exact ConcreteCategory.congr_hom
      (s2v_extendHomologyIso_inv_naturality G pΓ n) w
  have hi (w) := homologyMap_apply_of_comm'
    (HomologicalComplex.mapExtendCanonicalIso_inv_naturality Γ p
      ComplexShape.embeddingUpNat) (n : ℤ) w
  change HomologicalComplex.homologyMap i.inv (n : ℤ)
      (j.inv (HomologicalComplex.homologyMap g.inv n
        (HomologicalComplex.homologyMap
          (topOpenToGlobalSingularCochainSheafComplex ℂ X) n
          (ordinarySingularCohomologyEquivGlobalRaw ℂ X n (cohomologyMap ℂ n d x))))) =
    HomologicalComplex.homologyMap
      ((Γ.mapHomologicalComplex (ComplexShape.up ℤ)).map
        (HomologicalComplex.extendMap p ComplexShape.embeddingUpNat)) (n : ℤ)
      (HomologicalComplex.homologyMap i.inv (n : ℤ)
        (j.inv (HomologicalComplex.homologyMap g.inv n
          (HomologicalComplex.homologyMap
            (topOpenToGlobalSingularCochainSheafComplex ℂ X) n
            (ordinarySingularCohomologyEquivGlobalRaw ℂ X n x)))))
  rw [s2v_ordinarySingularCohomologyEquivGlobalRaw_deck, ht]
  erw [hg]
  rw [hj, hi]

def s2v_actualFiniteCoverCohomologyEquiv
    {W B E : Over (Spec ↧ℂ)}
    [IsProjective W.hom] [IsProjective B.hom] [IsProjective E.hom]
    (β : W ⟶ B) [IsFinite β.left] (j : E ⟶ B)
    (hX : ∀ (x : ComplexPoint (s2b_preimage β j))
      (U : Opens (ComplexPoint (s2b_preimage β j))), x ∈ U →
      ∃ V : Opens (ComplexPoint (s2b_preimage β j)),
        x ∈ V ∧ ContractibleSpace V ∧ V ≤ U) (n : ℕ) :
    Cohomology ℂ (s2c_points.obj (s2b_preimage β j)) n ≃+
      Sheaf.H (s2c_coverSheaf (s2c_points.map (s2b_toExceptional β j))) n := by
  letI : T2Space (s2c_points.obj (s2b_preimage β j)) := s2v_pullback_points_t2 β j
  letI : ∀ U : Opens (ComplexPoint (s2b_preimage β j)), ParacompactSpace U :=
    s2v_projective_preimage_openParacompactSpace β j
  letI : ParacompactSpace (s2c_points.obj (s2b_preimage β j)) :=
    (Homeomorph.Set.univ (ComplexPoint (s2b_preimage β j))).paracompactSpace_iff.mp
      (inferInstance : ParacompactSpace (⊤ : Opens (ComplexPoint (s2b_preimage β j))))
  exact (s2v_singularToGlobalPushedResolutionEquiv
    (s2c_points.map (s2b_toExceptional β j)) n).trans
      (s2v_preimageResolutionCohomologyEquiv β j hX n)

theorem s2v_actualFiniteCoverCohomologyEquiv_deck
    {W B E : Over (Spec ↧ℂ)}
    [IsProjective W.hom] [IsProjective B.hom] [IsProjective E.hom]
    (β : W ⟶ B) [IsFinite β.left] (j : E ⟶ B)
    (hX : ∀ (x : ComplexPoint (s2b_preimage β j))
      (U : Opens (ComplexPoint (s2b_preimage β j))), x ∈ U →
      ∃ V : Opens (ComplexPoint (s2b_preimage β j)),
        x ∈ V ∧ ContractibleSpace V ∧ V ≤ U) (n : ℕ)
    (δ : s2c_points.obj (s2b_preimage β j) ⟶ s2c_points.obj (s2b_preimage β j))
    (hδ : δ ≫ s2c_points.map (s2b_toExceptional β j) =
      s2c_points.map (s2b_toExceptional β j))
    (x : Cohomology ℂ (s2c_points.obj (s2b_preimage β j)) n) :
    s2v_actualFiniteCoverCohomologyEquiv β j hX n (cohomologyMap ℂ n δ x) =
      Sheaf.H.map.{0} (s2c_coverSheafDeck
        (s2c_points.map (s2b_toExceptional β j)) δ hδ) n
          (s2v_actualFiniteCoverCohomologyEquiv β j hX n x) := by
  letI : T2Space (s2c_points.obj (s2b_preimage β j)) := s2v_pullback_points_t2 β j
  letI : ∀ U : Opens (ComplexPoint (s2b_preimage β j)), ParacompactSpace U :=
    s2v_projective_preimage_openParacompactSpace β j
  letI : ParacompactSpace (s2c_points.obj (s2b_preimage β j)) :=
    (Homeomorph.Set.univ (ComplexPoint (s2b_preimage β j))).paracompactSpace_iff.mp
      (inferInstance : ParacompactSpace (⊤ : Opens (ComplexPoint (s2b_preimage β j))))
  change s2v_preimageResolutionCohomologyEquiv β j hX n
      (s2v_singularToGlobalPushedResolutionEquiv
        (s2c_points.map (s2b_toExceptional β j)) n (cohomologyMap ℂ n δ x)) = _
  rw [s2v_singularToGlobalPushedResolutionEquiv_deck
    (s2c_points.map (s2b_toExceptional β j)) δ hδ n x,
    s2v_preimageResolutionCohomologyEquiv_deck]
  rfl

theorem s2v_singularToGlobalPushedResolutionEquiv_scalar {X Y : TopCat.{0}}
    [T2Space X] [ParacompactSpace X] (f : X ⟶ Y) (z : ℂ) (n : ℕ) (x : Cohomology ℂ X n) :
    s2v_singularToGlobalPushedResolutionEquiv f n (z • x) =
      HomologicalComplex.homologyMap
        (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y).mapHomologicalComplex (ComplexShape.up ℤ)).map
            (HomologicalComplex.extendMap
              (((TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).mapHomologicalComplex
                (ComplexShape.up ℕ)).map (singularCochainSheafComplexScalar ℂ X z))
                ComplexShape.embeddingUpNat)) (n : ℤ)
          (s2v_singularToGlobalPushedResolutionEquiv f n x) := by
  let Γ := TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y
  let K := ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj (singularCochainSheafComplex ℂ X)
  let G := (Γ.mapHomologicalComplex (ComplexShape.up ℕ)).obj K
  let p := (((TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).mapHomologicalComplex
                (ComplexShape.up ℕ)).map (singularCochainSheafComplexScalar ℂ X z))
  let pΓ := (Γ.mapHomologicalComplex (ComplexShape.up ℕ)).map p
  let g := s2v_pushforwardGlobalSectionsNatIso f (singularCochainSheafComplex ℂ X)
  let j := G.extendHomologyIso ComplexShape.embeddingUpNat (j := n) rfl
  let i := HomologicalComplex.mapExtendCanonicalIso Γ K ComplexShape.embeddingUpNat
  have hp : pΓ ≫ g.hom = g.hom ≫ globalSingularCochainSheafComplexScalar ℂ X z :=
    by rfl
  have ht (w) := (homologyMap_apply_of_comm'
    (topOpenToGlobalSingularCochainSheafComplex_scalar ℂ X z) n w).symm
  have hg (w) := homologyMap_apply_of_comm'
    (inv_comp_eq_of_comp_hom g hp).symm n w
  have hj (w : G.homology n) :
      j.inv (HomologicalComplex.homologyMap pΓ n w) =
        HomologicalComplex.homologyMap
          (HomologicalComplex.extendMap pΓ ComplexShape.embeddingUpNat) (n : ℤ) (j.inv w) := by
    exact ConcreteCategory.congr_hom
      (s2v_extendHomologyIso_inv_naturality G pΓ n) w
  have hi (w) := homologyMap_apply_of_comm'
    (HomologicalComplex.mapExtendCanonicalIso_inv_naturality Γ p
      ComplexShape.embeddingUpNat) (n : ℤ) w
  change HomologicalComplex.homologyMap i.inv (n : ℤ)
      (j.inv (HomologicalComplex.homologyMap g.inv n
        (HomologicalComplex.homologyMap
          (topOpenToGlobalSingularCochainSheafComplex ℂ X) n
          (ordinarySingularCohomologyEquivGlobalRaw ℂ X n (z • x))))) =
    HomologicalComplex.homologyMap
      ((Γ.mapHomologicalComplex (ComplexShape.up ℤ)).map
        (HomologicalComplex.extendMap p ComplexShape.embeddingUpNat)) (n : ℤ)
      (HomologicalComplex.homologyMap i.inv (n : ℤ)
        (j.inv (HomologicalComplex.homologyMap g.inv n
          (HomologicalComplex.homologyMap
            (topOpenToGlobalSingularCochainSheafComplex ℂ X) n
            (ordinarySingularCohomologyEquivGlobalRaw ℂ X n x)))))
  rw [ordinarySingularCohomologyEquivGlobalRaw_smul, ht]
  erw [hg]
  rw [hj, hi]

theorem s2v_pushedConstantAugmentation_scalar {X Y : TopCat.{0}}
    (f : X ⟶ Y) (z : ℂ) :
    s2v_pushedConstantAugmentation f ≫
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).mapHomologicalComplex
        (ComplexShape.up ℕ)).map (singularCochainSheafComplexScalar ℂ X z) =
      (CochainComplex.single₀ (TopCat.Sheaf AddCommGrpCat.{0} Y)).map
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).map
          ((TopCat.Sheaf.constantFunctor X).map
            (AddCommGrpCat.ofHom (AddMonoidHom.mulLeft z)))) ≫
        s2v_pushedConstantAugmentation f := by
  let P := TopCat.Sheaf.pushforward AddCommGrpCat.{0} f
  let M := P.mapHomologicalComplex (ComplexShape.up ℕ)
  let c := (TopCat.Sheaf.constantFunctor X).map
    (AddCommGrpCat.ofHom (AddMonoidHom.mulLeft z))
  let i := HomologicalComplex.singleMapHomologicalComplex P (ComplexShape.up ℕ) 0
  change (i.inv.app _ ≫ M.map (constantsToSingularCochainSheafComplex ℂ X)) ≫ _ =
    _ ≫ (i.inv.app _ ≫ M.map (constantsToSingularCochainSheafComplex ℂ X))
  rw [Category.assoc, ← M.map_comp, constantsToSingularCochainSheafComplex_scalar,
    M.map_comp, ← Category.assoc]
  exact congrArg (fun q => q ≫ M.map (constantsToSingularCochainSheafComplex ℂ X))
    (i.inv.naturality c).symm

theorem s2v_pushedConstantAugmentationInt_scalar {X Y : TopCat.{0}}
    (f : X ⟶ Y) (z : ℂ) :
    s2v_pushedConstantAugmentationInt f ≫
        HomologicalComplex.extendMap
          (((TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).mapHomologicalComplex
            (ComplexShape.up ℕ)).map (singularCochainSheafComplexScalar ℂ X z))
          ComplexShape.embeddingUpNat =
      (CochainComplex.singleFunctor (TopCat.Sheaf AddCommGrpCat.{0} Y) 0).map
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).map
          ((TopCat.Sheaf.constantFunctor X).map
            (AddCommGrpCat.ofHom (AddMonoidHom.mulLeft z)))) ≫ s2v_pushedConstantAugmentationInt f := by
  let C := (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).obj
    ((TopCat.Sheaf.constantFunctor X).obj (AddCommGrpCat.of ℂ))
  let c := (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).map
    ((TopCat.Sheaf.constantFunctor X).map
      (AddCommGrpCat.ofHom (AddMonoidHom.mulLeft z)))
  let i := HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat C 0 0 rfl
  have hi := inv_comp_eq_of_comp_hom i
    (HomologicalComplex.extendSingleIso_hom_naturality ComplexShape.embeddingUpNat c 0 0 rfl)
  change (i.inv ≫ HomologicalComplex.extendMap (s2v_pushedConstantAugmentation f)
      ComplexShape.embeddingUpNat) ≫ _ = _ ≫
    (i.inv ≫ HomologicalComplex.extendMap (s2v_pushedConstantAugmentation f)
      ComplexShape.embeddingUpNat)
  rw [Category.assoc, ← HomologicalComplex.extendMap_comp,
    s2v_pushedConstantAugmentation_scalar, HomologicalComplex.extendMap_comp,
    ← Category.assoc, hi, Category.assoc]


theorem s2v_preimageResolutionCohomologyEquiv_scalar
    {W B E : Over (Spec ↧ℂ)}
    [IsProjective W.hom] [IsProjective B.hom] [IsProjective E.hom]
    (β : W ⟶ B) [IsFinite β.left] (j : E ⟶ B)
    (hX : ∀ (x : ComplexPoint (s2b_preimage β j))
      (U : Opens (ComplexPoint (s2b_preimage β j))), x ∈ U →
      ∃ V : Opens (ComplexPoint (s2b_preimage β j)),
        x ∈ V ∧ ContractibleSpace V ∧ V ≤ U)
    (z : ℂ) (n : ℕ)
    (x : (TopCat.Sheaf.globalSectionsComplexInt (s2c_points.obj E)
      ((((TopCat.Sheaf.pushforward AddCommGrpCat.{0}
        (s2c_points.map (s2b_toExceptional β j))).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj
            (singularCochainSheafComplex ℂ (s2c_points.obj (s2b_preimage β j)))).extend
              ComplexShape.embeddingUpNat)).homology (n : ℤ)) :
    s2v_preimageResolutionCohomologyEquiv β j hX n
        (HomologicalComplex.homologyMap
          (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
            (s2c_points.obj E)).mapHomologicalComplex ℤᵘᵖ).map
              (HomologicalComplex.extendMap
                (((TopCat.Sheaf.pushforward AddCommGrpCat.{0}
                  (s2c_points.map (s2b_toExceptional β j))).mapHomologicalComplex
                    (ComplexShape.up ℕ)).map (singularCochainSheafComplexScalar ℂ
                      (s2c_points.obj (s2b_preimage β j)) z))
                ComplexShape.embeddingUpNat)) n x) =
      Sheaf.H.map.{0} (s2c_coverSheafScalar
        (s2c_points.map (s2b_toExceptional β j)) z) n
          (s2v_preimageResolutionCohomologyEquiv β j hX n x) := by
  let f := s2c_points.map (s2b_toExceptional β j)
  let P := TopCat.Sheaf.pushforward AddCommGrpCat.{0} f
  let C : AnalyticAdditiveSheaf E :=
    P.obj ((TopCat.Sheaf.constantFunctor (s2c_points.obj (s2b_preimage β j))).obj
      (AddCommGrpCat.of ℂ))
  let S : CochainComplex (AnalyticAdditiveSheaf E) ℤ :=
    ((P.mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (singularCochainSheafComplex ℂ (s2c_points.obj (s2b_preimage β j)))).extend
        ComplexShape.embeddingUpNat
  let a : (CochainComplex.singleFunctor (AnalyticAdditiveSheaf E) 0).obj C ⟶ S :=
    s2v_pushedConstantAugmentationInt f
  let : S.IsStrictlyGE 0 := by dsimp only [S]; infer_instance
  let : QuasiIso a := s2v_pushedConstantAugmentationInt_quasiIso β j hX
  let c := P.map ((TopCat.Sheaf.constantFunctor
    (s2c_points.obj (s2b_preimage β j))).map
      (AddCommGrpCat.ofHom (AddMonoidHom.mulLeft z)))
  let v := HomologicalComplex.extendMap
    ((P.mapHomologicalComplex (ComplexShape.up ℕ)).map
      (singularCochainSheafComplexScalar ℂ (s2c_points.obj (s2b_preimage β j)) z))
    ComplexShape.embeddingUpNat
  let hS := fun q => s2v_preimage_pushedSingularInt_isFlasque β j q
  let e := s2v_resolutionCohomologyEquiv E C S a hS n
  let i := s2v_coverSheaf_pushforwardConstantIso f
  have h := s2v_resolutionCohomologyEquiv_map E C S a hS c v
    (s2v_pushedConstantAugmentationInt_scalar f z) n x
  change e (HomologicalComplex.homologyMap
      (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
        (s2c_points.obj E)).mapHomologicalComplex ℤᵘᵖ).map v) n x) =
    Sheaf.H.map.{0} c n (e x) at h
  change Sheaf.H.map.{0} i.inv n (e (HomologicalComplex.homologyMap
      (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
        (s2c_points.obj E)).mapHomologicalComplex ℤᵘᵖ).map v) n x)) =
    Sheaf.H.map.{0} (s2c_coverSheafScalar f z) n (Sheaf.H.map.{0} i.inv n (e x))
  rw [h, ← Sheaf.H.map_comp_apply, ← Sheaf.H.map_comp_apply]
  exact congrArg (fun q => Sheaf.H.map.{0} q n (e x))
    (s2v_coverSheaf_pushforwardConstantIso_inv_scalar f z)


theorem s2v_actualFiniteCoverCohomologyEquiv_scalar
    {W B E : Over (Spec ↧ℂ)}
    [IsProjective W.hom] [IsProjective B.hom] [IsProjective E.hom]
    (β : W ⟶ B) [IsFinite β.left] (j : E ⟶ B)
    (hX : ∀ (x : ComplexPoint (s2b_preimage β j))
      (U : Opens (ComplexPoint (s2b_preimage β j))), x ∈ U →
      ∃ V : Opens (ComplexPoint (s2b_preimage β j)),
        x ∈ V ∧ ContractibleSpace V ∧ V ≤ U) (n : ℕ)
    (z : ℂ)
    (x : Cohomology ℂ (s2c_points.obj (s2b_preimage β j)) n) :
    s2v_actualFiniteCoverCohomologyEquiv β j hX n (z • x) =
      Sheaf.H.map.{0} (s2c_coverSheafScalar
        (s2c_points.map (s2b_toExceptional β j)) z) n
          (s2v_actualFiniteCoverCohomologyEquiv β j hX n x) := by
  letI : T2Space (s2c_points.obj (s2b_preimage β j)) := s2v_pullback_points_t2 β j
  letI : ∀ U : Opens (ComplexPoint (s2b_preimage β j)), ParacompactSpace U :=
    s2v_projective_preimage_openParacompactSpace β j
  letI : ParacompactSpace (s2c_points.obj (s2b_preimage β j)) :=
    (Homeomorph.Set.univ (ComplexPoint (s2b_preimage β j))).paracompactSpace_iff.mp
      (inferInstance : ParacompactSpace (⊤ : Opens (ComplexPoint (s2b_preimage β j))))
  change s2v_preimageResolutionCohomologyEquiv β j hX n
      (s2v_singularToGlobalPushedResolutionEquiv
        (s2c_points.map (s2b_toExceptional β j)) n (z • x)) = _
  rw [s2v_singularToGlobalPushedResolutionEquiv_scalar,
    s2v_preimageResolutionCohomologyEquiv_scalar]
  rfl

end HodgeLean.Foundations.Program
