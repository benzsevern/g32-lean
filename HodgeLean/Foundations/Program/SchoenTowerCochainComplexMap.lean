import HodgeLean.Foundations.Program.SchoenTowerCochainMap
import HodgeLean.Foundations.Program.SchoenTowerPushedResolution

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Program

attribute [local instance] s2v_sheafPushforward_additive

def s2v_singularCochainSheafComplexMap {X Y : TopCat.{0}} (g : X ⟶ Y) :
    singularCochainSheafComplex ℂ Y ⟶
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} g).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj (singularCochainSheafComplex ℂ X) where
  f n := s2v_singularCochainSheafMap g n
  comm' i j hij := by
    have hj : i + 1 = j := hij
    subst j
    change s2v_singularCochainSheafMap g i ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat.{0} g).map
          ((singularCochainSheafComplex ℂ X).d i (i + 1)) =
      (singularCochainSheafComplex ℂ Y).d i (i + 1) ≫
        s2v_singularCochainSheafMap g (i + 1)
    rw [singularCochainSheafComplex_d, singularCochainSheafComplex_d]
    exact s2v_singularCochainSheafMap_coboundary g i

def s2v_singularCochainSheafComplexIntMap {X Y : TopCat.{0}} (g : X ⟶ Y) :
    (singularCochainSheafComplex ℂ Y).extend ComplexShape.embeddingUpNat ⟶
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} g).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
          ((singularCochainSheafComplex ℂ X).extend ComplexShape.embeddingUpNat) :=
  HomologicalComplex.extendMap (s2v_singularCochainSheafComplexMap g)
      ComplexShape.embeddingUpNat ≫
    (HomologicalComplex.mapExtendCanonicalIso
      (TopCat.Sheaf.pushforward AddCommGrpCat.{0} g)
        (singularCochainSheafComplex ℂ X) ComplexShape.embeddingUpNat).inv

def s2v_pushedSingularCochainSheafComplexDeck {X Y : TopCat.{0}}
    (f : X ⟶ Y) (d : X ⟶ X) (hd : d ≫ f = f) :
    CategoryTheory.End (((TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (singularCochainSheafComplex ℂ X)) :=
  .of <| ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).mapHomologicalComplex
      (ComplexShape.up ℕ)).map (s2v_singularCochainSheafComplexMap d) ≫
    eqToHom (by
      change ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} (d ≫ f)).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj (singularCochainSheafComplex ℂ X) = _
      rw [hd])

def s2v_pushedSingularCochainSheafComplexIntDeck {X Y : TopCat.{0}}
    (f : X ⟶ Y) (d : X ⟶ X) (hd : d ≫ f = f) :
    CategoryTheory.End (((TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj
        ((singularCochainSheafComplex ℂ X).extend ComplexShape.embeddingUpNat)) :=
  .of <| ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).mapHomologicalComplex
      (ComplexShape.up ℤ)).map (s2v_singularCochainSheafComplexIntMap d) ≫
    eqToHom (by
      change ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} (d ≫ f)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
            ((singularCochainSheafComplex ℂ X).extend ComplexShape.embeddingUpNat) = _
      rw [hd])

open AlgebraicGeometry ComplexPoint

def s2v_hypercohomologySingleEquiv (X : Over (Spec ↧ℂ))
    (F : AnalyticAdditiveSheaf X) (n : ℕ) :
    Hypercohomology X ((HomologicalComplex.single (AnalyticAdditiveSheaf X)
      (ComplexShape.up ℤ) 0).obj F) n ≃+ Sheaf.H F n := by
  letI : HasDerivedCategory (AnalyticAdditiveSheaf X) := analyticHasDerivedCategory X
  have h : HasExt.{0} (AnalyticAdditiveSheaf X) := inferInstance
  have hsmall := h ((constantSheaf (Opens.grothendieckTopology
    (TopCat.of (ComplexPoint X))) AddCommGrpCat).obj (AddCommGrpCat.of (ULift ℤ))) F
  let e := (Localization.SmallShiftedHom.precompEquiv.{1}
    (W := analyticQuasiIsomorphisms X)
    (constantIntegerSheafComplexIntIsoSingleULift X).hom
    ((HomologicalComplex.mem_quasiIso_iff _).mpr inferInstance)
    (a := (n : ℤ))).symm.trans
      (@Localization.SmallShiftedHom.chgUniv.{0, 1} _ _ _ _ _ _ _ _ _
        (analyticHasSmallLocalizedShiftedHom X _ _) hsmall)
  let χ := Localization.SmallShiftedHom.mk₀Inv
    (W := analyticQuasiIsomorphisms X) (0 : ℤ) rfl
    (constantIntegerSheafComplexIntIsoSingleULift X).hom
    ((HomologicalComplex.mem_quasiIso_iff _).mpr inferInstance)
  refine { toEquiv := e, map_add' := ?_ }
  intro α β
  apply Abelian.Ext.ext
  rw [Abelian.Ext.add_hom]
  show Localization.SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q
      (Localization.SmallShiftedHom.chgUniv.{0} (χ.comp (α + β) (add_zero (n : ℤ)))) =
    Localization.SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q
      (Localization.SmallShiftedHom.chgUniv.{0} (χ.comp α (add_zero (n : ℤ)))) +
    Localization.SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q
      (Localization.SmallShiftedHom.chgUniv.{0} (χ.comp β (add_zero (n : ℤ))))
  simp only [Localization.SmallShiftedHom.equiv_chgUniv,
    Localization.SmallShiftedHom.equiv_comp, hypercohomologyEquiv_add, ShiftedHom.comp_add]


attribute [local implicit_reducible] TopCat.Sheaf TopCat.instCategorySheaf._aux_1
  TopCat.instCategorySheaf._aux_3 TopCat.instCategorySheaf._aux_5

theorem s2v_hypercohomologySingleEquiv_map (X : Over (Spec ↧ℂ))
    {F G : AnalyticAdditiveSheaf X} (f : F ⟶ G) (n : ℕ)
    (α : Hypercohomology X ((CochainComplex.singleFunctor
      (AnalyticAdditiveSheaf X) 0).obj F) n) :
    s2v_hypercohomologySingleEquiv X G n
        (hypercohomologyMap X ((CochainComplex.singleFunctor
          (AnalyticAdditiveSheaf X) 0).map f) n α) =
      Sheaf.H.map.{0} f n (s2v_hypercohomologySingleEquiv X F n α) := by
  letI : HasDerivedCategory (AnalyticAdditiveSheaf X) := analyticHasDerivedCategory X
  let χ := Localization.SmallShiftedHom.mk₀Inv
    (W := analyticQuasiIsomorphisms X) (0 : ℤ) rfl
    (constantIntegerSheafComplexIntIsoSingleULift X).hom
    ((HomologicalComplex.mem_quasiIso_iff _).mpr inferInstance)
  let μ := Localization.SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) (0 : ℤ) rfl
    ((CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).map f)
  have h : (χ.comp α (add_zero (n : ℤ))).comp μ (zero_add (n : ℤ)) =
      χ.comp (hypercohomologyMap X ((CochainComplex.singleFunctor
        (AnalyticAdditiveSheaf X) 0).map f) n α) (add_zero (n : ℤ)) :=
    Localization.SmallShiftedHom.comp_assoc (analyticQuasiIsomorphisms X) χ α μ
      (add_zero (n : ℤ)) (zero_add (n : ℤ)) (by simp)
  apply Abelian.Ext.ext.{1, 0} (C := AnalyticAdditiveSheaf X)
  rw [Sheaf.H.map_apply.{0}, Abelian.Ext.comp_hom, Abelian.Ext.mk₀_hom]
  change Localization.SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q
      (Localization.SmallShiftedHom.chgUniv.{0}
        (χ.comp (hypercohomologyMap X ((CochainComplex.singleFunctor
          (AnalyticAdditiveSheaf X) 0).map f) n α) (add_zero (n : ℤ)))) =
    (Localization.SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q
      (Localization.SmallShiftedHom.chgUniv.{0} (χ.comp α (add_zero (n : ℤ))))).comp
        (ShiftedHom.mk₀ (0 : ℤ) rfl (DerivedCategory.Q.map
          ((CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).map f)))
        (zero_add (n : ℤ))
  have h' := congrArg
    (Localization.SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q) h
  simpa only [μ, Localization.SmallShiftedHom.equiv_chgUniv,
    Localization.SmallShiftedHom.equiv_comp, Localization.SmallShiftedHom.equiv_mk₀] using h'.symm


def s2v_hypercohomologyPostcompEquiv (X : Over (Spec ↧ℂ))
    {S T : CochainComplex (AnalyticAdditiveSheaf X) ℤ} (a : S ⟶ T) [QuasiIso a]
    (n : ℤ) : Hypercohomology X S n ≃+ Hypercohomology X T n where
  toEquiv := Localization.SmallShiftedHom.postcompEquiv a
    ((HomologicalComplex.mem_quasiIso_iff _).mpr inferInstance)
  map_add' α β := (hypercohomologyMap X a n).map_add α β


theorem s2v_hypercohomologyPostcompEquiv_symm_map (X : Over (Spec ↧ℂ))
    {S T : CochainComplex (AnalyticAdditiveSheaf X) ℤ} (a : S ⟶ T) [QuasiIso a]
    (u : S ⟶ S) (v : T ⟶ T) (h : a ≫ v = u ≫ a) (n : ℤ)
    (x : Hypercohomology X T n) :
    (s2v_hypercohomologyPostcompEquiv X a n).symm (hypercohomologyMap X v n x) =
      hypercohomologyMap X u n ((s2v_hypercohomologyPostcompEquiv X a n).symm x) := by
  rw [AddEquiv.symm_apply_eq]
  obtain ⟨y, rfl⟩ := (s2v_hypercohomologyPostcompEquiv X a n).surjective x
  rw [AddEquiv.symm_apply_apply]
  change hypercohomologyMap X v n (hypercohomologyMap X a n y) =
    hypercohomologyMap X a n (hypercohomologyMap X u n y)
  rw [← hypercohomologyMap_comp_apply, ← hypercohomologyMap_comp_apply, h]


def s2v_resolutionCohomologyEquiv (X : Over (Spec ↧ℂ))
    (F : AnalyticAdditiveSheaf X) (S : CochainComplex (AnalyticAdditiveSheaf X) ℤ)
    [S.IsStrictlyGE 0]
    (a : (CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).obj F ⟶ S)
    [QuasiIso a] (hS : ∀ q : ℤ, (S.X q).IsFlasque) (n : ℕ) :
    (TopCat.Sheaf.globalSectionsComplexInt (TopCat.of (ComplexPoint X)) S).homology
        (n : ℤ) ≃+ Sheaf.H F n :=
  (AddEquiv.ofBijective (globalSectionsToHypercohomology X S n)
    (globalSectionsToHypercohomology_bijective_of_flasque X S 0 hS n)).trans
      ((s2v_hypercohomologyPostcompEquiv X a n).symm.trans
        (s2v_hypercohomologySingleEquiv X F n))


theorem s2v_resolutionCohomologyEquiv_map (X : Over (Spec ↧ℂ))
    (F : AnalyticAdditiveSheaf X) (S : CochainComplex (AnalyticAdditiveSheaf X) ℤ)
    [S.IsStrictlyGE 0]
    (a : (CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).obj F ⟶ S)
    [QuasiIso a] (hS : ∀ q : ℤ, (S.X q).IsFlasque)
    (u : F ⟶ F) (v : S ⟶ S)
    (h : a ≫ v = (CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).map u ≫ a)
    (n : ℕ) (x : (TopCat.Sheaf.globalSectionsComplexInt
      (TopCat.of (ComplexPoint X)) S).homology (n : ℤ)) :
    s2v_resolutionCohomologyEquiv X F S a hS n
        (HomologicalComplex.homologyMap
          (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
            (TopCat.of (ComplexPoint X))).mapHomologicalComplex ℤᵘᵖ).map v) n x) =
      Sheaf.H.map.{0} u n (s2v_resolutionCohomologyEquiv X F S a hS n x) := by
  change s2v_hypercohomologySingleEquiv X F n
      ((s2v_hypercohomologyPostcompEquiv X a n).symm
        (globalSectionsToHypercohomology X S n
          (HomologicalComplex.homologyMap
            (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
              (TopCat.of (ComplexPoint X))).mapHomologicalComplex ℤᵘᵖ).map v) n x))) =
    Sheaf.H.map.{0} u n (s2v_hypercohomologySingleEquiv X F n
      ((s2v_hypercohomologyPostcompEquiv X a n).symm
        (globalSectionsToHypercohomology X S n x)))
  rw [globalSectionsToHypercohomology_naturality,
    s2v_hypercohomologyPostcompEquiv_symm_map X a _ _ h,
    s2v_hypercohomologySingleEquiv_map]


end HodgeLean.Foundations.Program
