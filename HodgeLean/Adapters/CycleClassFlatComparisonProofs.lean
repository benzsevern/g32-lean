import HodgeLean.Adapters.CycleClassFlatComparisonCore
import HodgeLean.Adapters.CycleClassSmoothCharts
import HodgeLean.Adapters.CycleClassFlatComparisonDefs
import HodgeLean.RealDefs.FundamentalClass.SingularChase
import HodgeLean.Adapters.HolomorphicPeriodsComparisonProofs
import HodgeLean.Adapters.ResolutionClassActionProofs
import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.RelativeHomotopyInvariance
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.Unramified.LocalStructure
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.Localization.FractionRing

/-! # Proof obligations for supported flat-pullback comparison

Each declaration isolates one geometric or comparison step. HC no distance;
AV milestone no distance.
-/

noncomputable section

set_option maxRecDepth 2048
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open AlgebraicTopology.Singular TopologicalSpace
open HodgeLean.RealDefs

namespace HodgeLean.Adapters

set_option backward.isDefEq.respectTransparency false in
private theorem ccm4_relativeCohomologyToAbsolute_naturality
    {A B : TopPair.{0}} (f : A ⟶ B) (n : ℕ) (u : RelativeCohomology ℚ B n) :
    relativeCohomologyToAbsolute ℚ A n (relativeCohomologyMap ℚ n f u) =
      cohomologyMap ℚ n (TopPair.Hom.fst f) (relativeCohomologyToAbsolute ℚ B n u) := by
  have hdual := congrArg HomologicalComplex.linearDualMap
    (TopPair.Homotopy.relativeChainProjection_naturality (R := ℚ) f)
  rw [HomologicalComplex.linearDualMap_comp, HomologicalComplex.linearDualMap_comp] at hdual
  have hhom := congrArg (fun v => HomologicalComplex.homologyMap v n) hdual
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at hhom
  exact ConcreteCategory.congr_hom hhom u

private theorem ccm4_supportedPullback_relativeToAbsolute
    {X Z : Over (Spec ↧ℂ)}
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (f : X ⟶ Z) (S : Closeds (ComplexPoint Z)) (n : ℕ)
    (u : TopCat.Sheaf.supportH (TopCat.of (ComplexPoint Z)) S
      ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint Z))).obj
        (AddCommGrpCat.of ℚ)) n) :
    relativeCohomologyToAbsolute ℚ
        (neighborhoodSupportComplementPair Set.univ
          (ccm4_inverseAnalyticSupport f S : Set (ComplexPoint X))) n
        (supportedSingularClass X (ccm4_inverseAnalyticSupport f S) n
          (ccm4_supportedPullback f S n u)) =
      cohomologyMap ℚ n (TopPair.Hom.fst (ccm4_inverseSupportPairMap f S))
        (relativeCohomologyToAbsolute ℚ
          (neighborhoodSupportComplementPair Set.univ (S : Set (ComplexPoint Z))) n
          (supportedSingularClass Z S n u)) := by
  simp only [ccm4_supportedPullback, AddMonoidHom.comp_apply,
    AddEquiv.coe_toAddMonoidHom, AddEquiv.apply_symm_apply,
    LinearMap.toAddMonoidHom_coe]
  exact ccm4_relativeCohomologyToAbsolute_naturality _ _ _

section Normalization

set_option maxRecDepth 4000
set_option maxHeartbeats 400000
set_option linter.auxLemma false
attribute [local implicit_reducible] TopCat.Sheaf TopCat.instCategorySheaf._aux_1
  TopCat.instCategorySheaf._aux_3 TopCat.instCategorySheaf._aux_5

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem ccm4_constant_unit_chain (X : Over (Spec ↧ℂ)) :
    (constantIntegerSheafComplexIntIsoSingleULift X).inv ≫
      constantsIntToCoefficient X ℚ ≫ (constantFieldSheafComplexIntIsoSingle ℚ X).hom =
    (CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).map
      (uliftIntegerToIntegerConstantSheaf X ≫ integerToFieldConstantSheaf ℚ X 1) := by
  dsimp only [constantIntegerSheafComplexIntIsoSingleULift, Iso.trans_inv,
    Iso.symm_inv, Functor.mapIso_hom, constantFieldSheafComplexIntIsoSingle,
    constantsIntToCoefficient]
  rw [HomologicalComplex.extendSingleIso_hom_naturality]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, ← Functor.map_comp]
  simp only [Functor.mapIso_inv, Iso.symm_inv, Functor.mapIso_hom]
  change (CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).map
      (uliftIntegerToIntegerConstantSheaf X) ≫
      (CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).map
        ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).map
          (AddCommGrpCat.ofHom (Int.castAddHom ℚ))) = _
  rw [← Functor.map_comp]
  apply congrArg ((CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).map)
  apply congrArg (fun g => uliftIntegerToIntegerConstantSheaf X ≫ g)
  unfold integerToFieldConstantSheaf
  apply congrArg ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).map)
  apply AddCommGrpCat.hom_ext
  ext
  simp [zmultiplesAddHom]

open HodgeLean.Foundations

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ccm4_singularToFieldCohomology_unit (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] :
    singularToFieldCohomology ℚ X 0 (Singular.unit (TopCat.of (ComplexPoint X))) =
      fieldCohomologyClass ℚ X 1 := by
  let instD : HasDerivedCategory (AnalyticAdditiveSheaf X) := HasDerivedCategory.standard _
  change hypercohomologyAddEquivConstantCohomology ℚ X 0
    ((fieldHypercohomologySingularCochainAddEquiv ℚ X 0).symm
      (singularToSheafHypercohomology X ℚ 0 (Singular.unit _))) = _
  rw [resolutionClassSingular_singularToSheafHypercohomology_unit]
  have h : Localization.SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) (0 : ℤ) rfl
      (constantsIntToCoefficient X ℚ ≫ constantsToSingularCochainComplexInt X ℚ) =
      fieldHypercohomologySingularCochainAddEquiv ℚ X 0
        (Localization.SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) (0 : ℤ) rfl
          (constantsIntToCoefficient X ℚ)) := by
    exact smallShiftedHomMkZero_comp X _ _
  rw [h, AddEquiv.symm_apply_apply]
  let : HasDerivedCategory (CategoryTheory.Sheaf
    (Opens.grothendieckTopology (TopCat.of (ComplexPoint X))) AddCommGrpCat.{0}) := instD
  apply Abelian.Ext.ext
  dsimp only [hypercohomologyAddEquivConstantCohomology, Equiv.trans, Equiv.symm,
    Localization.SmallShiftedHom.precompEquiv, Localization.SmallShiftedHom.postcompEquiv,
    Abelian.Ext.hom, Abelian.Ext.homEquiv]
  simp only [AddEquiv.coe_mk, Equiv.coe_fn_mk, Function.comp_apply]
  erw [Localization.SmallShiftedHom.equiv_chgUniv]
  erw [Localization.SmallShiftedHom.equiv_comp,
    Localization.SmallShiftedHom.equiv_comp,
    Localization.SmallShiftedHom.equiv_mk₀Inv,
    Localization.SmallShiftedHom.equiv_mk₀,
    Localization.SmallShiftedHom.equiv_mk₀]
  simp only [fieldCohomologyClass, Abelian.Ext.mk₀]
  erw [Localization.SmallShiftedHom.equiv_mk₀]
  simp only [ShiftedHom.mk₀_comp_mk₀,
    Localization.isoOfHom, asIso_inv, ← Functor.map_inv]
  congr 1
  simp only [IsIso.Iso.inv_hom]
  erw [← Functor.map_comp, ← Functor.map_comp]
  apply congrArg DerivedCategory.Q.map
  exact (Category.assoc _ _ _).trans (ccm4_constant_unit_chain X)

private theorem ccm4_rawComparison_unit (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    rationalCohomologyLinearEquivSingular X 0
        (HodgeLean.RealDefs.HQ.linearEquiv X 0 (cupUnit X)) =
      Singular.unit (TopCat.of (ComplexPoint X)) := by
  let (U : TopologicalSpace.Opens (ComplexPoint X)) : ParacompactSpace U := openParacompactSpace X U
  apply (spec_singularToFieldCohomology_bijective ℚ X 0).injective
  rw [singularToFieldCohomology_rationalCohomologyLinearEquivSingular,
    ccm4_singularToFieldCohomology_unit]
  rfl

private theorem ccm4_cupComparison_eq_raw (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (n : ℕ)
    (v : HodgeLean.RealDefs.HQ X n) :
    cupComparison X n v =
      rationalCohomologyLinearEquivSingular X n (HodgeLean.RealDefs.HQ.linearEquiv X n v) := by
  let := pathConnectedSpace_complexPoint X
  obtain ⟨r, _, he⟩ := exists_cupComparison_eq_smul X
  have h := cupComparison_unit X
  rw [he, ccm4_rawComparison_unit] at h
  have h1 : r = 1 := (smul_left_injective ℚ
    (Singular.unit_ne_zero (R := ℚ) (TopCat.of (ComplexPoint X))))
      (h.trans (one_smul ℚ (Singular.unit (TopCat.of (ComplexPoint X)))).symm)
  rw [he, h1, one_smul]

end Normalization

section ForgetSupportComparison
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem ccm4_shiftedLift_forget {C : Type*} [Category* C] [Abelian C]
    (S : CategoryTheory.ShortComplex (CochainComplex C ℤ)) :
    CochainComplex.mappingCocone.shiftedLiftShortComplex S ≫
      (CochainComplex.mappingCone.triangle S.g).mor₃ = -S.f⟦(1 : ℤ)⟧' := by
  dsimp only [CochainComplex.mappingCocone.shiftedLiftShortComplex]
  have hm := (CochainComplex.mappingCone.triangleMap
    (CochainComplex.mappingCone.inr S.f) S.g (𝟙 _)
    (CochainComplex.mappingCone.descShortComplex S) (by simp)).comm₃
  dsimp only [CochainComplex.mappingCone.triangleMap] at hm
  rw [Category.assoc, ← hm]
  change (CochainComplex.mappingCone.rotateHomotopyEquiv S.f).hom ≫
    (CochainComplex.mappingCone.triangle (CochainComplex.mappingCone.inr S.f)).mor₃ ≫
    (shiftFunctor (CochainComplex C ℤ) (1 : ℤ)).map (𝟙 S.X₂) = _
  erw [CategoryTheory.Functor.map_id, Category.comp_id]
  exact CochainComplex.mappingCone.rotateHomotopyEquiv_comm₃ S.f

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem ccm4_shortExactCone_forget {C : Type*} [Category* C] [Abelian C]
    (S : CategoryTheory.ShortComplex (CochainComplex C ℤ)) (hS : S.ShortExact)
    (n n' : ℤ) (h : 1 + n = n') :
    (CochainComplex.mappingCocone.shortExactHomologyIsoCone S hS n n' h).hom ≫
      HomologicalComplex.homologyMap (CochainComplex.mappingCone.triangle S.g).mor₃ n ≫
      (((HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) 0).shiftIso
        1 n n' h).app S.X₂).hom = -HomologicalComplex.homologyMap S.f n' := by
  let H := HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) 0
  dsimp only [CochainComplex.mappingCocone.shortExactHomologyIsoCone, Iso.trans_hom,
    Iso.symm_hom, asIso_hom]
  simp only [Category.assoc]
  change (H.shiftIso 1 n n' h).inv.app S.X₁ ≫
    (H.shift n).map (CochainComplex.mappingCocone.shiftedLiftShortComplex S) ≫
    (H.shift n).map (CochainComplex.mappingCone.triangle S.g).mor₃ ≫
    (H.shiftIso 1 n n' h).hom.app S.X₂ = _
  rw [← Functor.map_comp_assoc, ccm4_shiftedLift_forget, Functor.map_neg]
  simp only [Preadditive.comp_neg, Preadditive.neg_comp]
  congr 1
  change (H.shiftIso 1 n n' h).inv.app S.X₁ ≫
    ((shiftFunctor _ (1 : ℤ)) ⋙ H.shift n).map S.f ≫
    (H.shiftIso 1 n n' h).hom.app S.X₂ = (H.shift n').map S.f
  rw [(H.shiftIso 1 n n' h).hom.naturality, Iso.inv_hom_id_app_assoc]

open TopCat.Sheaf in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem ccm4_supportedInjective_forget
    (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (U V : Opens (ComplexPoint X)) (n : ℤ) :
    (complexSupportedSingularInjectiveHomologyIso X U V n).hom ≫
      HomologicalComplex.homologyMap
        (supportRestrictionSectionsComplexShortComplex
          (TopCat.of (ComplexPoint X)) U V (ambientRationalInjectiveComplex X)).f n =
    HomologicalComplex.homologyMap
        (supportRestrictionSectionsComplexShortComplex
          (TopCat.of (ComplexPoint X)) U V
          (rationalSingularCochainComplex (TopCat.of (ComplexPoint X)))).f n ≫
      HomologicalComplex.homologyMap
        (((supportEvaluation (TopCat.of (ComplexPoint X)) V).mapHomologicalComplex ℤᵘᵖ).map
          (complexSingularToAmbientInjective X)) n := by
  change HomologicalComplex.homologyMap _ n ≫ HomologicalComplex.homologyMap _ n =
    HomologicalComplex.homologyMap _ n ≫ HomologicalComplex.homologyMap _ n
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp]
  congr 1
  change ((supportEvaluation (TopCat.of (ComplexPoint X)) V).mapHomologicalComplex ℤᵘᵖ).map _ ≫
    ((supportEvaluation (TopCat.of (ComplexPoint X)) V).mapHomologicalComplex ℤᵘᵖ).map _ =
    ((supportEvaluation (TopCat.of (ComplexPoint X)) V).mapHomologicalComplex ℤᵘᵖ).map _ ≫
    ((supportEvaluation (TopCat.of (ComplexPoint X)) V).mapHomologicalComplex ℤᵘᵖ).map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  exact ((sheafSectionsSupportedOutsideInclusion (TopCat.of (ComplexPoint X)) U).mapHomologicalComplex
    ℤᵘᵖ).naturality (complexSingularToAmbientInjective X)

open TopologicalSpace TopCat.Sheaf in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem ccm4_supportedSectionCone_forget
    (X : TopCat.{0}) (U V : Opens X)
    (K : CochainComplex (TopCat.Sheaf AddCommGrpCat X) ℤ)
    (hK : ∀ n, (K.X n).IsFlasque) (n : ℤ) :
    (supportedSectionHomologyIsoRestrictionCone X U V K hK n).hom ≫
      HomologicalComplex.homologyMap
        (CochainComplex.mappingCone.triangle
          (sectionComplexRestriction X ℤᵘᵖ K (Opens.infLELeft V U))).mor₃ (n - 1) ≫
      (((HomologicalComplex.homologyFunctor AddCommGrpCat ℤᵘᵖ 0).shiftIso
        1 (n - 1) n (by omega)).app
          (((supportEvaluation X V).mapHomologicalComplex ℤᵘᵖ).obj K)).hom =
    -HomologicalComplex.homologyMap
      (supportRestrictionSectionsComplexShortComplex X U V K).f n := by
  let S := supportRestrictionSectionsComplexShortComplex X U V K
  have hS := supportRestrictionSectionsComplexShortComplex_shortExact_of_flasque X U V K hK
  have hc : (supportRestrictionSectionsConeIso X U V K).hom ≫
      (CochainComplex.mappingCone.triangle
        (sectionComplexRestriction X ℤᵘᵖ K (Opens.infLELeft V U))).mor₃ =
      (CochainComplex.mappingCone.triangle S.g).mor₃ := by
    rw [supportRestrictionSectionsConeIso_hom]
    have hm := (CochainComplex.mappingCone.triangleMap S.g
      (sectionComplexRestriction X ℤᵘᵖ K (Opens.infLELeft V U))
      (𝟙 _) (supportRestrictionSectionsIntersectionIso X U V K).hom
      (by simpa using supportRestrictionSectionsIntersectionIso_restriction X U V K)).comm₃
    dsimp only [CochainComplex.mappingCone.triangleMap] at hm
    erw [(shiftFunctor (CochainComplex AddCommGrpCat ℤ) (1 : ℤ)).map_id S.X₂,
      Category.comp_id] at hm
    exact hm.symm
  change ((CochainComplex.mappingCocone.shortExactHomologyIsoCone S hS
    (n - 1) n (by omega)).hom ≫
    HomologicalComplex.homologyMap (supportRestrictionSectionsConeIso X U V K).hom (n - 1)) ≫
    HomologicalComplex.homologyMap _ (n - 1) ≫ _ = _
  rw [Category.assoc, ← HomologicalComplex.homologyMap_comp_assoc, hc]
  exact ccm4_shortExactCone_forget S hS (n - 1) n (by omega)

open CategoryTheory.Limits Opposite in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ccm4_terminal_evaluation
    (Y : TopCat.{0}) (F : TopCat.Sheaf AddCommGrpCat Y)
    (g : (CategoryTheory.Sheaf.freeAbelianSheaf (Opens.grothendieckTopology Y)).obj ⊤ ⟶ F) :
    TopCat.Sheaf.integerConstantHomAddEquivGlobalSections F
      ((TopCat.Sheaf.constantFunctor Y).map
        (AddCommGrpCat.ofHom (AddEquiv.ulift.symm : ℤ ≃+ ULift ℤ).toAddMonoidHom) ≫
        (CategoryTheory.Sheaf.freeAbelianSheafTerminalIso isTerminalTop).inv ≫ g) =
      CategoryTheory.Sheaf.freeAbelianSheafHomAddEquiv ⊤ F g := by
  let t := CategoryTheory.Sheaf.freeAbelianSheafTerminalIso
    (J := Opens.grothendieckTopology Y) isTerminalTop
  let l := (TopCat.Sheaf.constantFunctor Y).map
    (AddCommGrpCat.ofHom (AddEquiv.ulift.symm : ℤ ≃+ ULift ℤ).toAddMonoidHom)
  let e := ((TopCat.Sheaf.forget AddCommGrpCat Y).mapIso t).app (op ⊤)
  have hgen : e.hom (CategoryTheory.Sheaf.freeAbelianSheafGenerator (J := Opens.grothendieckTopology Y) ⊤) =
      l.hom.app (op ⊤)
        ((toSheafify (Opens.grothendieckTopology Y)
          ((Functor.const (Opens Y)ᵒᵖ).obj (AddCommGrpCat.of ℤ))).app (op ⊤) (1 : ℤ)) := by
    dsimp only [e, l, t, CategoryTheory.Sheaf.freeAbelianSheafTerminalIso,
      CategoryTheory.Sheaf.freeAbelianSheafGenerator]
    have hn (P Q : (Opens Y)ᵒᵖ ⥤ AddCommGrpCat) (η : P ⟶ Q) (x : P.obj (op ⊤)) :
        (sheafifyMap (Opens.grothendieckTopology Y) η).app (op ⊤)
          ((toSheafify (Opens.grothendieckTopology Y) P).app (op ⊤) x) =
        (toSheafify (Opens.grothendieckTopology Y) Q).app (op ⊤) (η.app (op ⊤) x) :=
      (ConcreteCategory.congr_hom (NatTrans.congr_app
        (toSheafify_naturality (Opens.grothendieckTopology Y) η) (op ⊤)) x).symm
    erw [hn, hn]
    congr 1
  change g.hom.app (op ⊤) (e.inv (l.hom.app (op ⊤)
    ((toSheafify (Opens.grothendieckTopology Y)
      ((Functor.const (Opens Y)ᵒᵖ).obj (AddCommGrpCat.of ℤ))).app (op ⊤) (1 : ℤ)))) =
    g.hom.app (op ⊤) (CategoryTheory.Sheaf.freeAbelianSheafGenerator ⊤)
  erw [← hgen, Iso.hom_inv_id_apply]

open TopCat.Sheaf CategoryTheory.Limits Opposite in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ccm4_homComplex_supported_forget
    (Y : TopCat.{0}) (U : Opens Y)
    (K : CochainComplex (TopCat.Sheaf AddCommGrpCat Y) ℤ) :
    CochainComplex.HomComplex.precompMap
      ((CochainComplex.singleFunctor _ 0).map
        ((TopCat.Sheaf.constantFunctor Y).map
          (AddCommGrpCat.ofHom (AddEquiv.ulift.symm : ℤ ≃+ ULift ℤ).toAddMonoidHom) ≫
          (CategoryTheory.Sheaf.freeAbelianSheafTerminalIso isTerminalTop).inv ≫
          cokernel.π ((CategoryTheory.Sheaf.freeAbelianSheaf (Opens.grothendieckTopology Y)).map
            (homOfLE (le_top : U ≤ ⊤))))) K ≫
      (homComplexSingleIntegerIsoGlobalSections Y K).hom =
    (homComplexPairSheafIsoSupportedSections Y U ⊤ U (top_inf_eq U) K).hom ≫
      (supportRestrictionSectionsComplexShortComplex Y U ⊤ K).f := by
  dsimp only [homComplexSingleIntegerIsoGlobalSections,
    homComplexPairSheafIsoSupportedSections, Iso.trans_hom]
  rw [← Category.assoc,
    CochainComplex.HomComplex.precompMap_single_fromSingleZeroIsoPreadditiveCoyoneda,
    Category.assoc, Category.assoc]
  congr 1
  apply HomologicalComplex.hom_ext
  intro i
  change _ ≫ (integerConstantHomIsoGlobalSectionsFunctor Y).hom.app (K.X i) =
    (pairSheafHomIsoSupportedSections Y U ⊤ U (top_inf_eq U) (K.X i)).hom ≫
      ((sheafSectionsSupportedOutsideInclusion Y U).app (K.X i)).hom.app (op ⊤)
  rw [pairSheafHomIsoSupportedSections_hom_inclusion]
  apply AddCommGrpCat.hom_ext
  ext g
  exact ccm4_terminal_evaluation Y (K.X i)
    (cokernel.π ((CategoryTheory.Sheaf.freeAbelianSheaf (Opens.grothendieckTopology Y)).map
      (homOfLE (le_top : U ≤ ⊤))) ≫ g)

section Ccm4Cycles
open CochainComplex CategoryTheory.Limits
section StepC4

variable (P : TopPair.{0})

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Step C4: the canonical relative cone comparison sends the `inl` class of the inclusion of a
relative cocycle back to that cocycle's class. -/
private lemma ccm4_relativeCone_homologyπ (n : ℕ)
    (c : (RelativeCochainComplex ℚ P).cycles n)
    (cM : (mappingCone (relativeCochainRestrictionInt ℚ P)).cycles ((n : ℤ) - 1))
    (hcM : (mappingCone (relativeCochainRestrictionInt ℚ P)).iCycles _ cM =
      (mappingCone.inl (relativeCochainRestrictionInt ℚ P)).v (n : ℤ) ((n : ℤ) - 1)
        (by omega)
        ((relativeDualCochainShortComplexInt ℚ P).f.f (n : ℤ)
          (((RelativeCochainComplex ℚ P).extendXIso ComplexShape.embeddingUpNat rfl).inv
            ((RelativeCochainComplex ℚ P).iCycles n c)))) :
    relativeCochainConeCohomologyEquivCanonical ℚ P n
        ((mappingCone (relativeCochainRestrictionInt ℚ P)).homologyπ _ cM) =
      (RelativeCochainComplex ℚ P).homologyπ n c := by
  let K := RelativeCochainComplex ℚ P
  let cE := (K.extendCyclesIso ComplexShape.embeddingUpNat (rfl :
    ComplexShape.embeddingUpNat.f n = (n : ℤ))).inv c
  have hcE : (K.extend ComplexShape.embeddingUpNat).iCycles _ cE =
      (K.extendXIso ComplexShape.embeddingUpNat rfl).inv (K.iCycles n c) := by
    rw [← ConcreteCategory.comp_apply, HomologicalComplex.extendCyclesIso_inv_iCycles,
      ConcreteCategory.comp_apply]
  have hS := relativeDualCochainShortComplexInt_shortExact ℚ P
  have h1 := mod_shortExactHomologyIsoCone_homologyπ (relativeDualCochainShortComplexInt ℚ P) hS
    ((n : ℤ) - 1) (n : ℤ) (by omega) cE cM (hcM.trans (by rw [← hcE]; rfl))
  dsimp only [relativeCochainConeCohomologyEquivCanonical, relativeDualCochainHomologyIsoCone]
  rw [LinearEquiv.trans_apply]
  change (relativeDualCochainCohomologyEquiv ℚ P n)
    ((mappingCocone.shortExactHomologyIsoCone (relativeDualCochainShortComplexInt ℚ P) hS
      ((n : ℤ) - 1) (n : ℤ) (by omega)).inv
      ((mappingCone (relativeCochainRestrictionInt ℚ P)).homologyπ _ cM)) = _
  erw [← h1, Iso.hom_inv_id_apply]
  change (K.extendHomologyIso ComplexShape.embeddingUpNat rfl).hom
    ((K.extend ComplexShape.embeddingUpNat).homologyπ _ cE) = _
  rw [← ConcreteCategory.comp_apply, HomologicalComplex.homologyπ_extendHomologyIso_hom,
    ConcreteCategory.comp_apply, Iso.inv_hom_id_apply]

end StepC4

section StepC123

variable (X : TopCat.{0})

set_option maxHeartbeats 400000 in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Steps C1–C4: the raw-cochain cone comparison sends the `inl` class of a raw cochain to the
relative class of any relative cocycle that it pulls back. -/
private lemma ccm4_rawCone_homologyπ (n : ℕ) {V W : Opens X}
    (i : W ⟶ V) (r₀ : (openRawSingularCochainComplex ℚ X V).X n)
    (c : (openRawSingularRestrictionCone ℚ X i).cycles ((n : ℤ) - 1))
    (hc : (openRawSingularRestrictionCone ℚ X i).iCycles _ c =
      (mappingCone.inl (HomologicalComplex.extendMap (openRawSingularRestriction ℚ X i)
        ComplexShape.embeddingUpNat)).v (n : ℤ) ((n : ℤ) - 1) (by omega)
        (((openRawSingularCochainComplex ℚ X V).extendXIso ComplexShape.embeddingUpNat rfl).inv r₀))
    (cr : (RelativeCochainComplex ℚ (openInclusionPair X i)).cycles n)
    (hcr : (HomologicalComplex.linearDualMap (relativeChainProjection ℚ (openInclusionPair X i))).f n
      ((RelativeCochainComplex ℚ (openInclusionPair X i)).iCycles n cr) = r₀) :
    openRawSingularRestrictionConeCohomologyEquivRelative ℚ X i n
        ((openRawSingularRestrictionCone ℚ X i).homologyπ _ c) =
      (RelativeCochainComplex ℚ (openInclusionPair X i)).homologyπ n cr := by
  let P := openInclusionPair X i
  let φ := relativeCochainRestrictionInt ℚ P
  let F := forget₂ (ModuleCat ℚ) AddCommGrpCat
  let e1 := openRawSingularRestrictionConeIsoRelative ℚ X i
  let c1 := HomologicalComplex.cyclesMap e1.hom _ c
  let e2 := mappingCone.mapHomologicalComplexIso φ F
  let c2 := HomologicalComplex.cyclesMap e2.inv _ c1
  let S := (mappingCone φ).sc ((n : ℤ) - 1)
  let cM : (mappingCone φ).cycles ((n : ℤ) - 1) := (S.mapCyclesIso F).hom c2
  have s1 := ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality e1.hom
    ((n : ℤ) - 1)) c
  have s2 := ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality e2.inv
    ((n : ℤ) - 1)) c1
  have s3 := ConcreteCategory.congr_hom (homologyπ_mapHomologyIso_hom S F) c2
  have hcM : (mappingCone φ).iCycles _ cM =
      (mappingCone.inl φ).v (n : ℤ) ((n : ℤ) - 1) (by omega)
        ((relativeDualCochainShortComplexInt ℚ P).f.f (n : ℤ)
          (((RelativeCochainComplex ℚ P).extendXIso ComplexShape.embeddingUpNat rfl).inv
            ((RelativeCochainComplex ℚ P).iCycles n cr))) := by
    have h1 := ConcreteCategory.congr_hom (S.mapCyclesIso_hom_iCycles F) c2
    have h2 := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i e2.inv _) c1
    have h3 := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i e1.hom _) c
    rw [ConcreteCategory.comp_apply] at h1 h2 h3
    rw [ConcreteCategory.comp_apply] at h2 h3
    change F.map S.iCycles cM = _
    rw [h1]
    change (((F.mapHomologicalComplex _).obj (mappingCone φ)).iCycles _ c2) = _
    rw [h2, h3, hc]
    refine (congrArg (ConcreteCategory.hom (e2.inv.f _)) (ConcreteCategory.congr_hom
      (inl_v_mapArrowHom _ _ _ _ (n : ℤ) ((n : ℤ) - 1) (by omega)) _)).trans ?_
    refine (ConcreteCategory.congr_hom
      (inl_v_mapHomologicalComplexIso_inv φ F (n : ℤ) ((n : ℤ) - 1) (by omega)) _).trans ?_
    change (mappingCone.inl φ).v (n : ℤ) ((n : ℤ) - 1) (by omega) _ = _
    congr 1
    have hR := ConcreteCategory.congr_hom (HomologicalComplex.extendMap_f
      (HomologicalComplex.linearDualMap (relativeChainProjection ℚ P)) ComplexShape.embeddingUpNat
      (rfl : ComplexShape.embeddingUpNat.f n = (n : ℤ)))
      (((RelativeCochainComplex ℚ P).extendXIso ComplexShape.embeddingUpNat rfl).inv
        ((RelativeCochainComplex ℚ P).iCycles n cr))
    simp only [ConcreteCategory.comp_apply, Iso.inv_hom_id_apply] at hR
    refine Eq.trans ?_ hR.symm
    refine Eq.trans ?_ (congrArg _ hcr).symm
    have hm : (HomologicalComplex.extendMap (openRawSingularCochainComplexIsoDual ℚ X V).hom
          ComplexShape.embeddingUpNat).f n ≫
        (HomologicalComplex.mapExtendCanonicalIso (forget₂ (ModuleCat ℚ) AddCommGrpCat)
          (HomologicalComplex.linearDualCochainComplex (SingularChainComplex ℚ (TopCat.of V)))
          ComplexShape.embeddingUpNat).inv.f n =
        ((openRawSingularCochainComplex ℚ X V).extendXIso ComplexShape.embeddingUpNat rfl).hom ≫
          (openRawSingularCochainComplexIsoDual ℚ X V).hom.f n ≫
          (forget₂ (ModuleCat ℚ) AddCommGrpCat).map
            ((HomologicalComplex.linearDualCochainComplex (SingularChainComplex ℚ (TopCat.of V))).extendXIso
              ComplexShape.embeddingUpNat rfl).inv := by
      rw [HomologicalComplex.extendMap_f _ _ (i := n) (i' := (n : ℤ)) rfl,
        mapExtendCanonicalIso_inv_f _ _ _ (i := n) (j := (n : ℤ)) rfl]
      simp
    refine (ConcreteCategory.congr_hom hm _).trans ?_
    simp
    rfl
  have s4 := ccm4_relativeCone_homologyπ P n cr cM hcM
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at s1 s2 s3
  dsimp only [openRawSingularRestrictionConeCohomologyEquivRelative, AddEquiv.trans_apply]
  change (relativeCochainConeCohomologyEquivCanonical ℚ P n)
    ((S.mapHomologyIso F).hom (HomologicalComplex.homologyMap e2.inv _
      (HomologicalComplex.homologyMap e1.hom _
        ((openRawSingularRestrictionCone ℚ X i).homologyπ _ c)))) = _
  rw [s1, s2]
  erw [s3]
  exact s4

end StepC123



end Ccm4Cycles

section ExtBridge
set_option linter.auxLemma false
attribute [local implicit_reducible] TopCat.Sheaf TopCat.instCategorySheaf._aux_1
  TopCat.instCategorySheaf._aux_3 TopCat.instCategorySheaf._aux_5
open TopCat.Sheaf CategoryTheory.Abelian CategoryTheory.Limits Opposite
variable (Y : TopCat.{0})
  [HasExt.{0} (CategoryTheory.Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat)]
local instance : HasDerivedCategory (TopCat.Sheaf AddCommGrpCat Y) :=
  HasDerivedCategory.standard _
local instance : HasDerivedCategory (CategoryTheory.Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat) :=
  HasDerivedCategory.standard _
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 400000 in
private theorem ccm4_relH_injective_forget (U : Opens Y)
    (F : TopCat.Sheaf AddCommGrpCat Y)
    (I : CochainComplex (TopCat.Sheaf AddCommGrpCat Y) ℤ) [I.IsKInjective]
    (ι : (CochainComplex.singleFunctor _ 0).obj F ⟶ I) [QuasiIso ι]
    (n : ℕ) (x : CategoryTheory.Sheaf.relH F n (homOfLE (le_top : U ≤ ⊤))) :
    let k := (TopCat.Sheaf.constantFunctor Y).map
        (AddCommGrpCat.ofHom (AddEquiv.ulift.symm : ℤ ≃+ ULift ℤ).toAddMonoidHom) ≫
        (CategoryTheory.Sheaf.freeAbelianSheafTerminalIso isTerminalTop).inv ≫
        cokernel.π ((CategoryTheory.Sheaf.freeAbelianSheaf (Opens.grothendieckTopology Y)).map
          (homOfLE (le_top : U ≤ ⊤)))
    CochainComplex.HomComplex.homologyAddEquiv (integerConstantSingleComplex Y) I n
      (HomologicalComplex.homologyMap (homComplexSingleIntegerIsoGlobalSections Y I).inv n
        (HomologicalComplex.homologyMap
          (supportRestrictionSectionsComplexShortComplex Y U ⊤ I).f n
          (relHAddEquivSupportedSectionsHomology Y U ⊤ U (top_inf_eq U) F I ι n x))) =
    CochainComplex.kInjectiveDerivedHomAddEquivCohomologyClass (integerConstantSingleComplex Y) I n
      (DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map k) ≫
        x.hom ≫ (shiftFunctor _ (n : ℤ)).map (DerivedCategory.Q.map ι)) := by
  dsimp only
  let P := pairSheaf' Y U ⊤ U (top_inf_eq U)
  let k := (TopCat.Sheaf.constantFunctor Y).map
      (AddCommGrpCat.ofHom (AddEquiv.ulift.symm : ℤ ≃+ ULift ℤ).toAddMonoidHom) ≫
      (CategoryTheory.Sheaf.freeAbelianSheafTerminalIso isTerminalTop).inv ≫
      cokernel.π ((CategoryTheory.Sheaf.freeAbelianSheaf (Opens.grothendieckTopology Y)).map
        (homOfLE (le_top : U ≤ ⊤)))
  let p := CochainComplex.HomComplex.precompMap ((CochainComplex.singleFunctor _ 0).map k) I
  have hchain : (homComplexPairSheafIsoSupportedSections Y U ⊤ U (top_inf_eq U) I).hom ≫
      (supportRestrictionSectionsComplexShortComplex Y U ⊤ I).f ≫
      (homComplexSingleIntegerIsoGlobalSections Y I).inv = p := by
    rw [← Category.assoc, ← ccm4_homComplex_supported_forget, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  have hh := congrArg (fun f => HomologicalComplex.homologyMap f (n : ℤ)) hchain
  simp only [HomologicalComplex.homologyMap_comp] at hh
  dsimp only [relHAddEquivSupportedSectionsHomology, AddEquiv.trans_apply,
    isoHomCongrAddEquiv_apply, Iso.refl_inv, Category.id_comp, Functor.mapIso_hom, asIso_hom,
    Ext.homAddEquiv_apply]
  rw [Iso.addCommGroupIsoToAddEquiv_apply, HomologicalComplex.homologyMapIso_hom]
  have hhe := fun a => ConcreteCategory.congr_hom hh a
  simp only [ConcreteCategory.comp_apply] at hhe
  erw [hhe]
  erw [CochainComplex.HomComplex.homologyAddEquiv_precompMap, AddEquiv.apply_symm_apply]
  erw [isoHomCongrAddEquiv_apply, Iso.refl_inv, Category.id_comp]
  exact (CochainComplex.kInjectiveDerivedHomAddEquivCohomologyClass_precomp
    ((CochainComplex.singleFunctor _ 0).map k) I n
    (x.hom ≫ (shiftFunctor _ (n : ℤ)).map (DerivedCategory.Q.map ι))).symm
end ExtBridge

section Ccm4CyclesAssembly
open CochainComplex CategoryTheory.Limits
section Assembly

variable (X : TopCat.{0}) [T2Space X] [∀ V : Opens X, ParacompactSpace V] (U V : Opens X)

set_option maxHeartbeats 400000 in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem ccm4_supportedCone_raw_cycle (n : ℕ)
    (c : (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex X U V
      (rationalSingularCochainComplex X)).X₁.cycles (n : ℤ))
    (r₀ : (openRawSingularCochainComplex ℚ X V).X n)
    (hr : (openRawToSingularCochainSheafComplex ℚ X V).f n r₀ =
      ((singularCochainSheafComplex ℚ X).extendXIso ComplexShape.embeddingUpNat
        (rfl : ComplexShape.embeddingUpNat.f n = (n : ℤ))).hom.hom.app (Opposite.op V)
        ((TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex X U V
          (rationalSingularCochainComplex X)).f.f (n : ℤ)
          ((TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex X U V
            (rationalSingularCochainComplex X)).X₁.iCycles _ c)))
    (cR : (openRawSingularRestrictionCone ℚ X (Opens.infLELeft V U)).cycles ((n : ℤ) - 1))
    (hcR : (openRawSingularRestrictionCone ℚ X (Opens.infLELeft V U)).iCycles _ cR =
      (mappingCone.inl (HomologicalComplex.extendMap
        (openRawSingularRestriction ℚ X (Opens.infLELeft V U))
        ComplexShape.embeddingUpNat)).v (n : ℤ) ((n : ℤ) - 1) (by omega)
        (((openRawSingularCochainComplex ℚ X V).extendXIso ComplexShape.embeddingUpNat rfl).inv r₀)) :
    let i := Opens.infLELeft V U
    let mR := openRawToSingularSheafRestrictionCone ℚ X i
    let cB := HomologicalComplex.cyclesMap mR _ cR
    let eB := TopCat.Sheaf.sectionComplexRestrictionExtendConeIso X
      (singularCochainSheafComplex ℚ X) i
    let cA := HomologicalComplex.cyclesMap eB.inv _ cB
    (TopCat.Sheaf.supportedSectionHomologyIsoRestrictionCone X U V
      (rationalSingularCochainComplex X) (fun _ => inferInstance) (n : ℤ)).hom
      ((TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex X U V
        (rationalSingularCochainComplex X)).X₁.homologyπ _ c) =
      (mappingCone (TopCat.Sheaf.sectionComplexRestriction X ℤᵘᵖ
        (rationalSingularCochainComplex X) i)).homologyπ _ cA := by
  let i := Opens.infLELeft V U
  let K' := singularCochainSheafComplex ℚ X
  let rE := ((openRawSingularCochainComplex ℚ X V).extendXIso ComplexShape.embeddingUpNat
    (rfl : ComplexShape.embeddingUpNat.f n = (n : ℤ))).inv r₀
  let mR := openRawToSingularSheafRestrictionCone ℚ X i
  let cB := HomologicalComplex.cyclesMap mR _ cR
  let eB := TopCat.Sheaf.sectionComplexRestrictionExtendConeIso X K' i
  let cA := HomologicalComplex.cyclesMap eB.inv _ cB
  exact supportedSectionHomologyIsoRestrictionCone_homologyπ X U V
    (rationalSingularCochainComplex X) (fun _ => inferInstance) (n : ℤ) c cA (by
      have h1 := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i eB.inv _) cB
      have h2 := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i mR _) cR
      rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h1 h2
      change (HomologicalComplex.cyclesMap eB.inv _ ≫ HomologicalComplex.iCycles _ _) cB = _
      rw [ConcreteCategory.comp_apply, h1]
      change eB.inv.f _ ((HomologicalComplex.cyclesMap mR _ ≫ HomologicalComplex.iCycles _ _) cR) = _
      rw [ConcreteCategory.comp_apply, h2, hcR]
      refine (congrArg (ConcreteCategory.hom (eB.inv.f _)) (ConcreteCategory.congr_hom
        (inl_v_mappingCone_map _ _
          (HomologicalComplex.extendMap (openRawToSingularCochainSheafComplex ℚ X V)
            ComplexShape.embeddingUpNat)
          (HomologicalComplex.extendMap (openRawToSingularCochainSheafComplex ℚ X (V ⊓ U))
            ComplexShape.embeddingUpNat)
          (openSingularSheafRestrictionInt_naturality ℚ X i)
          (n : ℤ) ((n : ℤ) - 1) (by omega)) rE)).trans ?_
      refine (ConcreteCategory.congr_hom
        (inl_v_mapArrowHom (C := AddCommGrpCat.{0})
          (HomologicalComplex.extendMap (TopCat.Sheaf.sectionComplexRestriction X (.up ℕ) K' i)
            ComplexShape.embeddingUpNat)
          (TopCat.Sheaf.sectionComplexRestriction X ℤᵘᵖ
            (K'.extend ComplexShape.embeddingUpNat) i) _ _
          (n : ℤ) ((n : ℤ) - 1) (by omega)) _).trans ?_
      refine congrArg (ConcreteCategory.hom ((mappingCone.inl (TopCat.Sheaf.sectionComplexRestriction
        X ℤᵘᵖ (K'.extend ComplexShape.embeddingUpNat) i)).v (n : ℤ) ((n : ℤ) - 1)
          (by omega))) ?_
      change (HomologicalComplex.mapExtendCanonicalIso (TopCat.Sheaf.supportEvaluation X V) K'
        ComplexShape.embeddingUpNat).inv.f (n : ℤ)
          ((HomologicalComplex.extendMap (openRawToSingularCochainSheafComplex ℚ X V)
            ComplexShape.embeddingUpNat).f (n : ℤ) rE) = _
      rw [mapExtendCanonicalIso_inv_f _ _ _ (i := n) (j := (n : ℤ)) rfl,
        HomologicalComplex.extendMap_f _ _ (i := n) (i' := (n : ℤ)) rfl]
      simp only [rE, ConcreteCategory.comp_apply]
      erw [Iso.inv_hom_id_apply, Iso.inv_hom_id_apply, hr]
      have hK := congrArg (fun f => f.hom.app (Opposite.op V))
        ((singularCochainSheafComplex ℚ X).extendXIso ComplexShape.embeddingUpNat
          (rfl : ComplexShape.embeddingUpNat.f n = (n : ℤ))).hom_inv_id
      exact ConcreteCategory.congr_hom hK _)

set_option maxHeartbeats 400000 in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Upstream's singular-section comparison sends the class of a supported section to the relative
class of a relative cocycle, as soon as the section comes from a raw cochain `r₀` that is a cocycle
vanishing on `V ⊓ U`, and `r₀` is the pullback of the relative cocycle. -/
private theorem ccm4_supportedRelative_homologyπ (n : ℕ)
    (c : (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex X U V
      (rationalSingularCochainComplex X)).X₁.cycles (n : ℤ))
    (r₀ : (openRawSingularCochainComplex ℚ X V).X n)
    (hd : (openRawSingularCochainComplex ℚ X V).d n (n + 1) r₀ = 0)
    (hW : (openRawSingularRestriction ℚ X (Opens.infLELeft V U)).f n r₀ = 0)
    (hr : (openRawToSingularCochainSheafComplex ℚ X V).f n r₀ =
      ((singularCochainSheafComplex ℚ X).extendXIso ComplexShape.embeddingUpNat
        (rfl : ComplexShape.embeddingUpNat.f n = (n : ℤ))).hom.hom.app (Opposite.op V)
        ((TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex X U V
          (rationalSingularCochainComplex X)).f.f (n : ℤ)
          ((TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex X U V
            (rationalSingularCochainComplex X)).X₁.iCycles _ c)))
    (cr : (RelativeCochainComplex ℚ (openInclusionPair X (Opens.infLELeft V U))).cycles n)
    (hcr : (HomologicalComplex.linearDualMap
      (relativeChainProjection ℚ (openInclusionPair X (Opens.infLELeft V U)))).f n
      ((RelativeCochainComplex ℚ (openInclusionPair X (Opens.infLELeft V U))).iCycles n cr) = r₀) :
    supportedRationalSingularSectionCohomologyEquivRelative X U V n
        ((TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex X U V
          (rationalSingularCochainComplex X)).X₁.homologyπ _ c) =
      (RelativeCochainComplex ℚ (openInclusionPair X (Opens.infLELeft V U))).homologyπ n cr := by
  let i := Opens.infLELeft V U
  let K' := singularCochainSheafComplex ℚ X
  let rE := ((openRawSingularCochainComplex ℚ X V).extendXIso ComplexShape.embeddingUpNat
    (rfl : ComplexShape.embeddingUpNat.f n = (n : ℤ))).inv r₀
  obtain ⟨cR, hcR⟩ := ab_exists_cycles (K := openRawSingularRestrictionCone ℚ X i)
    (i := ((n : ℤ) - 1))
    ((mappingCone.inl (HomologicalComplex.extendMap (openRawSingularRestriction ℚ X i)
      ComplexShape.embeddingUpNat)).v (n : ℤ) ((n : ℤ) - 1) (by omega) rE) (by
      have h01 : ((n : ℤ) - 1) + 1 = (n : ℤ) := by omega
      rw [h01]
      refine (ConcreteCategory.congr_hom (mappingCone.inl_v_d (HomologicalComplex.extendMap
        (openRawSingularRestriction ℚ X i) ComplexShape.embeddingUpNat) (n : ℤ)
        ((n : ℤ) - 1) (((n + 1 : ℕ) : ℤ)) (by omega) (by omega)) rE).trans ?_
      have hφ : (HomologicalComplex.extendMap (openRawSingularRestriction ℚ X i)
          ComplexShape.embeddingUpNat).f (n : ℤ) rE = 0 := by
        rw [HomologicalComplex.extendMap_f _ _ (i := n) (i' := (n : ℤ)) rfl]
        simp only [rE, ConcreteCategory.comp_apply]
        erw [Iso.inv_hom_id_apply, hW]
        exact map_zero _
      have hdE : ((openRawSingularCochainComplex ℚ X V).extend ComplexShape.embeddingUpNat).d
          (n : ℤ) ((n + 1 : ℕ) : ℤ) rE = 0 := by
        rw [HomologicalComplex.extend_d_eq _ _ (i := n) (j := n + 1) (i' := (n : ℤ))
          (j' := ((n + 1 : ℕ) : ℤ)) rfl rfl]
        simp only [rE, ConcreteCategory.comp_apply]
        erw [Iso.inv_hom_id_apply, hd]
        exact map_zero _
      simp only [ConcreteCategory.comp_apply,
        AddCommGrpCat.hom_sub, AddMonoidHom.sub_apply, hφ, hdE, map_zero, sub_zero])
  let mR := openRawToSingularSheafRestrictionCone ℚ X i
  let cB := HomologicalComplex.cyclesMap mR _ cR
  let eB := TopCat.Sheaf.sectionComplexRestrictionExtendConeIso X K' i
  let cA := HomologicalComplex.cyclesMap eB.inv _ cB
  have hA := ccm4_supportedCone_raw_cycle X U V n c r₀ hr cR hcR
  dsimp only [supportedRationalSingularSectionCohomologyEquivRelative, AddEquiv.trans_apply]
  change openSingularSheafRestrictionConeCohomologyEquivRelative X i n
    (HomologicalComplex.homologyMap eB.hom _
      ((TopCat.Sheaf.supportedSectionHomologyIsoRestrictionCone X U V
        (rationalSingularCochainComplex X) (fun _ => inferInstance) (n : ℤ)).hom
        ((TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex X U V
          (rationalSingularCochainComplex X)).X₁.homologyπ _ c))) = _
  rw [hA]
  have hB : HomologicalComplex.homologyMap eB.hom _
      ((mappingCone (TopCat.Sheaf.sectionComplexRestriction X ℤᵘᵖ
        (rationalSingularCochainComplex X) i)).homologyπ _ cA) = (openSingularSheafRestrictionCone ℚ X i).homologyπ _ cB := by
    apply ab_homologyMap_homologyπ
    have h1 := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i eB.inv _) cB
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h1
    rw [h1, ← ConcreteCategory.comp_apply, ← HomologicalComplex.comp_f, eB.inv_hom_id]
    rfl
  erw [hB]
  have hC := ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality mR
    ((n : ℤ) - 1)) cR
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hC
  dsimp only [openSingularSheafRestrictionConeCohomologyEquivRelative, AddEquiv.trans_apply]
  rw [Iso.addCommGroupIsoToAddEquiv_apply, Iso.symm_hom]
  erw [← hC]
  rw [asIso_inv]
  erw [IsIso.hom_inv_id_apply]
  exact ccm4_rawCone_homologyπ X n i r₀ cR hcR cr hcr

end Assembly
end Ccm4CyclesAssembly

set_option maxHeartbeats 400000 in
private theorem ccm4_kInjective_localization
    {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
    (A I : CochainComplex C ℤ) [I.IsKInjective]
    [Localization.HasSmallLocalizedShiftedHom
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) ℤ A I] (n : ℤ)
    (x : ShiftedHom (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj I) n) :
    Localization.SmallShiftedHom.equiv (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
      DerivedCategory.Q
      ((CochainComplex.kInjectiveDerivedHomAddEquivCohomologyClass A I n x).toSmallShiftedHom) = x := by
  obtain ⟨c, rfl⟩ := (CochainComplex.kInjectiveDerivedHomAddEquivCohomologyClass A I n).symm.surjective x
  rw [AddEquiv.apply_symm_apply]
  obtain ⟨z, rfl⟩ := c.mk_surjective
  rw [CochainComplex.HomComplex.CohomologyClass.equiv_toSmallShiftedHom_mk,
    CochainComplex.kInjectiveDerivedHomAddEquivCohomologyClass_symm_mk]

open TopCat.Sheaf in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem ccm4_supported_cycles_lift
    (Y : TopCat.{0}) (U V : Opens Y)
    (K : CochainComplex (TopCat.Sheaf AddCommGrpCat Y) ℤ) (n : ℤ)
    (s : (((supportEvaluation Y V).mapHomologicalComplex ℤᵘᵖ).obj K).X n)
    (hd : (((supportEvaluation Y V).mapHomologicalComplex ℤᵘᵖ).obj K).d n (n + 1) s = 0)
    (hs : (sectionComplexRestriction Y ℤᵘᵖ K (Opens.infLELeft V U)).f n s = 0) :
    ∃ c : (supportRestrictionSectionsComplexShortComplex Y U V K).X₁.cycles n,
      (supportRestrictionSectionsComplexShortComplex Y U V K).f.f n
        ((supportRestrictionSectionsComplexShortComplex Y U V K).X₁.iCycles n c) = s := by
  let S := supportRestrictionSectionsComplexShortComplex Y U V K
  obtain ⟨t, ht⟩ := exists_supportedOutsideSection_of_restrict_eq_zero Y U V (K.X n) s hs
  change ∃ c : S.X₁.cycles n, S.f.f n (S.X₁.iCycles n c) = s
  have : Mono (S.f.f (n + 1)) := inferInstanceAs
    (Mono (((sheafSectionsSupportedOutsideInclusion Y U).app (K.X (n + 1))).hom.app (Opposite.op V)))
  have hdt : S.X₁.d n (n + 1) t = 0 := by
    apply (ConcreteCategory.injective_of_mono_of_preservesPullback (S.f.f (n + 1)))
    rw [map_zero, ← ConcreteCategory.comp_apply, ← S.f.comm, ConcreteCategory.comp_apply]
    exact (congrArg (fun a => S.X₂.d n (n + 1) a) ht).trans hd
  obtain ⟨c, hc⟩ := ab_exists_cycles (K := S.X₁) t hdt
  exact ⟨c, (congrArg (fun a => S.f.f n a) hc).trans ht⟩

section RawToSections
open TopCat.Sheaf
private def ccm4_rawToSections (X : TopCat.{0}) (V : Opens X) :
    (openRawSingularCochainComplex ℚ X V).extend ComplexShape.embeddingUpNat ⟶
      ((supportEvaluation X V).mapHomologicalComplex ℤᵘᵖ).obj
        (rationalSingularCochainComplex X) :=
  HomologicalComplex.extendMap (openRawToSingularCochainSheafComplex ℚ X V)
    ComplexShape.embeddingUpNat ≫
    (HomologicalComplex.mapExtendCanonicalIso (supportEvaluation X V)
      (singularCochainSheafComplex ℚ X) ComplexShape.embeddingUpNat).inv

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem ccm4_rawToSections_restriction (X : TopCat.{0})
    {V W : Opens X} (i : W ⟶ V) :
    ccm4_rawToSections X V ≫ sectionComplexRestriction X ℤᵘᵖ
      (rationalSingularCochainComplex X) i =
    HomologicalComplex.extendMap (openRawSingularRestriction ℚ X i)
      ComplexShape.embeddingUpNat ≫ ccm4_rawToSections X W := by
  have hr : (HomologicalComplex.mapExtendCanonicalIso (supportEvaluation X V)
        (singularCochainSheafComplex ℚ X) ComplexShape.embeddingUpNat).inv ≫
      sectionComplexRestriction X ℤᵘᵖ (rationalSingularCochainComplex X) i =
    HomologicalComplex.extendMap (openSingularSheafRestriction ℚ X i) ComplexShape.embeddingUpNat ≫
      (HomologicalComplex.mapExtendCanonicalIso (supportEvaluation X W)
        (singularCochainSheafComplex ℚ X) ComplexShape.embeddingUpNat).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
    exact sectionComplexRestriction_extend X (singularCochainSheafComplex ℚ X) i
  dsimp only [ccm4_rawToSections]
  rw [Category.assoc, hr, ← Category.assoc, ← openSingularSheafRestrictionInt_naturality,
    Category.assoc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem ccm4_rawToSections_f (X : TopCat.{0}) (V : Opens X) (n : ℕ)
    (r : (openRawSingularCochainComplex ℚ X V).X n) :
    (ccm4_rawToSections X V).f (n : ℤ)
      (((openRawSingularCochainComplex ℚ X V).extendXIso
        ComplexShape.embeddingUpNat rfl).inv r) =
    (((singularCochainSheafComplex ℚ X).extendXIso ComplexShape.embeddingUpNat
      (rfl : ComplexShape.embeddingUpNat.f n = (n : ℤ))).inv.hom.app (Opposite.op V))
      ((openRawToSingularCochainSheafComplex ℚ X V).f n r) := by
  dsimp only [ccm4_rawToSections]
  rw [HomologicalComplex.comp_f, ConcreteCategory.comp_apply,
    HomologicalComplex.extendMap_f _ _ (i := n) (i' := (n : ℤ)) rfl,
    mapExtendCanonicalIso_inv_f _ _ _ (i := n) (j := (n : ℤ)) rfl]
  simp only [ConcreteCategory.comp_apply]
  erw [Iso.inv_hom_id_apply, Iso.inv_hom_id_apply]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem ccm4_supported_cycle_of_raw (X : TopCat.{0}) (U V : Opens X) (n : ℕ)
    (r : (openRawSingularCochainComplex ℚ X V).cycles n)
    (hW : (openRawSingularRestriction ℚ X (Opens.infLELeft V U)).f n
      ((openRawSingularCochainComplex ℚ X V).iCycles n r) = 0) :
    ∃ c : (supportRestrictionSectionsComplexShortComplex X U V
        (rationalSingularCochainComplex X)).X₁.cycles (n : ℤ),
      (supportRestrictionSectionsComplexShortComplex X U V
        (rationalSingularCochainComplex X)).f.f (n : ℤ)
        ((supportRestrictionSectionsComplexShortComplex X U V
          (rationalSingularCochainComplex X)).X₁.iCycles (n : ℤ) c) =
      (ccm4_rawToSections X V).f (n : ℤ)
        (((openRawSingularCochainComplex ℚ X V).extendXIso
          ComplexShape.embeddingUpNat rfl).inv
          ((openRawSingularCochainComplex ℚ X V).iCycles n r)) := by
  let R := openRawSingularCochainComplex ℚ X V
  let A := ((supportEvaluation X V).mapHomologicalComplex ℤᵘᵖ).obj
    (rationalSingularCochainComplex X)
  let rE := (R.extendCyclesIso ComplexShape.embeddingUpNat
    (rfl : ComplexShape.embeddingUpNat.f n = (n : ℤ))).inv r
  have hrE : (R.extend ComplexShape.embeddingUpNat).iCycles (n : ℤ) rE =
      (R.extendXIso ComplexShape.embeddingUpNat rfl).inv (R.iCycles n r) := by
    exact ConcreteCategory.congr_hom (HomologicalComplex.extendCyclesIso_inv_iCycles R
      ComplexShape.embeddingUpNat (rfl : ComplexShape.embeddingUpNat.f n = (n : ℤ))) r
  let a := HomologicalComplex.cyclesMap (ccm4_rawToSections X V) (n : ℤ) rE
  have ha : A.iCycles (n : ℤ) a =
      (ccm4_rawToSections X V).f (n : ℤ)
        ((R.extend ComplexShape.embeddingUpNat).iCycles (n : ℤ) rE) := by
    rw [← ConcreteCategory.comp_apply, HomologicalComplex.cyclesMap_i,
      ConcreteCategory.comp_apply]
  have hd : A.d (n : ℤ) ((n : ℤ) + 1) (A.iCycles (n : ℤ) a) = 0 := by
    rw [← ConcreteCategory.comp_apply, HomologicalComplex.iCycles_d]
    rfl
  have hz : (HomologicalComplex.extendMap
      (openRawSingularRestriction ℚ X (Opens.infLELeft V U)) ComplexShape.embeddingUpNat).f
      (n : ℤ) ((R.extend ComplexShape.embeddingUpNat).iCycles (n : ℤ) rE) = 0 := by
    rw [hrE, HomologicalComplex.extendMap_f _ _ (i := n) (i' := (n : ℤ)) rfl]
    simp only [ConcreteCategory.comp_apply]
    erw [Iso.inv_hom_id_apply, hW]
    exact map_zero _
  have hs : (sectionComplexRestriction X ℤᵘᵖ (rationalSingularCochainComplex X)
      (Opens.infLELeft V U)).f (n : ℤ) (A.iCycles (n : ℤ) a) = 0 := by
    rw [ha, ← ConcreteCategory.comp_apply, ← HomologicalComplex.comp_f,
      ccm4_rawToSections_restriction, HomologicalComplex.comp_f, ConcreteCategory.comp_apply,
      hz, map_zero]
  obtain ⟨c, hc⟩ := ccm4_supported_cycles_lift X U V (rationalSingularCochainComplex X)
    (n : ℤ) (A.iCycles (n : ℤ) a) hd hs
  exact ⟨c, hc.trans (ha.trans (congrArg (fun z => (ccm4_rawToSections X V).f (n : ℤ) z) hrE))⟩

private theorem ccm4_nat_cycles (K : CochainComplex AddCommGrpCat.{0} ℕ)
    (n : ℕ) (x : K.X n) (hx : K.d n (n + 1) x = 0) :
    ∃ c : K.cycles n, K.iCycles n c = x := by
  refine ⟨K.liftCycles (AddCommGrpCat.ofHom (zmultiplesHom _ x)) (n + 1) (by simp) (by
    ext
    simp [hx]) (1 : ℤ), ?_⟩
  rw [← ConcreteCategory.comp_apply, HomologicalComplex.liftCycles_i]
  simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem ccm4_relative_raw_cycle (X : TopCat.{0}) {V W : Opens X}
    (i : W ⟶ V) (n : ℕ)
    (cr : (RelativeCochainComplex ℚ (openInclusionPair X i)).cycles n) :
    ∃ r : (openRawSingularCochainComplex ℚ X V).cycles n,
      (HomologicalComplex.linearDualMap
        (relativeChainProjection ℚ (openInclusionPair X i))).f n
        ((RelativeCochainComplex ℚ (openInclusionPair X i)).iCycles n cr) =
        (openRawSingularCochainComplex ℚ X V).iCycles n r ∧
      (openRawSingularRestriction ℚ X i).f n
        ((openRawSingularCochainComplex ℚ X V).iCycles n r) = 0 := by
  let P := openInclusionPair X i
  let K := RelativeCochainComplex ℚ P
  let j := HomologicalComplex.linearDualMap (relativeChainProjection ℚ P)
  let r₀ := j.f n (K.iCycles n cr)
  have hd : (SingularChainComplex ℚ (TopCat.of V)).linearDualCochainComplex.d n (n + 1) r₀ = 0 := by
    change ((SingularChainComplex ℚ (TopCat.of V)).linearDualCochainComplex.d n (n + 1))
      (j.f n (K.iCycles n cr)) = 0
    have h := ConcreteCategory.congr_hom (j.comm n (n + 1)) (K.iCycles n cr)
    have hz := ConcreteCategory.congr_hom (K.iCycles_d n (n + 1)) cr
    simp only [ConcreteCategory.comp_apply] at h hz
    exact h.trans ((congrArg (fun z => j.f (n + 1) z) hz).trans (map_zero _))
  have hdr : (openRawSingularCochainComplex ℚ X V).d n (n + 1) r₀ = 0 := by
    let e := openRawSingularCochainComplexIsoDual ℚ X V
    change (openRawSingularCochainComplex ℚ X V).d n (n + 1) (e.inv.f n r₀) = 0
    rw [← ConcreteCategory.comp_apply, e.inv.comm, ConcreteCategory.comp_apply]
    exact (congrArg (fun z => e.inv.f (n + 1) z) hd).trans (map_zero _)
  obtain ⟨r, hr⟩ := ccm4_nat_cycles (openRawSingularCochainComplex ℚ X V) n r₀ hdr
  refine ⟨r, hr.symm, ?_⟩
  rw [hr]
  change (HomologicalComplex.linearDualMap ((chainPairFunctor ℚ).obj P).hom).f n
    (j.f n (K.iCycles n cr)) = 0
  have hz := congrArg (fun m => m.f n) (relativeDualCochainShortComplexNat ℚ P).zero
  exact ConcreteCategory.congr_hom hz (K.iCycles n cr)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem ccm4_relative_absolute_raw (X : TopCat.{0}) {V W : Opens X}
    (i : W ⟶ V) (n : ℕ)
    (cr : (RelativeCochainComplex ℚ (openInclusionPair X i)).cycles n)
    (r : (openRawSingularCochainComplex ℚ X V).cycles n)
    (hr : (HomologicalComplex.linearDualMap
      (relativeChainProjection ℚ (openInclusionPair X i))).f n
      ((RelativeCochainComplex ℚ (openInclusionPair X i)).iCycles n cr) =
      (openRawSingularCochainComplex ℚ X V).iCycles n r) :
    relativeCohomologyToAbsolute ℚ (openInclusionPair X i) n
      ((RelativeCochainComplex ℚ (openInclusionPair X i)).homologyπ n cr) =
    (ShortComplex.mapHomologyIso
      ((SingularChainComplex ℚ (TopCat.of V)).linearDualCochainComplex.sc n)
      (forget₂ (ModuleCat ℚ) AddCommGrpCat)).hom
      (HomologicalComplex.homologyMap (openRawSingularCochainComplexIsoDual ℚ X V).hom n
        ((openRawSingularCochainComplex ℚ X V).homologyπ n r)) := by
  let P := openInclusionPair X i
  let K := RelativeCochainComplex ℚ P
  let A := (SingularChainComplex ℚ (TopCat.of V)).linearDualCochainComplex
  let F := forget₂ (ModuleCat ℚ) AddCommGrpCat
  let j := HomologicalComplex.linearDualMap (relativeChainProjection ℚ P)
  let e := openRawSingularCochainComplexIsoDual ℚ X V
  let rF := HomologicalComplex.cyclesMap e.hom n r
  have hL := ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality j n) cr
  have hR := ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality e.hom n) r
  have hF := ConcreteCategory.congr_hom (homologyπ_mapHomologyIso_hom (A.sc n) F) rF
  simp only [ConcreteCategory.comp_apply] at hL hR hF
  change HomologicalComplex.homologyMap j n (K.homologyπ n cr) =
    ((A.sc n).mapHomologyIso F).hom
      (HomologicalComplex.homologyMap e.hom n
        ((openRawSingularCochainComplex ℚ X V).homologyπ n r))
  rw [hL, hR]
  erw [hF]
  apply congrArg (fun c => A.homologyπ n c)
  apply (ConcreteCategory.injective_of_mono_of_preservesPullback (A.iCycles n))
  have h₁ := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i j n) cr
  have h₂ := ConcreteCategory.congr_hom ((A.sc n).mapCyclesIso_hom_iCycles F) rF
  have h₃ := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i e.hom n) r
  simp only [ConcreteCategory.comp_apply] at h₁ h₂ h₃
  change A.iCycles n (HomologicalComplex.cyclesMap j n cr) =
    (F.map (A.sc n).iCycles) (((A.sc n).mapCyclesIso F).hom rF)
  exact h₁.trans (hr.trans (h₂.trans h₃).symm)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem ccm4_ordinary_raw_univ (X : TopCat.{0}) (n : ℕ)
    (v : Cohomology ℚ (TopCat.of (⊤ : Opens X)) n) :
    ordinarySingularCohomologyEquivGlobalRaw ℚ X n
      (cohomologyMap ℚ n
        (TopCat.ofHom ⟨(Homeomorph.Set.univ X).symm, (Homeomorph.Set.univ X).symm.continuous⟩) v) =
    (HomologicalComplex.homologyMapIso (globalRawSingularCochainComplexIso ℚ X) n).inv
      ((topOpenForgottenSingularCochainHomologyIso ℚ X n).inv v) := by
  let i := (Opens.inclusionTopIso X).hom
  let j : X ⟶ TopCat.of (⊤ : Opens X) :=
    TopCat.ofHom ⟨(Homeomorph.Set.univ X).symm, (Homeomorph.Set.univ X).symm.continuous⟩
  have h : i ≫ j = 𝟙 _ := by ext x; rfl
  have hh : cohomologyMap ℚ n i (cohomologyMap ℚ n j v) = v := by
    rw [← LinearMap.comp_apply, ← cohomologyMap_comp, h, cohomologyMap_id]
    rfl
  dsimp only [ordinarySingularCohomologyEquivGlobalRaw, AddEquiv.trans_apply]
  change (HomologicalComplex.homologyMapIso (globalRawSingularCochainComplexIso ℚ X) n).inv
    ((topOpenForgottenSingularCochainHomologyIso ℚ X n).inv
      (cohomologyMap ℚ n i (cohomologyMap ℚ n j v))) = _
  rw [hh]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem ccm4_supported_class_raw_lift (X : TopCat.{0}) [T2Space X]
    [∀ V : Opens X, ParacompactSpace V] (U V : Opens X) (n : ℕ)
    (a : (supportRestrictionSectionsComplexShortComplex X U V
      (rationalSingularCochainComplex X)).X₁.homology (n : ℤ)) :
    ∃ (c : (supportRestrictionSectionsComplexShortComplex X U V
      (rationalSingularCochainComplex X)).X₁.cycles (n : ℤ))
      (cr : (RelativeCochainComplex ℚ (openInclusionPair X (Opens.infLELeft V U))).cycles n)
      (r : (openRawSingularCochainComplex ℚ X V).cycles n),
      (supportRestrictionSectionsComplexShortComplex X U V
        (rationalSingularCochainComplex X)).X₁.homologyπ (n : ℤ) c = a ∧
      (RelativeCochainComplex ℚ (openInclusionPair X (Opens.infLELeft V U))).homologyπ n cr =
        supportedRationalSingularSectionCohomologyEquivRelative X U V n a ∧
      (HomologicalComplex.linearDualMap
        (relativeChainProjection ℚ (openInclusionPair X (Opens.infLELeft V U)))).f n
        ((RelativeCochainComplex ℚ (openInclusionPair X (Opens.infLELeft V U))).iCycles n cr) =
        (openRawSingularCochainComplex ℚ X V).iCycles n r ∧
      (supportRestrictionSectionsComplexShortComplex X U V
        (rationalSingularCochainComplex X)).f.f (n : ℤ)
        ((supportRestrictionSectionsComplexShortComplex X U V
          (rationalSingularCochainComplex X)).X₁.iCycles (n : ℤ) c) =
        (ccm4_rawToSections X V).f (n : ℤ)
          (((openRawSingularCochainComplex ℚ X V).extendXIso
            ComplexShape.embeddingUpNat rfl).inv
            ((openRawSingularCochainComplex ℚ X V).iCycles n r)) := by
  let E := supportedRationalSingularSectionCohomologyEquivRelative X U V n
  let K := RelativeCochainComplex ℚ (openInclusionPair X (Opens.infLELeft V U))
  obtain ⟨cr, hcr⟩ := (ModuleCat.epi_iff_surjective (K.homologyπ n)).mp inferInstance (E a)
  obtain ⟨r, hr, hW⟩ := ccm4_relative_raw_cycle X (Opens.infLELeft V U) n cr
  obtain ⟨c, hc⟩ := ccm4_supported_cycle_of_raw X U V n r hW
  refine ⟨c, cr, r, ?_, hcr, hr, hc⟩
  apply E.injective
  refine (ccm4_supportedRelative_homologyπ X U V n c _ ?_ hW ?_ cr hr).trans hcr
  · exact ConcreteCategory.congr_hom
      ((openRawSingularCochainComplex ℚ X V).iCycles_d n (n + 1)) r
  · rw [hc, ccm4_rawToSections_f]
    have h := congrArg (fun f => f.hom.app (Opposite.op V))
      ((singularCochainSheafComplex ℚ X).extendXIso ComplexShape.embeddingUpNat
        (rfl : ComplexShape.embeddingUpNat.f n = (n : ℤ))).inv_hom_id
    exact (ConcreteCategory.congr_hom h _).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem ccm4_relative_raw_global (X : TopCat.{0}) (U : Opens X) (n : ℕ)
    (cr : (RelativeCochainComplex ℚ (openInclusionPair X (Opens.infLELeft ⊤ U))).cycles n)
    (r : (openRawSingularCochainComplex ℚ X ⊤).cycles n)
    (hr : (HomologicalComplex.linearDualMap
      (relativeChainProjection ℚ (openInclusionPair X (Opens.infLELeft ⊤ U)))).f n
      ((RelativeCochainComplex ℚ (openInclusionPair X (Opens.infLELeft ⊤ U))).iCycles n cr) =
      (openRawSingularCochainComplex ℚ X ⊤).iCycles n r) :
    ordinarySingularCohomologyEquivGlobalRaw ℚ X n
      (cohomologyMap ℚ n
        (TopCat.ofHom ⟨(Homeomorph.Set.univ X).symm, (Homeomorph.Set.univ X).symm.continuous⟩)
        (relativeCohomologyToAbsolute ℚ (openInclusionPair X (Opens.infLELeft ⊤ U)) n
          ((RelativeCochainComplex ℚ (openInclusionPair X (Opens.infLELeft ⊤ U))).homologyπ n cr))) =
      (openRawSingularCochainComplex ℚ X ⊤).homologyπ n r := by
  rw [ccm4_ordinary_raw_univ, ccm4_relative_absolute_raw X _ n cr r hr]
  change (HomologicalComplex.homologyMapIso (globalRawSingularCochainComplexIso ℚ X) n).inv
    ((topOpenForgottenSingularCochainHomologyIso ℚ X n).inv
      ((topOpenForgottenSingularCochainHomologyIso ℚ X n).hom
        ((HomologicalComplex.homologyMapIso (globalRawSingularCochainComplexIso ℚ X) n).hom
          ((openRawSingularCochainComplex ℚ X ⊤).homologyπ n r)))) = _
  rw [Iso.hom_inv_id_apply, Iso.hom_inv_id_apply]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem ccm4_supported_raw_homology (X : TopCat.{0}) [T2Space X]
    [∀ V : Opens X, ParacompactSpace V] (U : Opens X) (n : ℕ)
    (a : (supportRestrictionSectionsComplexShortComplex X U ⊤
      (rationalSingularCochainComplex X)).X₁.homology (n : ℤ)) :
    HomologicalComplex.homologyMap
      (supportRestrictionSectionsComplexShortComplex X U ⊤
        (rationalSingularCochainComplex X)).f (n : ℤ) a =
      HomologicalComplex.homologyMap (ccm4_rawToSections X ⊤) (n : ℤ)
        (((openRawSingularCochainComplex ℚ X ⊤).extendHomologyIso
          ComplexShape.embeddingUpNat (j := n) rfl).inv
          (ordinarySingularCohomologyEquivGlobalRaw ℚ X n
            (cohomologyMap ℚ n
              (TopCat.ofHom ⟨(Homeomorph.Set.univ X).symm, (Homeomorph.Set.univ X).symm.continuous⟩)
              (relativeCohomologyToAbsolute ℚ (openInclusionPair X (Opens.infLELeft ⊤ U)) n
                (supportedRationalSingularSectionCohomologyEquivRelative X U ⊤ n a))))) := by
  obtain ⟨c, cr, r, hc, hcr, hr, hs⟩ := ccm4_supported_class_raw_lift X U ⊤ n a
  rw [← hcr, ccm4_relative_raw_global X U n cr r hr, ← hc]
  let R := openRawSingularCochainComplex ℚ X ⊤
  let rE := (R.extendCyclesIso ComplexShape.embeddingUpNat
    (rfl : ComplexShape.embeddingUpNat.f n = (n : ℤ))).inv r
  have hE := ConcreteCategory.congr_hom (R.homologyπ_extendHomologyIso_inv
    ComplexShape.embeddingUpNat (rfl : ComplexShape.embeddingUpNat.f n = (n : ℤ))) r
  simp only [ConcreteCategory.comp_apply] at hE
  rw [hE]
  have hL := ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality
    (supportRestrictionSectionsComplexShortComplex X U ⊤ (rationalSingularCochainComplex X)).f
    (n : ℤ)) c
  have hR := ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality
    (ccm4_rawToSections X ⊤) (n : ℤ)) rE
  simp only [ConcreteCategory.comp_apply] at hL hR
  refine hL.trans (Eq.trans ?_ hR.symm)
  congr 1
  apply ConcreteCategory.injective_of_mono_of_preservesPullback
    ((((supportEvaluation X ⊤).mapHomologicalComplex ℤᵘᵖ).obj
      (rationalSingularCochainComplex X)).iCycles (n : ℤ))
  have h₁ := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i
    (supportRestrictionSectionsComplexShortComplex X U ⊤ (rationalSingularCochainComplex X)).f
    (n : ℤ)) c
  have h₂ := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i
    (ccm4_rawToSections X ⊤) (n : ℤ)) rE
  have h₃ := ConcreteCategory.congr_hom (R.extendCyclesIso_inv_iCycles
    ComplexShape.embeddingUpNat (rfl : ComplexShape.embeddingUpNat.f n = (n : ℤ))) r
  simp only [ConcreteCategory.comp_apply] at h₁ h₂ h₃
  exact h₁.trans (hs.trans (h₂.trans (congrArg (fun x =>
    (ccm4_rawToSections X ⊤).f (n : ℤ) x) h₃)).symm)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ccm4_supportedPullback_univToAbsolute
    {X Z : Over (Spec ↧ℂ)}
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (f : X ⟶ Z) (S : Closeds (ComplexPoint Z)) (n : ℕ)
    (u : TopCat.Sheaf.supportH (TopCat.of (ComplexPoint Z)) S
      ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint Z))).obj
        (AddCommGrpCat.of ℚ)) n) :
    cohomologyMap ℚ n (TopCat.ofHom ⟨(Homeomorph.Set.univ (ComplexPoint X)).symm, (Homeomorph.Set.univ (ComplexPoint X)).symm.continuous⟩)
      (relativeCohomologyToAbsolute ℚ
        (neighborhoodSupportComplementPair Set.univ
          (ccm4_inverseAnalyticSupport f S : Set (ComplexPoint X))) n
        (supportedSingularClass X (ccm4_inverseAnalyticSupport f S) n
          (ccm4_supportedPullback f S n u))) =
    cohomologyMap ℚ n (TopCat.ofHom (Point.continuousMap f))
      (cohomologyMap ℚ n
        (TopCat.ofHom ⟨(Homeomorph.Set.univ (ComplexPoint Z)).symm, (Homeomorph.Set.univ (ComplexPoint Z)).symm.continuous⟩)
        (relativeCohomologyToAbsolute ℚ
          (neighborhoodSupportComplementPair Set.univ (S : Set (ComplexPoint Z))) n
          (supportedSingularClass Z S n u))) := by
  rw [ccm4_supportedPullback_relativeToAbsolute]
  generalize relativeCohomologyToAbsolute ℚ
    (neighborhoodSupportComplementPair Set.univ (S : Set (ComplexPoint Z))) n
    (supportedSingularClass Z S n u) = v
  let a : TopCat.of (ComplexPoint X) ⟶ TopCat.of (Set.univ : Set (ComplexPoint X)) :=
    TopCat.ofHom ⟨(Homeomorph.Set.univ (ComplexPoint X)).symm,
      (Homeomorph.Set.univ (ComplexPoint X)).symm.continuous⟩
  let b : TopCat.of (ComplexPoint Z) ⟶ TopCat.of (Set.univ : Set (ComplexPoint Z)) :=
    TopCat.ofHom ⟨(Homeomorph.Set.univ (ComplexPoint Z)).symm,
      (Homeomorph.Set.univ (ComplexPoint Z)).symm.continuous⟩
  let g := TopCat.ofHom (Point.continuousMap f)
  let p := TopPair.Hom.fst (ccm4_inverseSupportPairMap f S)
  have h : a ≫ p = g ≫ b := by ext x; rfl
  exact (LinearMap.congr_fun (cohomologyMap_comp ℚ n a p) v).symm.trans
    ((congrArg (fun k => cohomologyMap ℚ n k v) h).trans
      (LinearMap.congr_fun (cohomologyMap_comp ℚ n g b) v))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ccm4_supportComplement_toAbsolute (X : TopCat.{0}) [T2Space X]
    [∀ V : Opens X, ParacompactSpace V] (S : Set X) (hS : IsClosed S)
    (V : Opens X) (n : ℕ)
    (a : (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex X
      ⟨Sᶜ, hS.isOpen_compl⟩ V (rationalSingularCochainComplex X)).X₁.homology (n : ℤ)) :
    relativeCohomologyToAbsolute ℚ (neighborhoodSupportComplementPair (V : Set X) S) n
      (supportedRationalSingularSectionCohomologyEquivSupportComplement X S hS V n a) =
    relativeCohomologyToAbsolute ℚ
      (openInclusionPair X (Opens.infLELeft V ⟨Sᶜ, hS.isOpen_compl⟩)) n
      (supportedRationalSingularSectionCohomologyEquivRelative X
        ⟨Sᶜ, hS.isOpen_compl⟩ V n a) := by
  dsimp only [supportedRationalSingularSectionCohomologyEquivSupportComplement, AddEquiv.trans_apply]
  change relativeCohomologyToAbsolute ℚ _ n
    (relativeCohomologyMap ℚ n (openIntersectionPairIsoSupportComplement X S hS V).inv
      (supportedRationalSingularSectionCohomologyEquivRelative X _ V n a)) = _
  rw [ccm4_relativeCohomologyToAbsolute_naturality]
  change cohomologyMap ℚ n (𝟙 _) _ = _
  rw [cohomologyMap_id]
  rfl
end RawToSections

section GlobalComparison
open HodgeLean.Foundations TopCat.Sheaf CategoryTheory.Limits
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem ccm4_rawToSections_global (X : Over (Spec ↧ℂ)) :
    ccm4_rawToSections (TopCat.of (ComplexPoint X)) ⊤ ≫
      (globalSectionsSingularCochainComplexIntIsoExtendField ℚ X).hom =
    HomologicalComplex.extendMap
      (topOpenToGlobalSingularCochainSheafComplex ℚ (TopCat.of (ComplexPoint X)))
      ComplexShape.embeddingUpNat := by
  dsimp only [ccm4_rawToSections, globalSectionsSingularCochainComplexIntIsoExtendField,
    Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  rw [Category.assoc]
  erw [Iso.inv_hom_id_assoc]
  change HomologicalComplex.extendMap _ _ ≫ HomologicalComplex.extendMap _ _ = _
  rw [← HomologicalComplex.extendMap_comp]
  congr 1
  ext n
  rw [topOpenToGlobalSingularCochainSheafComplex_f]
  rfl
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem ccm4_rawToSections_global_homology (X : Over (Spec ↧ℂ)) (n : ℕ)
    (r : (globalRawSingularCochainComplex ℚ (TopCat.of (ComplexPoint X))).homology n) :
    HomologicalComplex.homologyMap (ccm4_rawToSections (TopCat.of (ComplexPoint X)) ⊤) (n : ℤ)
      (((globalRawSingularCochainComplex ℚ (TopCat.of (ComplexPoint X))).extendHomologyIso
        ComplexShape.embeddingUpNat (j := n) rfl).inv r) =
      (HomologicalComplex.homologyMapIso
        (globalSectionsSingularCochainComplexIntIsoExtendField ℚ X) (n : ℤ)).inv
        (((globalSingularCochainSheafComplex ℚ (TopCat.of (ComplexPoint X))).extendHomologyIso
          ComplexShape.embeddingUpNat (j := n) rfl).inv
          (HomologicalComplex.homologyMap
            (topOpenToGlobalSingularCochainSheafComplex ℚ (TopCat.of (ComplexPoint X))) n r)) := by
  let Y := TopCat.of (ComplexPoint X)
  let R := globalRawSingularCochainComplex ℚ Y
  let G := globalSingularCochainSheafComplex ℚ Y
  let e := HomologicalComplex.homologyMapIso
    (globalSectionsSingularCochainComplexIntIsoExtendField ℚ X) (n : ℤ)
  let eR := R.extendHomologyIso ComplexShape.embeddingUpNat (j := n) rfl
  let eG := G.extendHomologyIso ComplexShape.embeddingUpNat (j := n) rfl
  apply ConcreteCategory.injective_of_mono_of_preservesPullback e.hom
  rw [Iso.inv_hom_id_apply]
  apply ConcreteCategory.injective_of_mono_of_preservesPullback eG.hom
  rw [Iso.inv_hom_id_apply]
  have hh : HomologicalComplex.homologyMap (ccm4_rawToSections Y ⊤) (n : ℤ) ≫
      e.hom ≫ eG.hom = eR.hom ≫ HomologicalComplex.homologyMap
        (topOpenToGlobalSingularCochainSheafComplex ℚ Y) n := by
    change HomologicalComplex.homologyMap _ _ ≫ HomologicalComplex.homologyMap _ _ ≫ _ = _
    rw [← Category.assoc, ← HomologicalComplex.homologyMap_comp, ccm4_rawToSections_global]
    exact HomologicalComplex.extendHomologyIso_hom_naturality _ _ rfl
  have h := ConcreteCategory.congr_hom hh (eR.inv r)
  simp only [ConcreteCategory.comp_apply] at h
  exact h.trans (congrArg (fun x => HomologicalComplex.homologyMap
    (topOpenToGlobalSingularCochainSheafComplex ℚ Y) n x) (Iso.inv_hom_id_apply eR r))
end GlobalComparison

section EdgeComparison
open HodgeLean.Foundations TopCat.Sheaf CategoryTheory.Limits
set_option linter.auxLemma false
attribute [local implicit_reducible] TopCat.Sheaf TopCat.instCategorySheaf._aux_1 TopCat.instCategorySheaf._aux_3 TopCat.instCategorySheaf._aux_5
variable (X : Over (Spec ↧ℂ))
local instance ccm4_edge_derived : HasDerivedCategory (AnalyticAdditiveSheaf X) := HasDerivedCategory.standard _
local instance : HasDerivedCategory (CategoryTheory.Sheaf
  (Opens.grothendieckTopology (TopCat.of (ComplexPoint X))) AddCommGrpCat) := ccm4_edge_derived X
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem ccm4_edge_kInjective
    (I : CochainComplex (AnalyticAdditiveSheaf X) ℤ) [I.IsKInjective] (n : ℤ)
    (x : DerivedCategory.Q.obj (integerConstantSingleComplex (TopCat.of (ComplexPoint X))) ⟶
      (DerivedCategory.Q.obj I)⟦n⟧) :
    Localization.SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q
      (cohomologyClassToHypercohomology X I n
        (CochainComplex.kInjectiveDerivedHomAddEquivCohomologyClass
          (integerConstantSingleComplex (TopCat.of (ComplexPoint X))) I n x)) =
      DerivedCategory.Q.map (constantIntegerSheafComplexIntIsoSingle X).hom ≫ x := by
  change Localization.SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q
    ((Localization.SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) (0 : ℤ) rfl
      (constantIntegerSheafComplexIntIsoSingle X).hom).comp
      (CochainComplex.kInjectiveDerivedHomAddEquivCohomologyClass
        (integerConstantSingleComplex (TopCat.of (ComplexPoint X))) I n x).toSmallShiftedHom
      (add_zero n)) = _
  rw [Localization.SmallShiftedHom.equiv_comp, Localization.SmallShiftedHom.equiv_mk₀]
  rw [ccm4_kInjective_localization]
  simp only [ShiftedHom.mk₀_comp]
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem ccm4_forgetSupport_hom (S : Closeds (ComplexPoint X)) (n : ℕ)
    (u : TopCat.Sheaf.supportH (TopCat.of (ComplexPoint X)) S
      ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj (AddCommGrpCat.of ℚ)) n) :
    (ComplexPoint.forgetSupport ℚ X S n u).hom =
      DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map
        ((CategoryTheory.Sheaf.freeAbelianSheafTerminalIso isTerminalTop).inv ≫
          cokernel.π ((CategoryTheory.Sheaf.freeAbelianSheaf
            (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))).map
            (homOfLE (le_top : S.compl ≤ ⊤))))) ≫ u.hom := by
  change ((CategoryTheory.Abelian.Ext.mk₀
    (CategoryTheory.Sheaf.freeAbelianSheafTerminalIso isTerminalTop).inv).comp
      ((CategoryTheory.Abelian.Ext.mk₀
        (cokernel.π ((CategoryTheory.Sheaf.freeAbelianSheaf
          (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))).map
          (homOfLE (le_top : S.compl ≤ ⊤))))).comp u (zero_add n)) (zero_add n)).hom = _
  rw [CategoryTheory.Abelian.Ext.comp_hom, CategoryTheory.Abelian.Ext.comp_hom,
    CategoryTheory.Abelian.Ext.mk₀_hom, CategoryTheory.Abelian.Ext.mk₀_hom]
  simp only [ShiftedHom.mk₀_comp, ← Category.assoc, ← CategoryTheory.Functor.map_comp]
  rfl
variable [HasExt.{0} (CategoryTheory.Sheaf
  (Opens.grothendieckTopology (TopCat.of (ComplexPoint X))) AddCommGrpCat)]
local instance (A B : CochainComplex (CategoryTheory.Sheaf
    (Opens.grothendieckTopology (TopCat.of (ComplexPoint X))) AddCommGrpCat) ℤ) :
    Localization.HasSmallLocalizedShiftedHom.{1}
      (HomologicalComplex.quasiIso _ ℤᵘᵖ) ℤ A B := by
  intro a b
  exact Localization.hasSmallLocalizedHom_of_isLocalization _ DerivedCategory.Q
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 100000 in
private theorem ccm4_support_injective_localization (S : Closeds (ComplexPoint X)) (n : ℕ)
    (u : TopCat.Sheaf.supportH (TopCat.of (ComplexPoint X)) S
      ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj (AddCommGrpCat.of ℚ)) n) :
    let Y := TopCat.of (ComplexPoint X)
    let k := (TopCat.Sheaf.constantFunctor Y).map
        (AddCommGrpCat.ofHom (AddEquiv.ulift.symm : ℤ ≃+ ULift ℤ).toAddMonoidHom) ≫
        (CategoryTheory.Sheaf.freeAbelianSheafTerminalIso isTerminalTop).inv ≫
        cokernel.π ((CategoryTheory.Sheaf.freeAbelianSheaf (Opens.grothendieckTopology Y)).map
          (homOfLE (le_top : S.compl ≤ ⊤)))
    Localization.SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q
      (globalSectionsToHypercohomology X (ambientRationalInjectiveComplex X) (n : ℤ)
        (HomologicalComplex.homologyMap
          (supportRestrictionSectionsComplexShortComplex Y S.compl ⊤
            (ambientRationalInjectiveComplex X)).f (n : ℤ)
          (rationalSupportAddEquivSupportedInjectiveHomology X S n u))) =
      DerivedCategory.Q.map (constantIntegerSheafComplexIntIsoSingle X).hom ≫
        DerivedCategory.Q.map ((CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).map k) ≫
          u.hom ≫ (shiftFunctor _ (n : ℤ)).map
            (DerivedCategory.Q.map (ambientRationalInjectiveSingleAugmentation X)) := by
  let : (ambientRationalInjectiveComplex X).IsKInjective :=
    ambientRationalInjectiveComplex_isKInjective X
  let : QuasiIso (ambientRationalInjectiveSingleAugmentation X) :=
    ambientRationalInjectiveSingleAugmentation_quasiIso X
  have h := ccm4_relH_injective_forget (TopCat.of (ComplexPoint X)) S.compl
    ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj (AddCommGrpCat.of ℚ))
    (ambientRationalInjectiveComplex X) (ambientRationalInjectiveSingleAugmentation X) n u
  exact (congrArg (fun c => Localization.SmallShiftedHom.equiv
    (analyticQuasiIsomorphisms X) DerivedCategory.Q
      (cohomologyClassToHypercohomology X (ambientRationalInjectiveComplex X) (n : ℤ) c)) h).trans
    (ccm4_edge_kInjective X (ambientRationalInjectiveComplex X) (n : ℤ) _)
end EdgeComparison

private theorem ccm4_transport_localization {C D : Type*} [Category* C] [Category* D]
    [HasShift C ℤ] [HasShift D ℤ]
    (W : MorphismProperty C) [W.RespectsIso] [W.IsCompatibleWithShift ℤ]
    (L : C ⥤ D) [L.IsLocalization W] [L.CommShift ℤ]
    [∀ A B : C, Localization.HasSmallLocalizedShiftedHom.{1} W ℤ A B]
    {A B P Q : C} (e : A ≅ P) (f : B ≅ Q) (hf : W f.hom) (n : ℤ)
    [Localization.HasSmallLocalizedShiftedHom.{0} W ℤ P Q]
    (u : Localization.SmallShiftedHom.{0} W P Q n) :
    Localization.SmallShiftedHom.equiv W L
      ((Localization.SmallShiftedHom.mk₀.{1} W (0 : ℤ) rfl e.hom).comp
        ((Localization.SmallShiftedHom.chgUniv.{1, 0} u).comp
          (Localization.SmallShiftedHom.mk₀Inv.{1} (W := W) (0 : ℤ) rfl f.hom hf)
          (zero_add n)) (add_zero n)) =
      L.map e.hom ≫ Localization.SmallShiftedHom.equiv W L u ≫
        (shiftFunctor D n).map (L.map f.inv) := by
  rw [Localization.SmallShiftedHom.equiv_comp, Localization.SmallShiftedHom.equiv_comp,
    Localization.SmallShiftedHom.equiv_chgUniv, Localization.SmallShiftedHom.equiv_mk₀,
    Localization.SmallShiftedHom.equiv_mk₀Inv]
  simp only [ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀, Localization.isoOfHom,
    asIso_inv, ← CategoryTheory.Functor.map_inv, IsIso.Iso.inv_hom]

section ConstantComparison
open HodgeLean.Foundations
set_option linter.auxLemma false
attribute [local implicit_reducible] TopCat.Sheaf TopCat.instCategorySheaf._aux_1 TopCat.instCategorySheaf._aux_3 TopCat.instCategorySheaf._aux_5
variable (X : Over (Spec ↧ℂ))
local instance ccm4_constant_derived : HasDerivedCategory (AnalyticAdditiveSheaf X) := HasDerivedCategory.standard _
local instance : HasDerivedCategory (CategoryTheory.Sheaf
  (Opens.grothendieckTopology (TopCat.of (ComplexPoint X))) AddCommGrpCat) := ccm4_constant_derived X
variable [HasExt.{0} (CategoryTheory.Sheaf
  (Opens.grothendieckTopology (TopCat.of (ComplexPoint X))) AddCommGrpCat)]
local instance ccm4_small_derived (A B : CochainComplex (CategoryTheory.Sheaf
    (Opens.grothendieckTopology (TopCat.of (ComplexPoint X))) AddCommGrpCat) ℤ) :
    Localization.HasSmallLocalizedShiftedHom.{1}
      (HomologicalComplex.quasiIso _ ℤᵘᵖ) ℤ A B := by
  intro a b
  exact Localization.hasSmallLocalizedHom_of_isLocalization _ DerivedCategory.Q
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ccm4_constantCohomology_inverse_apply (K : Type) [Field K] (n : ℕ) (u : H^n(X; K)) :
    (hypercohomologyAddEquivConstantCohomology K X n).symm u =
    (Localization.SmallShiftedHom.mk₀.{1} (analyticQuasiIsomorphisms X) (0 : ℤ) rfl
      (constantIntegerSheafComplexIntIsoSingleULift X).hom).comp
      ((Localization.SmallShiftedHom.chgUniv.{1, 0} u).comp
        (Localization.SmallShiftedHom.mk₀Inv.{1} (W := analyticQuasiIsomorphisms X) (0 : ℤ) rfl
          (constantFieldSheafComplexIntIsoSingle K X).hom
          ((HomologicalComplex.mem_quasiIso_iff _).mpr inferInstance)) (zero_add (n : ℤ)))
      (add_zero (n : ℤ)) := by
  rfl
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ccm4_constantCohomology_inverse (K : Type) [Field K] (n : ℕ) (u : H^n(X; K)) :
    Localization.SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q
      ((hypercohomologyAddEquivConstantCohomology K X n).symm u) =
    DerivedCategory.Q.map (constantIntegerSheafComplexIntIsoSingleULift X).hom ≫
      u.hom ≫ (shiftFunctor _ (n : ℤ)).map
        (DerivedCategory.Q.map (constantFieldSheafComplexIntIsoSingle K X).inv) := by
  let : ∀ A B : CochainComplex (AnalyticAdditiveSheaf X) ℤ,
      Localization.HasSmallLocalizedShiftedHom.{1} (analyticQuasiIsomorphisms X) ℤ A B :=
    analyticHasSmallLocalizedShiftedHom X
  rw [ccm4_constantCohomology_inverse_apply X K n u]
  exact ccm4_transport_localization (analyticQuasiIsomorphisms X) DerivedCategory.Q
    (constantIntegerSheafComplexIntIsoSingleULift X) (constantFieldSheafComplexIntIsoSingle K X)
    ((HomologicalComplex.mem_quasiIso_iff _).mpr inferInstance) (n : ℤ) u

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem ccm4_constants_injective [IsIntegral X.left] [Smooth X.hom] :
    constantsToSingularCochainComplexInt X ℚ ≫ complexSingularToAmbientInjective X =
      ambientRationalInjectiveAugmentation X := by
  change HomologicalComplex.extendMap _ _ ≫ HomologicalComplex.extendMap _ _ = _
  rw [← HomologicalComplex.extendMap_comp,
    constants_comp_singularToConstantInjectiveResolution]
  rfl

open TopCat.Sheaf

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ccm4_support_edge_forget (S : Closeds (ComplexPoint X)) (n : ℕ)
    (u : TopCat.Sheaf.supportH (TopCat.of (ComplexPoint X)) S
      ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj (AddCommGrpCat.of ℚ)) n) :
    globalSectionsToHypercohomology X (ambientRationalInjectiveComplex X) (n : ℤ)
      (HomologicalComplex.homologyMap
        (supportRestrictionSectionsComplexShortComplex (TopCat.of (ComplexPoint X)) S.compl ⊤
          (ambientRationalInjectiveComplex X)).f (n : ℤ)
        (rationalSupportAddEquivSupportedInjectiveHomology X S n u)) =
    hypercohomologyMap X (ambientRationalInjectiveAugmentation X) (n : ℤ)
      ((hypercohomologyAddEquivConstantCohomology ℚ X n).symm
        (ComplexPoint.forgetSupport ℚ X S n u)) := by
  apply (Localization.SmallShiftedHom.equiv (analyticQuasiIsomorphisms X)
    DerivedCategory.Q).injective
  rw [ccm4_support_injective_localization]
  change _ = Localization.SmallShiftedHom.equiv (analyticQuasiIsomorphisms X)
    DerivedCategory.Q ((hypercohomologyAddEquivConstantCohomology ℚ X n).symm
      (ComplexPoint.forgetSupport ℚ X S n u) |>.comp
      (Localization.SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) 0 rfl
        (ambientRationalInjectiveAugmentation X)) (zero_add (n : ℤ)))
  rw [Localization.SmallShiftedHom.equiv_comp, Localization.SmallShiftedHom.equiv_mk₀,
    ccm4_constantCohomology_inverse, ccm4_forgetSupport_hom]
  simp only [ShiftedHom.comp_mk₀, ambientRationalInjectiveSingleAugmentation,
    constantIntegerSheafComplexIntIsoSingleULift, constantIntegerSheafComplexIntIsoSingle,
    Iso.trans_hom, Functor.mapIso_hom, Functor.mapIso_inv, Iso.symm_hom,
    Functor.map_comp, Category.assoc]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ccm4_singular_support_edge [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (S : Closeds (ComplexPoint X)) (n : ℕ)
    (u : TopCat.Sheaf.supportH (TopCat.of (ComplexPoint X)) S
      ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj (AddCommGrpCat.of ℚ)) n) :
    globalSectionsToHypercohomology X (rationalSingularCochainComplex (TopCat.of (ComplexPoint X)))
      (n : ℤ) (HomologicalComplex.homologyMap
        (supportRestrictionSectionsComplexShortComplex (TopCat.of (ComplexPoint X)) S.compl ⊤
          (rationalSingularCochainComplex (TopCat.of (ComplexPoint X)))).f (n : ℤ)
        ((complexSupportedSingularInjectiveHomologyIso X S.compl ⊤ (n : ℤ)).inv
          (rationalSupportAddEquivSupportedInjectiveHomology X S n u))) =
    fieldHypercohomologySingularCochainAddEquiv ℚ X (n : ℤ)
      ((hypercohomologyAddEquivConstantCohomology ℚ X n).symm
        (ComplexPoint.forgetSupport ℚ X S n u)) := by
  apply (Localization.SmallShiftedHom.postcompEquiv
    (W := analyticQuasiIsomorphisms X) (complexSingularToAmbientInjective X)
    ((HomologicalComplex.mem_quasiIso_iff _).mpr inferInstance)).injective
  change hypercohomologyMap X (complexSingularToAmbientInjective X) (n : ℤ) _ =
    hypercohomologyMap X (complexSingularToAmbientInjective X) (n : ℤ)
      (hypercohomologyMap X (constantsToSingularCochainComplexInt X ℚ) (n : ℤ) _)
  let v := (hypercohomologyAddEquivConstantCohomology ℚ X n).symm
    (ComplexPoint.forgetSupport ℚ X S n u)
  let a := (complexSupportedSingularInjectiveHomologyIso X S.compl ⊤ (n : ℤ)).inv
    (rationalSupportAddEquivSupportedInjectiveHomology X S n u)
  have h := ConcreteCategory.congr_hom
    (ccm4_supportedInjective_forget X S.compl ⊤ (n : ℤ)) a
  simp only [ConcreteCategory.comp_apply] at h
  have hi : (complexSupportedSingularInjectiveHomologyIso X S.compl ⊤ (n : ℤ)).hom a =
      rationalSupportAddEquivSupportedInjectiveHomology X S n u :=
    Iso.inv_hom_id_apply _ _
  rw [hi] at h
  have hn := globalSectionsToHypercohomology_naturality X
    (complexSingularToAmbientInjective X) (n : ℤ)
    (HomologicalComplex.homologyMap
      (supportRestrictionSectionsComplexShortComplex (TopCat.of (ComplexPoint X)) S.compl ⊤
        (rationalSingularCochainComplex (TopCat.of (ComplexPoint X)))).f (n : ℤ) a)
  have hc := (congrArg (fun k => hypercohomologyMap X k (n : ℤ) v)
    (ccm4_constants_injective X)).symm.trans
    (hypercohomologyMap_comp_apply X (constantsToSingularCochainComplexInt X ℚ)
      (complexSingularToAmbientInjective X) (n : ℤ) v)
  exact hn.symm.trans ((congrArg
    (globalSectionsToHypercohomology X (ambientRationalInjectiveComplex X) (n : ℤ))
    h.symm).trans ((ccm4_support_edge_forget X S n u).trans hc))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ccm4_forgetSupport_singular [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (S : Closeds (ComplexPoint X)) (n : ℕ)
    (u : TopCat.Sheaf.supportH (TopCat.of (ComplexPoint X)) S
      ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj (AddCommGrpCat.of ℚ)) n) :
    singularToFieldCohomology ℚ X n
      (cohomologyMap ℚ n
        (TopCat.ofHom ⟨(Homeomorph.Set.univ (ComplexPoint X)).symm,
          (Homeomorph.Set.univ (ComplexPoint X)).symm.continuous⟩)
        (relativeCohomologyToAbsolute ℚ
          (neighborhoodSupportComplementPair Set.univ (S : Set (ComplexPoint X))) n
          (supportedSingularClass X S n u))) = ComplexPoint.forgetSupport ℚ X S n u := by
  let Y := TopCat.of (ComplexPoint X)
  let (V : Opens (ComplexPoint X)) : ParacompactSpace V := openParacompactSpace X V
  let a := (complexSupportedSingularInjectiveHomologyIso X S.compl ⊤ (n : ℤ)).inv
    (rationalSupportAddEquivSupportedInjectiveHomology X S n u)
  change singularToFieldCohomology ℚ X n
    (cohomologyMap ℚ n _ (relativeCohomologyToAbsolute ℚ _ n
      (supportedRationalSingularSectionCohomologyEquivSupportComplement Y S S.isClosed ⊤ n a))) = _
  rw [ccm4_supportComplement_toAbsolute]
  have hraw := (ccm4_supported_raw_homology Y S.compl n a).trans
    (ccm4_rawToSections_global_homology X n _)
  have he := (congrArg
    (globalSectionsToHypercohomology X
      (rationalSingularCochainComplex (TopCat.of (ComplexPoint X))) (n : ℤ)) hraw).symm.trans
    (ccm4_singular_support_edge X S n u)
  exact (congrArg (fun w => (hypercohomologyAddEquivConstantCohomology ℚ X n)
    ((fieldHypercohomologySingularCochainAddEquiv ℚ X (n : ℤ)).symm w)) he).trans
    (by rw [AddEquiv.symm_apply_apply, AddEquiv.apply_symm_apply])

end ConstantComparison


end ForgetSupportComparison

set_option maxHeartbeats 400000 in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Source: Voisin, *Hodge Theory and Complex Algebraic Geometry I*, §11,
functoriality of cohomology with supports. -/
theorem ccm4_forgetSupport_supportedPullback_aux {X Z : Over (Spec ↧ℂ)}
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (f : X ⟶ Z) (S : Closeds (ComplexPoint Z)) (n : ℕ) (u :
      TopCat.Sheaf.supportH (TopCat.of (ComplexPoint Z)) S
        ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint Z))).obj
          (AddCommGrpCat.of ℚ)) n) :
    ComplexPoint.forgetSupport ℚ X (ccm4_inverseAnalyticSupport f S) n
        (ccm4_supportedPullback f S n u) =
      homPullback f n (ComplexPoint.forgetSupport ℚ Z S n u) := by
  apply (cupComparison X n).injective
  have hcmp (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom]
      [IsProjective Y.hom] (T : Closeds (ComplexPoint Y))
      (v : TopCat.Sheaf.supportH (TopCat.of (ComplexPoint Y)) T
        ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint Y))).obj
          (AddCommGrpCat.of ℚ)) n) :
      cupComparison Y n (ComplexPoint.forgetSupport ℚ Y T n v) =
        cohomologyMap ℚ n
          (TopCat.ofHom ⟨(Homeomorph.Set.univ (ComplexPoint Y)).symm,
            (Homeomorph.Set.univ (ComplexPoint Y)).symm.continuous⟩)
          (relativeCohomologyToAbsolute ℚ
            (neighborhoodSupportComplementPair Set.univ (T : Set (ComplexPoint Y))) n
            (supportedSingularClass Y T n v)) := by
    let (V : Opens (ComplexPoint Y)) : ParacompactSpace V :=
      openParacompactSpace Y V
    apply (HodgeLean.Foundations.spec_singularToFieldCohomology_bijective ℚ Y n).injective
    exact (congrArg (HodgeLean.Foundations.singularToFieldCohomology ℚ Y n)
      (ccm4_cupComparison_eq_raw Y n (ComplexPoint.forgetSupport ℚ Y T n v))).trans
      ((singularToFieldCohomology_rationalCohomologyLinearEquivSingular Y n
        (ComplexPoint.forgetSupport ℚ Y T n v)).trans
        (ccm4_forgetSupport_singular Y T n v).symm)
  change _ = cupComparison X n ((cupComparison X n).symm
    (cohomologyMap ℚ n (TopCat.ofHom (Point.continuousMap f))
      (cupComparison Z n (ComplexPoint.forgetSupport ℚ Z S n u))))
  rw [LinearEquiv.apply_symm_apply]
  exact (hcmp X (ccm4_inverseAnalyticSupport f S) (ccm4_supportedPullback f S n u)).trans
    ((ccm4_supportedPullback_univToAbsolute f S n u).trans
      (congrArg (cohomologyMap ℚ n (TopCat.ofHom (Point.continuousMap f)))
        (hcmp Z S u).symm))


open scoped TensorProduct in
private theorem ccm4_flat_unramified_reduced_domain
    (R A : Type*) [CommRing R] [IsDomain R] [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A] [Module.Flat R A] [Algebra.FormallyUnramified R A] : _root_.IsReduced A := by
  let K := FractionRing R
  have : _root_.IsReduced (K ⊗[R] A) := Algebra.FormallyUnramified.isReduced_of_field K _
  exact isReduced_of_injective (Algebra.TensorProduct.includeRight : A →ₐ[R] K ⊗[R] A)
    (Algebra.TensorProduct.includeRight_injective (IsFractionRing.injective R K))

private theorem ccm4_smooth_reduced_domain
    (R A : Type*) [CommRing R] [IsDomain R] [CommRing A] [Algebra R A]
    [Algebra.Smooth R A] : _root_.IsReduced A := by
  constructor
  intro x hx
  apply eq_zero_of_localization x
  intro p hp
  letI := hp
  obtain ⟨f, hf, n, hAlg, hTower, hEtale⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := R) (p := p)
  letI := hAlg
  letI := hTower
  letI := hEtale
  have : _root_.IsReduced (Localization.Away f) :=
    ccm4_flat_unramified_reduced_domain (MvPolynomial (Fin n) R) _
  have hz := (hx.map (algebraMap A (Localization.Away f))).eq_zero
  obtain ⟨m, hm⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers f)
    (Localization.Away f) x).mp hz
  obtain ⟨k, hk⟩ := m.property
  apply (IsLocalization.map_eq_zero_iff p.primeCompl (Localization.AtPrime p) x).mpr
  refine ⟨⟨m, ?_⟩, hm⟩
  change (m : A) ∉ p
  rw [← hk]
  exact p.primeCompl.pow_mem hf k

private theorem ccm4_smooth_reduced_integral {X Y : Scheme} (f : X ⟶ Y)
    [IsIntegral Y] [Smooth f] : AlgebraicGeometry.IsReduced X := by
  apply +allowSynthFailures isReduced_of_isReduced_stalk
  intro x
  obtain ⟨U, hU, V, hV, hxV, e, _⟩ := Smooth.exists_isStandardSmooth f x
  have : Nonempty U := ⟨⟨f x, e hxV⟩⟩
  algebraize [(f.appLE U V e).hom]
  have : Algebra.Smooth Γ(Y, U) Γ(X, V) := by
    rw [← RingHom.smooth_algebraMap]
    exact f.smooth_appLE hU hV e
  have : _root_.IsReduced Γ(X, V) := ccm4_smooth_reduced_domain Γ(Y, U) Γ(X, V)
  let _ := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hxV⟩ : V)
  have := hV.isLocalization_stalk ⟨x, hxV⟩
  exact isReduced_localizationPreserves (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl
    (X.presheaf.stalk x) inferInstance

private theorem ccm4_inverseIdeal_isReduced {X Z : Scheme}
    (f : X ⟶ Z) [Smooth f] (x : Z) :
    IsReduced (ccm3_inverseIdeal f x).subscheme := by
  have : IsIntegral (ccm3_primeIdeal Z x).subscheme :=
    inferInstanceAs (IsIntegral (cycleComponent Z x))
  have : IsReduced (CategoryTheory.Limits.pullback f
      (ccm3_primeIdeal Z x).subschemeι) :=
    ccm4_smooth_reduced_integral (CategoryTheory.Limits.pullback.snd _ _)
  exact ObjectProperty.prop_of_iso (fun Y : Scheme => IsReduced Y)
    ((ccm3_primeIdeal Z x).comapIso f).symm inferInstance

private theorem ccm4_genericLength_eq_one_of_isReduced {X Z : Scheme}
    (f : X ⟶ Z) (x : Z) [IsReduced (ccm3_inverseIdeal f x).subscheme]
    (y : (ccm3_inverseIdeal f x).subscheme)
    (hy : closure ({y} : Set (ccm3_inverseIdeal f x).subscheme) ∈
      irreducibleComponents (ccm3_inverseIdeal f x).subscheme) :
    ccm3_genericLength f x y = 1 := by
  have hfield := isField_stalk_of_closure_mem_irreducibleComponents
    (ccm3_inverseIdeal f x).subscheme y hy
  letI := hfield.toField
  exact Module.length_eq_one _ _

open scoped Classical in
private theorem ccm4_flatPullbackPrime_eq_component_sum
    {X Z : Scheme} (f : X ⟶ Z) [Smooth f] (x : Z) :
    ccm3_flatPullbackPrime f x =
      ∑ᶠ y : (ccm3_inverseIdeal f x).subscheme,
        if closure ({y} : Set (ccm3_inverseIdeal f x).subscheme) ∈
            irreducibleComponents (ccm3_inverseIdeal f x).subscheme then
          Function.locallyFinsuppWithin.single
            ((ccm3_inverseIdeal f x).subschemeι y) (1 : ℚ)
        else 0 := by
  classical
  have := ccm4_inverseIdeal_isReduced f x
  unfold ccm3_flatPullbackPrime
  apply finsum_congr
  intro y
  split_ifs with hy
  · rw [ccm4_genericLength_eq_one_of_isReduced f x y hy]
    rfl
  · rfl

private theorem ccm4_flatPullbackPrime_coeff_eq_one_of_isReduced
    {X Z : Over (Spec ↧ℂ)}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (f : X ⟶ Z) (x : Z.left) [IsReduced (ccm3_inverseIdeal f.left x).subscheme]
    (z : X.left) (hz : ccm3_flatPullbackPrime f.left x z ≠ 0) :
    ccm3_flatPullbackPrime f.left x z = 1 := by
  obtain ⟨y, rfl, hy⟩ := (ccm3_flatPullbackPrime_support f x z).mp hz
  rw [ccm3_flatPullbackPrime_coeff f x y hy,
    ccm4_genericLength_eq_one_of_isReduced f.left x y hy]
  rfl

private theorem ccm4_flatPullbackPrime_coeff_eq_one_of_smooth
    {X Z : Over (Spec ↧ℂ)}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (f : X ⟶ Z) [Smooth f.left] (x : Z.left)
    (z : X.left) (hz : ccm3_flatPullbackPrime f.left x z ≠ 0) :
    ccm3_flatPullbackPrime f.left x z = 1 := by
  have := ccm4_inverseIdeal_isReduced f.left x
  exact ccm4_flatPullbackPrime_coeff_eq_one_of_isReduced f x z hz

private theorem ccm4_chartNormalProjectionCoclass_pullback
    {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
    (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (c : ℕ)
    (e : OpenPartialHomeomorph M (E × (Fin c → ℂ)))
    (d : OpenPartialHomeomorph N (F × (Fin c → ℂ)))
    (S : Set M) (T : Set N)
    (hS : ∀ y ∈ e.source, y ∈ S ↔ (e y).2 = 0)
    (hT : ∀ y ∈ d.source, y ∈ T ↔ (d y).2 = 0)
    (V : Set M) (W : Set N) (hV : V ⊆ e.source) (hW : W ⊆ d.source)
    (φ : neighborhoodSupportComplementPair V S ⟶ neighborhoodSupportComplementPair W T)
    (hφ : ∀ y : V, (d (TopPair.Hom.fst φ y).1).2 = (e y.1).2) :
    relativeCohomologyMap ℚ (2 * c) φ
      (chartNormalProjectionCoclass F c d T hT W hW) =
        chartNormalProjectionCoclass E c e S hS V hV := by
  have hcomp : φ ≫ chartNormalProjectionPair F c d T hT W hW =
      chartNormalProjectionPair E c e S hS V hV := by
    apply MorphismProperty.Arrow.Hom.ext
    · ext y
      apply Subtype.ext
      change (d (TopPair.Hom.snd φ y).1.1).2 = (e y.1.1).2
      have hw : (TopPair.Hom.snd φ y).1 = TopPair.Hom.fst φ y.1 :=
        TopPair.Hom.w_apply φ y
      rw [hw]
      exact hφ y.1
    · ext y
      exact hφ y
  unfold chartNormalProjectionCoclass
  rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp, hcomp]

private theorem ccm4_supportedSingularClass_weighted_sum
    (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    {ι : Type*} (S : ι → Closeds (ComplexPoint X))
    (T : Closeds (ComplexPoint X)) (h : ∀ i, S i ≤ T) (n : ℕ)
    (a : ι → ℚ)
    (u : ∀ i, TopCat.Sheaf.supportH (TopCat.of (ComplexPoint X)) (S i)
      ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj
        (AddCommGrpCat.of ℚ)) n) :
    supportedSingularClass X T n (∑ᶠ i, a i • supportEnlarge X (h i) n (u i)) =
      ∑ᶠ i, a i • relativeCohomologyMap ℚ n
        (neighborhoodSupportEnlargePairMap _ (SetLike.coe_subset_coe.mpr (h i)))
        (supportedSingularClass X (S i) n (u i)) := by
  rw [(supportedSingularClass X T n).map_finsum]
  apply finsum_congr
  intro i
  rw [map_rat_smul, supportedSingularClass_restrict]

private theorem ccm4_supportedSingularClass_smooth_component_sum
    {X Z : Over (Spec ↧ℂ)}
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (f : X ⟶ Z) [Smooth f.left] (q : ℕ) (x : Z.left)
    (hx : Order.coheight x = q)
    (h : ∀ z : {z : X.left // ccm3_flatPullbackPrime f.left x z ≠ 0},
      cycleComponentAnalyticClosedSupport X z.1 ≤
        ccm4_inverseAnalyticSupport f (cycleComponentAnalyticClosedSupport Z x)) :
    supportedSingularClass X
        (ccm4_inverseAnalyticSupport f (cycleComponentAnalyticClosedSupport Z x)) (2 * q)
        (∑ᶠ z : {z : X.left // ccm3_flatPullbackPrime f.left x z ≠ 0},
          ccm3_flatPullbackPrime f.left x z.1 • supportEnlarge X (h z) (2 * q)
            (cycleComponentSupportedInjectiveClass X z.1
              (ccm3_flatPullbackPrime_codimension f q x hx z.1 z.2))) =
      ∑ᶠ z : {z : X.left // ccm3_flatPullbackPrime f.left x z ≠ 0},
        relativeCohomologyMap ℚ (2 * q)
          (neighborhoodSupportEnlargePairMap _ (SetLike.coe_subset_coe.mpr (h z)))
          (supportedSingularClass X (cycleComponentAnalyticClosedSupport X z.1) (2 * q)
            (cycleComponentSupportedInjectiveClass X z.1
              (ccm3_flatPullbackPrime_codimension f q x hx z.1 z.2))) := by
  rw [ccm4_supportedSingularClass_weighted_sum]
  apply finsum_congr
  intro z
  rw [ccm4_flatPullbackPrime_coeff_eq_one_of_smooth f x z.1 z.2, one_smul]

private theorem ccm4_splitSubmersion_chart
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]
    {g : E → F} {A : E →L[ℂ] F} {a : E}
    (hg : HasStrictFDerivAt g A a) (B : F →L[ℂ] E)
    (hAB : A.comp B = ContinuousLinearMap.id ℂ F) :
    ∃ e : OpenPartialHomeomorph E (F × A.ker),
      a ∈ e.source ∧ ∀ y : E, (e y).1 = g y := by
  letI : CompleteSpace E := FiniteDimensional.complete ℂ E
  let L := (B.splitKernelEquiv A hAB).symm
  let K : E →L[ℂ] A.ker :=
    (ContinuousLinearMap.snd ℂ F A.ker).comp L.toContinuousLinearMap
  have hd : HasStrictFDerivAt (fun y => (g y, K y)) L.toContinuousLinearMap a := by
    convert hg.prodMk K.hasStrictFDerivAt using 1
    ext y <;> rfl
  exact ⟨hd.toOpenPartialHomeomorph _, hd.mem_toOpenPartialHomeomorph_source,
    fun _ => rfl⟩


private theorem ccm4_splitSubmersion_support_chart
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]
    {g : E → F} {A : E →L[ℂ] F} {a : E}
    (hg : HasStrictFDerivAt g A a) (B : F →L[ℂ] E)
    (hAB : A.comp B = ContinuousLinearMap.id ℂ F) :
    ∃ e : OpenPartialHomeomorph E (F × A.ker),
      a ∈ e.source ∧ (∀ y : E, (e y).1 = g y) ∧
      ∀ S : Set F, e '' (e.source ∩ g ⁻¹' S) =
        e.target ∩ S ×ˢ (Set.univ : Set A.ker) := by
  obtain ⟨e, ha, he⟩ := ccm4_splitSubmersion_chart hg B hAB
  refine ⟨e, ha, he, fun S => ?_⟩
  ext w
  constructor
  · rintro ⟨y, ⟨hy, hS⟩, rfl⟩
    exact ⟨e.map_source hy, (he y).symm ▸ hS, Set.mem_univ _⟩
  · rintro ⟨hw, hS, _⟩
    refine ⟨e.symm w, ⟨e.map_target hw, ?_⟩, e.right_inv hw⟩
    change g (e.symm w) ∈ S
    rw [← he, e.right_inv hw]
    exact hS


private theorem ccm4_smooth_relative_etale_coordinates
    {X Z : Scheme} (f : X ⟶ Z) [Smooth f] (y : X) :
    ∃ (U : Z.Opens) (V : X.Opens) (_ : IsAffineOpen U) (_ : IsAffineOpen V)
      (hVU : V ≤ f ⁻¹ᵁ U), y ∈ V ∧
      ∃ (n : ℕ) (g : MvPolynomial (Fin n) Γ(Z, U) →+* Γ(X, V)),
        g.comp MvPolynomial.C = (f.appLE U V hVU).hom ∧ g.Etale := by
  obtain ⟨U, hU, V, hV, hy, hVU, hf⟩ := Smooth.exists_isStandardSmooth f y
  obtain ⟨n, g, hg, hEtale⟩ := hf.exists_etale_mvPolynomial
  exact ⟨U, V, hU, hV, hVU, hy, n, g, hg, hEtale⟩


private theorem ccm4_inverseAnalyticSupport_eq_component_union
    {X Z : Over (Spec ↧ℂ)}
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (f : X ⟶ Z) (x : Z.left) :
    (ccm4_inverseAnalyticSupport f (cycleComponentAnalyticClosedSupport Z x) :
        Set (ComplexPoint X)) =
      ⋃ z : {z : X.left // ccm3_flatPullbackPrime f.left x z ≠ 0},
        (cycleComponentAnalyticClosedSupport X z.1 : Set (ComplexPoint X)) := by
  let I := ccm3_inverseIdeal f.left x
  have hrange : Set.range I.subschemeι = f.left ⁻¹' closure ({x} : Set Z.left) := by
    rw [I.range_subschemeι]
    simp only [I, ccm3_inverseIdeal, Scheme.IdealSheafData.support_comap,
      ccm3_primeIdeal]
    rfl
  ext a
  change f.left a.underlying ∈ closure ({x} : Set Z.left) ↔ _
  constructor
  · intro ha
    have har : a.underlying ∈ Set.range I.subschemeι := by
      rw [hrange]
      exact ha
    obtain ⟨b, hb⟩ := har
    let C := irreducibleComponent b
    have hC : C ∈ irreducibleComponents I.subscheme :=
      irreducibleComponent_mem_irreducibleComponents b
    let y := hC.1.genericPoint
    have hy : closure ({y} : Set I.subscheme) = C :=
      hC.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ hC)
    have hz : ccm3_flatPullbackPrime f.left x (I.subschemeι y) ≠ 0 :=
      (ccm3_flatPullbackPrime_support f x _).mpr ⟨y, rfl, hy ▸ hC⟩
    apply Set.mem_iUnion.mpr
    refine ⟨⟨I.subschemeι y, hz⟩, ?_⟩
    change a.underlying ∈ closure ({I.subschemeι y} : Set X.left)
    rw [← hb]
    have hbc : b ∈ closure ({y} : Set I.subscheme) := hy.symm ▸ mem_irreducibleComponent
    have him := image_closure_subset_closure_image I.subschemeι.continuous
      (s := ({y} : Set I.subscheme))
    simpa only [Set.image_singleton] using him ⟨b, hbc, rfl⟩
  · intro ha
    obtain ⟨z, hz⟩ := Set.mem_iUnion.mp ha
    obtain ⟨y, heq, hy⟩ := (ccm3_flatPullbackPrime_support f x z.1).mp z.2
    change a.underlying ∈ closure ({z.1} : Set X.left) at hz
    have hclosed : IsClosed (f.left ⁻¹' closure ({x} : Set Z.left)) :=
      isClosed_closure.preimage f.left.continuous
    apply (hclosed.closure_subset_iff.mpr ?_) hz
    rw [Set.singleton_subset_iff, ← heq, ← hrange]
    exact ⟨y, rfl⟩


private theorem ccm4_generic_component_isolation
    {Y : Type*} [TopologicalSpace Y] [T0Space Y]
    (hfin : (irreducibleComponents Y).Finite)
    (y : Y) (hy : closure ({y} : Set Y) ∈ irreducibleComponents Y) :
    ∃ U : Opens Y, y ∈ U ∧ (U : Set Y) ⊆ closure ({y} : Set Y) ∧
      ∀ z : Y, closure ({z} : Set Y) ∈ irreducibleComponents Y →
        z ≠ y → Disjoint (U : Set Y) (closure ({z} : Set Y)) := by
  let C := closure ({y} : Set Y)
  let A := irreducibleComponents Y \ {C}
  have hclosed : IsClosed (⋃₀ A) := by
    rw [Set.sUnion_eq_biUnion]
    exact hfin.sdiff.isClosed_biUnion fun D hD =>
      isClosed_of_mem_irreducibleComponents D hD.1
  let U : Opens Y := ⟨(⋃₀ A)ᶜ, hclosed.isOpen_compl⟩
  have hyU : y ∈ U := by
    rintro ⟨D, hD, hyD⟩
    have hsub : C ⊆ D := (isClosed_of_mem_irreducibleComponents D hD.1).closure_subset_iff.mpr
      (Set.singleton_subset_iff.mpr hyD)
    have hDC : D = C := Set.Subset.antisymm (hy.2 hD.1.1 hsub) hsub
    exact hD.2 (Set.mem_singleton_iff.mpr hDC)
  refine ⟨U, hyU, ?_, ?_⟩
  · have hcl := closure_sUnion_irreducibleComponents_sdiff_singleton hfin C hy
    change (U : Set Y) ⊆ C
    rw [← hcl]
    exact subset_closure
  · intro z hz hzy
    apply Set.disjoint_left.mpr
    intro a ha haz
    apply ha
    refine Set.mem_sUnion.mpr ⟨closure ({z} : Set Y), ⟨hz, ?_⟩, haz⟩
    intro heq
    apply hzy
    exact (inseparable_iff_closure_eq.mpr (Set.mem_singleton_iff.mp heq)).eq

private theorem ccm4_inverse_component_isolating_open
    {X Z : Over (Spec ↧ℂ)}
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (f : X ⟶ Z) (x : Z.left)
    (y : (ccm3_inverseIdeal f.left x).subscheme)
    (hy : closure ({y} : Set (ccm3_inverseIdeal f.left x).subscheme) ∈
      irreducibleComponents (ccm3_inverseIdeal f.left x).subscheme) :
    ∃ V : X.left.Opens, (ccm3_inverseIdeal f.left x).subschemeι y ∈ V ∧
      Point.overOpen V ∩
          (ccm4_inverseAnalyticSupport f (cycleComponentAnalyticClosedSupport Z x) :
            Set (ComplexPoint X)) =
        Point.overOpen V ∩
          (cycleComponentAnalyticClosedSupport X
            ((ccm3_inverseIdeal f.left x).subschemeι y) : Set (ComplexPoint X)) := by
  let I := ccm3_inverseIdeal f.left x
  let Y := I.subscheme
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian I.subschemeι
  have : CompactSpace X.left := (quasiCompact_iff_compactSpace X.hom).mp inferInstance
  have : CompactSpace Y := (quasiCompact_iff_compactSpace I.subschemeι).mp inferInstance
  let : IsNoetherian Y := { toIsLocallyNoetherian := inferInstance, toCompactSpace := inferInstance }
  obtain ⟨U, hyU, hUC, _⟩ := ccm4_generic_component_isolation
    (Y := Y) NoetherianSpace.finite_irreducibleComponents y hy
  obtain ⟨W, hW, hWU⟩ := I.subschemeι.isClosedEmbedding.isEmbedding.isInducing.isOpen_iff.mp U.isOpen
  let V : X.left.Opens := ⟨W, hW⟩
  have hrange : Set.range I.subschemeι = f.left ⁻¹' closure ({x} : Set Z.left) := by
    rw [I.range_subschemeι]
    simp only [I, ccm3_inverseIdeal, Scheme.IdealSheafData.support_comap, ccm3_primeIdeal]
    rfl
  have him : I.subschemeι '' closure ({y} : Set Y) =
      closure ({I.subschemeι y} : Set X.left) := by
    rw [← I.subschemeι.isClosedEmbedding.isClosedMap.closure_image_eq_of_continuous
      I.subschemeι.continuous, Set.image_singleton]
  refine ⟨V, ?_, ?_⟩
  · change y ∈ I.subschemeι ⁻¹' W
    rw [hWU]
    exact hyU
  · ext a
    change (a.underlying ∈ W ∧ f.left a.underlying ∈ closure ({x} : Set Z.left)) ↔
      (a.underlying ∈ W ∧ a.underlying ∈ closure ({I.subschemeι y} : Set X.left))
    constructor
    · rintro ⟨haW, ha⟩
      refine ⟨haW, ?_⟩
      have har : a.underlying ∈ Set.range I.subschemeι := by
        rw [hrange]
        exact ha
      obtain ⟨b, hb⟩ := har
      have hbU : b ∈ U := by
        change b ∈ (U : Set Y)
        rw [← hWU]
        change I.subschemeι b ∈ W
        rw [hb]
        exact haW
      rw [← him]
      exact ⟨b, hUC hbU, hb⟩
    · rintro ⟨haW, ha⟩
      refine ⟨haW, ?_⟩
      rw [← him] at ha
      obtain ⟨b, _, hb⟩ := ha
      have har : a.underlying ∈ Set.range I.subschemeι := ⟨b, hb⟩
      rw [hrange] at har
      exact har

open Filter Topology

private theorem ccm4_chart_composition_eventually
    (X Y Z : Over (Spec ↧ℂ)) (f : X ⟶ Y) (g : Y ⟶ Z)
    (d e k : ℕ) [SmoothOfRelativeDimension d X.hom]
    [SmoothOfRelativeDimension e Y.hom] [SmoothOfRelativeDimension k Z.hom]
    (z : ComplexPoint X) :
    (inclusionInComplexCharts Z Y g e k (Point.map f z) ∘
      inclusionInComplexCharts Y X f d e z) =ᶠ[𝓝 (localChart X d z z)]
        inclusionInComplexCharts Z X (f ≫ g) d k z := by
  let a := localChart X d z z
  have hcont : ContinuousAt
      (fun v => Point.map f ((localChart X d z).symm v)) a :=
    (Point.continuous_map f).continuousAt.comp
      ((localChart X d z).continuousAt_symm
        ((localChart X d z).map_source (mem_localChart_source X d z)))
  have hm : Point.map f ((localChart X d z).symm a) ∈
      (localChart Y e (Point.map f z)).source := by
    rw [(localChart X d z).left_inv (mem_localChart_source X d z)]
    exact mem_localChart_source Y e (Point.map f z)
  have he := hcont ((localChart Y e (Point.map f z)).open_source.mem_nhds hm)
  filter_upwards [he] with v hv
  dsimp only [Function.comp_def, inclusionInComplexCharts]
  rw [(localChart Y e (Point.map f z)).left_inv hv]
  simp only [Point.map_comp_apply]

private theorem ccm4_chart_derivative_comp
    (X Y Z : Over (Spec ↧ℂ)) (f : X ⟶ Y) (g : Y ⟶ Z)
    (d e k : ℕ) [SmoothOfRelativeDimension d X.hom]
    [SmoothOfRelativeDimension e Y.hom] [SmoothOfRelativeDimension k Z.hom]
    (z : ComplexPoint X) :
    (fderiv ℂ (inclusionInComplexCharts Z Y g e k (Point.map f z))
      (localChart Y e (Point.map f z) (Point.map f z))).comp
      (fderiv ℂ (inclusionInComplexCharts Y X f d e z) (localChart X d z z)) =
    fderiv ℂ (inclusionInComplexCharts Z X (f ≫ g) d k z) (localChart X d z z) := by
  have hf := (analyticAt_inclusionInComplexCharts Y X f d e z).differentiableAt.hasFDerivAt
  have hg := (analyticAt_inclusionInComplexCharts Z Y g e k (Point.map f z)).differentiableAt.hasFDerivAt
  rw [← inclusionInComplexCharts_at_center Y X f d e z] at hg
  simpa only [inclusionInComplexCharts_at_center] using ((hg.comp _ hf).congr_of_eventuallyEq
    (ccm4_chart_composition_eventually X Y Z f g d e k z).symm).fderiv.symm

private theorem ccm4_chart_derivative_id
    (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (z : ComplexPoint X) :
    fderiv ℂ (inclusionInComplexCharts X X (𝟙 X) d d z) (localChart X d z z) =
      ContinuousLinearMap.id ℂ (Fin d → ℂ) := by
  have he : inclusionInComplexCharts X X (𝟙 X) d d z =ᶠ[𝓝 (localChart X d z z)] id := by
    filter_upwards [(localChart X d z).open_target.mem_nhds
      ((localChart X d z).map_source (mem_localChart_source X d z))] with v hv
    exact (localChart X d z).right_inv hv
  exact ((hasFDerivAt_id (localChart X d z z)).congr_of_eventuallyEq he).fderiv

private theorem ccm4_chart_derivative_rightInverse_of_section
    (X Y : Over (Spec ↧ℂ)) (f : X ⟶ Y) (s : Y ⟶ X) (hs : s ≫ f = 𝟙 Y)
    (d e : ℕ) [SmoothOfRelativeDimension d X.hom]
    [SmoothOfRelativeDimension e Y.hom] (z : ComplexPoint Y) :
    (fderiv ℂ (inclusionInComplexCharts Y X f d e (Point.map s z))
      (localChart X d (Point.map s z) (Point.map s z))).comp
      (fderiv ℂ (inclusionInComplexCharts X Y s e d z) (localChart Y e z z)) =
        ContinuousLinearMap.id ℂ (Fin e → ℂ) := by
  rw [ccm4_chart_derivative_comp Y X Y s f e d e z, hs,
    ccm4_chart_derivative_id]

/-- Smooth pullback of a normalized supported prime class is the sum of the
inverse-image component classes, weighted by their generic lengths. The coefficients
are those of `ccm3_flatPullbackPrime`, identified by `ccm3_flatPullbackPrime_coeff`.
Source: Fulton, *Intersection Theory*, second edition, §1.7 and §19.1;
Voisin, *Hodge Theory and Complex Algebraic Geometry I*, §11, smooth pullback of cycle classes. -/
theorem ccm4_supportedPullback_prime_aux {X Z : Over (Spec ↧ℂ)}
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (f : X ⟶ Z) [Smooth f.left] (q : ℕ) (x : Z.left)
    (hx : Order.coheight x = q) :
    ccm4_supportedPullback f (cycleComponentAnalyticClosedSupport Z x) (2 * q)
        (cycleComponentSupportedInjectiveClass Z x hx) =
      ∑ᶠ z : {z : X.left // ccm3_flatPullbackPrime f.left x z ≠ 0},
        ccm3_flatPullbackPrime f.left x z.1 •
          supportEnlarge X (ccm4_flatPullbackPrime_support_le_aux f x z.1 z.2) (2 * q)
            (cycleComponentSupportedInjectiveClass X z.1
              (ccm3_flatPullbackPrime_codimension f q x hx z.1 z.2)) :=
  ccm5_ccm4_supportedPullback_prime_aux f q x hx

end HodgeLean.Adapters
