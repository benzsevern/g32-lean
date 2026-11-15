import HodgeLean.RealDefs.FundamentalClass.Constants
import HodgeLean.RealDefs.FundamentalClass.Augmentation
import HodgeLean.RealDefs.Operations

/-! # `[X] = 1`: the section of a lift of the unit

A lift `g` of the unit sends the generator of `ℤ[X(ℂ)]` to the constant section `1`
(`freeAbelianSheafHomAddEquiv_eq_constSection`), and the singular augmentation in degree `0` is
upstream's inclusion of constants as `0`-cochains (`rationalSingularAugmentation_f_zero`). So the
supported section `g ≫ ρ⁰` is the sheafified constant raw cochain
(`constantRawCochain_sheafify_eq`). -/

open CategoryTheory Limits TopologicalSpace Opposite AlgebraicGeometry ComplexPoint
open AlgebraicTopology.Singular

namespace HodgeLean.RealDefs

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

local instance (V : Opens (ComplexPoint X)) : ParacompactSpace V := openParacompactSpace X V

omit [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- In degree `0`, the singular augmentation is the inclusion of constants as `0`-cochains. -/
lemma rationalSingularAugmentation_f_zero :
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0 𝓒(↧(ComplexPoint X); ℚ)).inv ≫
        (rationalSingularAugmentation X).f 0 ≫
        ((singularCochainSheafComplex ℚ (TopCat.of (ComplexPoint X))).extendXIso
          ComplexShape.embeddingUpNat (rfl : ComplexShape.embeddingUpNat.f 0 = 0)).hom =
      constantsToSingularCochainZeroSheaf ℚ (TopCat.of (ComplexPoint X)) := by
  simp [rationalSingularAugmentation, constantFieldSheafComplexIntIsoSingle,
    constantsToSingularCochainSheafComplex]
  rw [HomologicalComplex.extendMap_f _ ComplexShape.embeddingUpNat (i := 0) (i' := 0) rfl,
    HomologicalComplex.extendSingleIso_inv_f _ _ (i := 0) (i' := 0) rfl]
  simp [CochainComplex.fromSingle₀Equiv_symm_apply_f_zero]

omit [Smooth X.hom] [IsProjective X.hom] in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A lift `g` of the unit sends the generator of `ℤ[X(ℂ)]` through the pair sheaf to the
morphism `uliftℤ → ℚ` of the unit. -/
lemma freeAbelianSheafTerminalIso_inv_comp_eq (Z : Closeds (ComplexPoint X))
    (g : TopCat.Sheaf.pairSheaf' (TopCat.of (ComplexPoint X)) Z.compl ⊤ Z.compl (top_inf_eq _) ⟶
      (TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj (AddCommGrpCat.of ℚ))
    (hg : forgetSupport ℚ X Z 0 (Abelian.Ext.mk₀ g) = unitClass X) :
    (CategoryTheory.Sheaf.freeAbelianSheafTerminalIso isTerminalTop).inv ≫
        cokernel.π ((CategoryTheory.Sheaf.freeAbelianSheaf
          (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))).map
            (homOfLE (le_top : Z.compl ≤ ⊤))) ≫ g =
      uliftIntegerToIntegerConstantSheaf X ≫ integerToFieldConstantSheaf ℚ X 1 := by
  apply (Abelian.Ext.mk₀_bijective _ _).1
  refine Eq.trans ?_ hg
  rw [← Abelian.Ext.mk₀_comp_mk₀, ← Abelian.Ext.mk₀_comp_mk₀]
  rfl

omit [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] in
/-- Sheafification maps act on unit images through the presheaf map. -/
lemma sheafifyMap_toSheafify_apply {P Q : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ ⥤ AddCommGrpCat.{0}}
    (η : P ⟶ Q) (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (x : P.obj U) :
    (sheafifyMap (Opens.grothendieckTopology (TopCat.of (ComplexPoint X))) η).app U
        ((toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X))) P).app U x) =
      (toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X))) Q).app U (η.app U x) :=
  (ConcreteCategory.congr_hom (NatTrans.congr_app
    (toSheafify_naturality (Opens.grothendieckTopology (TopCat.of (ComplexPoint X))) η) U) x).symm

omit [Smooth X.hom] [IsProjective X.hom] in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A lift `g` of the unit sends the generator of `ℤ[X(ℂ)]` to the constant section `1`. -/
lemma freeAbelianSheafHomAddEquiv_eq_constSection (Z : Closeds (ComplexPoint X))
    (g : TopCat.Sheaf.pairSheaf' (TopCat.of (ComplexPoint X)) Z.compl ⊤ Z.compl (top_inf_eq _) ⟶
      (TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj (AddCommGrpCat.of ℚ))
    (hg : forgetSupport ℚ X Z 0 (Abelian.Ext.mk₀ g) = unitClass X) :
    CategoryTheory.Sheaf.freeAbelianSheafHomAddEquiv ⊤ _
        (cokernel.π ((CategoryTheory.Sheaf.freeAbelianSheaf
          (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))).map
            (homOfLE (le_top : Z.compl ≤ ⊤))) ≫ g) =
      constSection (T := TopCat.of (ComplexPoint X)) (AddCommGrpCat.of ℚ) ⊤ 1 := by
  let iso := CategoryTheory.Sheaf.freeAbelianSheafTerminalIso
    (J := Opens.grothendieckTopology (TopCat.of (ComplexPoint X))) isTerminalTop
  have h : cokernel.π ((CategoryTheory.Sheaf.freeAbelianSheaf
      (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))).map
        (homOfLE (le_top : Z.compl ≤ ⊤))) ≫ g =
      iso.hom ≫ uliftIntegerToIntegerConstantSheaf X ≫ integerToFieldConstantSheaf ℚ X 1 := by
    rw [← freeAbelianSheafTerminalIso_inv_comp_eq X Z g hg, Iso.hom_inv_id_assoc]
  rw [CategoryTheory.Sheaf.freeAbelianSheafHomAddEquiv_apply, h]
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, ConcreteCategory.comp_apply,
    CategoryTheory.Sheaf.freeAbelianSheafGenerator]
  erw [sheafifyMap_toSheafify_apply, sheafifyMap_toSheafify_apply, sheafifyMap_toSheafify_apply]
  congr 1
  simp [FreeAbelianGroup.uniqueEquiv]

omit [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The constant section `1` is the sheafified constant raw cochain. -/
lemma constantsToSingularCochainZeroSheaf_constSection (V : Opens (ComplexPoint X)) :
    (constantsToSingularCochainZeroSheaf ℚ (TopCat.of (ComplexPoint X))).hom.app (op V)
        (constSection (T := TopCat.of (ComplexPoint X)) (AddCommGrpCat.of ℚ) V 1) =
      (openRawToSingularCochainSheafComplex ℚ (TopCat.of (ComplexPoint X)) V).f 0
        (constantRawCochain (TopCat.of (ComplexPoint X)) V) := by
  change (sheafifyMap _ (constantsToSingularCochainZero ℚ (TopCat.of (ComplexPoint X)))).app (op V)
    ((toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
      ((Functor.const (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ).obj (AddCommGrpCat.of ℚ))).app
        (op V) (1 : ℚ)) = _
  rw [sheafifyMap_toSheafify_apply]
  rfl

omit [IsProjective X.hom] in
set_option maxHeartbeats 800000 in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The supported section of `g ≫ ρ⁰`, for a lift `g` of the unit, is the sheafified constant raw
cochain. -/
lemma constantRawCochain_sheafify_eq (Z : Closeds (ComplexPoint X))
    (g : TopCat.Sheaf.pairSheaf' (TopCat.of (ComplexPoint X)) Z.compl ⊤ Z.compl (top_inf_eq _) ⟶
      (TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj (AddCommGrpCat.of ℚ))
    (hg : forgetSupport ℚ X Z 0 (Abelian.Ext.mk₀ g) = unitClass X)
    (c : (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex (TopCat.of (ComplexPoint X))
      Z.compl ⊤ (rationalSingularCochainComplex (TopCat.of (ComplexPoint X)))).X₁.cycles
        ((0 : ℕ) : ℤ))
    (hc : (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex (TopCat.of (ComplexPoint X))
      Z.compl ⊤ (rationalSingularCochainComplex (TopCat.of (ComplexPoint X)))).X₁.iCycles _ c =
      (TopCat.Sheaf.pairSheafHomIsoSupportedSections (TopCat.of (ComplexPoint X)) Z.compl ⊤ Z.compl
        (top_inf_eq _) ((rationalSingularCochainComplex (TopCat.of (ComplexPoint X))).X 0)).hom
        (g ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 _).inv ≫
          (rationalSingularAugmentation X).f 0)) :
    (openRawToSingularCochainSheafComplex ℚ (TopCat.of (ComplexPoint X)) ⊤).f 0
        (constantRawCochain (TopCat.of (ComplexPoint X)) ⊤) =
      ((singularCochainSheafComplex ℚ (TopCat.of (ComplexPoint X))).extendXIso
        ComplexShape.embeddingUpNat
        (rfl : ComplexShape.embeddingUpNat.f 0 = ((0 : ℕ) : ℤ))).hom.hom.app (op ⊤)
        ((TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex (TopCat.of (ComplexPoint X))
          Z.compl ⊤ (rationalSingularCochainComplex (TopCat.of (ComplexPoint X)))).f.f
            ((0 : ℕ) : ℤ)
          ((TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex (TopCat.of (ComplexPoint X))
            Z.compl ⊤ (rationalSingularCochainComplex (TopCat.of (ComplexPoint X)))).X₁.iCycles _ c)) := by
  let h : TopCat.Sheaf.pairSheaf' (TopCat.of (ComplexPoint X)) Z.compl ⊤ Z.compl (top_inf_eq _) ⟶
      (rationalSingularCochainComplex (TopCat.of (ComplexPoint X))).X 0 :=
    g ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 _).inv ≫ (rationalSingularAugmentation X).f 0
  have hinc := ConcreteCategory.congr_hom
    (TopCat.Sheaf.pairSheafHomIsoSupportedSections_hom_inclusion (TopCat.of (ComplexPoint X))
      Z.compl ⊤ Z.compl (top_inf_eq _)
      ((rationalSingularCochainComplex (TopCat.of (ComplexPoint X))).X 0)) h
  rw [ConcreteCategory.comp_apply] at hinc
  rw [hc]
  erw [hinc]
  have he : TopCat.Sheaf.pairSheafHomEvaluation (TopCat.of (ComplexPoint X)) Z.compl ⊤ Z.compl
      (top_inf_eq _) ((rationalSingularCochainComplex (TopCat.of (ComplexPoint X))).X 0) h =
      ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 _).inv ≫
        (rationalSingularAugmentation X).f 0).hom.app (op ⊤)
        (CategoryTheory.Sheaf.freeAbelianSheafHomAddEquiv ⊤ _
          (cokernel.π ((CategoryTheory.Sheaf.freeAbelianSheaf
            (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))).map
              (homOfLE (le_top : Z.compl ≤ ⊤))) ≫ g)) := rfl
  erw [he, freeAbelianSheafHomAddEquiv_eq_constSection X Z g hg]
  refine (constantsToSingularCochainZeroSheaf_constSection X ⊤).symm.trans ?_
  rw [← rationalSingularAugmentation_f_zero X]
  rfl

end HodgeLean.RealDefs
