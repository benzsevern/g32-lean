import HodgeLean.RealDefs.FundamentalClass.Bridge
import HodgeConjecture.Lemmas.AlgebraicGeometry.Cohomology.SupportedSingularModel

/-! # `[X] = 1`, layer 4: the constant cochain

The augmentation `ρ : ℚ[0] → C^•` into sheafified singular cochains, followed by upstream's
comparison `C^• → I^•`, is the injective augmentation `ι`
(`rationalSingularAugmentation_comp_singularToConstantInjectiveComplex`). So the relative class
of `Ext.mk₀ g` is the relative class of the supported singular section of `g ≫ ρ⁰`
(`complexSupportInjectiveSectionCohomologyEquiv_mk₀`). -/

open CategoryTheory Limits Abelian Opposite TopologicalSpace

namespace HodgeLean.RealDefs

section Naturality

open TopCat.Sheaf

variable (X : TopCat.{0}) (U V W : Opens X) (hW : V ⊓ U = W)

set_option linter.auxLemma false
attribute [local implicit_reducible] TopCat.Sheaf TopCat.instCategorySheaf._aux_1
  TopCat.instCategorySheaf._aux_3 TopCat.instCategorySheaf._aux_5

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A map of complexes sends the degree-`0` class of the supported section `h` to that of
`h ≫ f⁰`. -/
lemma homologyMap_supportedSections_homologyπ
    {K L : CochainComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat) ℤ}
    (f : K ⟶ L) (h : pairSheaf' X U V W hW ⟶ K.X 0)
    (cK : (((supportEvaluation X V).mapHomologicalComplex ℤᵘᵖ).obj
        (((sheafSectionsSupportedOutside X U).mapHomologicalComplex ℤᵘᵖ).obj K)).cycles 0)
    (hK : (((supportEvaluation X V).mapHomologicalComplex ℤᵘᵖ).obj
        (((sheafSectionsSupportedOutside X U).mapHomologicalComplex ℤᵘᵖ).obj K)).iCycles 0 cK =
      (pairSheafHomIsoSupportedSections X U V W hW (K.X 0)).hom h)
    (cL : (((supportEvaluation X V).mapHomologicalComplex ℤᵘᵖ).obj
        (((sheafSectionsSupportedOutside X U).mapHomologicalComplex ℤᵘᵖ).obj L)).cycles 0)
    (hL : (((supportEvaluation X V).mapHomologicalComplex ℤᵘᵖ).obj
        (((sheafSectionsSupportedOutside X U).mapHomologicalComplex ℤᵘᵖ).obj L)).iCycles 0 cL =
      (pairSheafHomIsoSupportedSections X U V W hW (L.X 0)).hom (h ≫ f.f 0)) :
    HomologicalComplex.homologyMap (((supportEvaluation X V).mapHomologicalComplex ℤᵘᵖ).map
        (((sheafSectionsSupportedOutside X U).mapHomologicalComplex ℤᵘᵖ).map f)) 0
        ((((supportEvaluation X V).mapHomologicalComplex ℤᵘᵖ).obj
          (((sheafSectionsSupportedOutside X U).mapHomologicalComplex ℤᵘᵖ).obj K)).homologyπ 0 cK) =
      (((supportEvaluation X V).mapHomologicalComplex ℤᵘᵖ).obj
        (((sheafSectionsSupportedOutside X U).mapHomologicalComplex ℤᵘᵖ).obj L)).homologyπ 0 cL := by
  rw [← ConcreteCategory.comp_apply, HomologicalComplex.homologyπ_naturality,
    ConcreteCategory.comp_apply]
  congr 1
  apply cycles_ext
  rw [← ConcreteCategory.comp_apply, HomologicalComplex.cyclesMap_i, ConcreteCategory.comp_apply,
    hK, hL]
  have H := ConcreteCategory.congr_hom
    (pairSheafHomIsoSupportedSections_naturality X U V W hW (f.f 0)) h
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at H
  change ((sheafSectionsSupportedOutside X U).map (f.f 0)).hom.app (op V) _ = _
  rw [H]
  rfl


set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The supported section of `g ≫ φ⁰` underlies a degree-`0` cycle, for any chain map `φ` out of
`F[0]`. -/
lemma exists_supportedSections_cycle (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat)
    {K : CochainComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat) ℤ}
    (φ : (CochainComplex.singleFunctor _ 0).obj F ⟶ K) (g : pairSheaf' X U V W hW ⟶ F) :
    ∃ c : (((supportEvaluation X V).mapHomologicalComplex ℤᵘᵖ).obj
        (((sheafSectionsSupportedOutside X U).mapHomologicalComplex ℤᵘᵖ).obj K)).cycles 0,
      (((supportEvaluation X V).mapHomologicalComplex ℤᵘᵖ).obj
        (((sheafSectionsSupportedOutside X U).mapHomologicalComplex ℤᵘᵖ).obj K)).iCycles 0 c =
      (pairSheafHomIsoSupportedSections X U V W hW (K.X 0)).hom
        (g ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 F).inv ≫ φ.f 0) := by
  let Φ := homComplexPairSheafIsoSupportedSections X U V W hW K
  let ψ := (CochainComplex.singleFunctor _ 0).map g ≫ φ
  let z := CochainComplex.HomComplex.Cocycle.ofHom ψ
  let c₀ := (CochainComplex.HomComplex.leftHomologyData _ K 0).cyclesIso.inv z
  refine ⟨HomologicalComplex.cyclesMap Φ.hom 0 c₀, ?_⟩
  rw [← ConcreteCategory.comp_apply, HomologicalComplex.cyclesMap_i, ConcreteCategory.comp_apply,
    ← fromSingleEquiv_ofHom_single_comp g φ]
  have hc : (CochainComplex.HomComplex _ K).iCycles 0 c₀ =
      CochainComplex.HomComplex.Cochain.ofHom ψ := by
    change ((CochainComplex.HomComplex.leftHomologyData _ K 0).cyclesIso.inv ≫
      ((CochainComplex.HomComplex _ K).sc 0).iCycles) z = _
    rw [ShortComplex.LeftHomologyData.cyclesIso_inv_comp_iCycles]
    rfl
  rw [hc]
  rfl

end Naturality

section Constants

open AlgebraicGeometry ComplexPoint AlgebraicTopology.Singular

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

local instance (V : Opens (ComplexPoint X)) : ParacompactSpace V := openParacompactSpace X V

set_option linter.auxLemma false
attribute [local implicit_reducible] TopCat.Sheaf TopCat.instCategorySheaf._aux_1
  TopCat.instCategorySheaf._aux_3 TopCat.instCategorySheaf._aux_5

omit [IsProjective X.hom] in


set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The singular augmentation followed by the comparison to the injective resolution is the
injective augmentation. -/
lemma rationalSingularAugmentation_comp_singularToConstantInjectiveComplex :
    rationalSingularAugmentation X ≫
        singularToConstantInjectiveComplex (TopCat.of (ComplexPoint X))
          (exists_contractibleOpen_le X) =
      ambientRationalInjectiveSingleAugmentation X := by
  dsimp only [rationalSingularAugmentation, ambientRationalInjectiveSingleAugmentation,
    singularToConstantInjectiveComplex, ambientRationalInjectiveAugmentation]
  rw [Category.assoc, ← HomologicalComplex.extendMap_comp,
    constants_comp_singularToConstantInjectiveResolution]



set_option maxHeartbeats 1000000 in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Layer 4, part (i): the relative class of `Ext.mk₀ g` is that of the supported section of
`g ≫ ρ⁰`, where `ρ` is the augmentation into sheafified singular cochains. -/
theorem complexSupportInjectiveSectionCohomologyEquiv_mk₀ (Z : Closeds (ComplexPoint X))
    (g : TopCat.Sheaf.pairSheaf' (TopCat.of (ComplexPoint X)) Z.compl ⊤ Z.compl (top_inf_eq _) ⟶
      (TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj (AddCommGrpCat.of ℚ))
    (c : (((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) ⊤).mapHomologicalComplex
        ℤᵘᵖ).obj (supportedRationalSingularCochainComplex (TopCat.of (ComplexPoint X))
          Z.compl)).cycles 0)
    (hc : (((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) ⊤).mapHomologicalComplex
        ℤᵘᵖ).obj (supportedRationalSingularCochainComplex (TopCat.of (ComplexPoint X))
          Z.compl)).iCycles 0 c =
      (TopCat.Sheaf.pairSheafHomIsoSupportedSections (TopCat.of (ComplexPoint X)) Z.compl ⊤ Z.compl
        (top_inf_eq _) ((rationalSingularCochainComplex (TopCat.of (ComplexPoint X))).X 0)).hom
        (g ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 _).inv ≫
          (rationalSingularAugmentation X).f 0)) :
    complexSupportInjectiveSectionCohomologyEquiv X Z ⊤ 0
        (rationalSupportAddEquivSupportedInjectiveHomology X Z 0 (Abelian.Ext.mk₀ g)) =
      supportedRationalSingularSectionCohomologyEquivSupportComplement
        (TopCat.of (ComplexPoint X)) Z Z.isClosed ⊤ 0
        ((((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) ⊤).mapHomologicalComplex
          ℤᵘᵖ).obj (supportedRationalSingularCochainComplex (TopCat.of (ComplexPoint X))
            Z.compl)).homologyπ 0 c) := by
  have := ambientRationalInjectiveComplex_isKInjective X
  obtain ⟨cI, hI⟩ := exists_supportedSections_cycle (TopCat.of (ComplexPoint X)) Z.compl ⊤ Z.compl
    (top_inf_eq _) _ (ambientRationalInjectiveSingleAugmentation X) g
  have hmap := homologyMap_supportedSections_homologyπ (TopCat.of (ComplexPoint X)) Z.compl ⊤
    Z.compl (top_inf_eq _)
    (singularToConstantInjectiveComplex (TopCat.of (ComplexPoint X)) (exists_contractibleOpen_le X))
    _ c hc cI (by
      have hI' := hI
      rw [← rationalSingularAugmentation_comp_singularToConstantInjectiveComplex X] at hI'
      simp only [HomologicalComplex.comp_f, Category.assoc] at hI' ⊢
      exact hI')
  have hB : rationalSupportAddEquivSupportedInjectiveHomology X Z 0 (Abelian.Ext.mk₀ g) =
      _ := @relHAddEquivSupportedSectionsHomology_mk₀_eq_homologyπ (TopCat.of (ComplexPoint X))
        Z.compl ⊤ Z.compl (top_inf_eq _) inferInstance _ (ambientRationalInjectiveComplex X)
        (ambientRationalInjectiveComplex_isKInjective X) (ambientRationalInjectiveSingleAugmentation X)
        (ambientRationalInjectiveSingleAugmentation_quasiIso X) g cI hI
  have h2 := hB.trans hmap.symm
  refine (congrArg (complexSupportInjectiveSectionCohomologyEquiv X Z ⊤ 0) h2).trans ?_
  change supportedRationalSingularSectionCohomologyEquivSupportComplement
      (TopCat.of (ComplexPoint X)) Z Z.isClosed ⊤ 0
      ((complexSupportedSingularInjectiveHomologyIso X Z.compl ⊤ 0).inv
        ((complexSupportedSingularInjectiveHomologyIso X Z.compl ⊤ 0).hom
          ((((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) ⊤).mapHomologicalComplex
            ℤᵘᵖ).obj (supportedRationalSingularCochainComplex (TopCat.of (ComplexPoint X))
              Z.compl)).homologyπ 0 c))) = _
  rw [← ConcreteCategory.comp_apply, Iso.hom_inv_id]
  rfl

end Constants

end HodgeLean.RealDefs
