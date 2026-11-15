import HodgeConjecture.Definitions.AlgebraicTopology.Support.CohomologyInjectiveModel
import HodgeLean.RealDefs.DegreeZero
import HodgeLean.RealDefs.Operations
import HodgeLean.RealDefs.Port.OpenRestrictedLowest
import HodgeLean.RealDefs.Port.SectionRestriction
import HodgeLean.RealDefs.Port.SupportNormalization

/-! # `[X] = 1`, layers 2 and 3: the supported-sections model and the assembly

Roadmap item U3 (`docs/notes/fundamental-class-unit.md`): the fundamental class of the generic
point, `cycleComponentSheafClass X x hx` with `Order.coheight x = 0`, is the constant class
`unitClass X = fieldCohomologyClass ℚ X 1`. The proof follows the constant class through each layer
of `cycleComponentSupportedClassNormalizationIso`, in degree `0`.

* Layer 2 (`relHAddEquivSupportedSectionsHomology_mk₀`): in degree `0`, the supported-sections
  model sends `Ext.mk₀ g` to the class of the cocycle `g ≫ ι`.
-/

open CategoryTheory Limits Abelian Opposite TopologicalSpace

namespace HodgeLean.RealDefs

section KInjective

open CochainComplex

variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- In degree zero, the K-injective comparison sends the class of a chain map to its cocycle. -/
lemma kInjectiveDerivedHomAddEquivCohomologyClass_mk₀
    (K L : CochainComplex C ℤ) [L.IsKInjective] (φ : K ⟶ L) :
    kInjectiveDerivedHomAddEquivCohomologyClass K L 0
        (ShiftedHom.mk₀ (0 : ℤ) rfl (DerivedCategory.Q.map φ)) =
      HomComplex.CohomologyClass.mk (HomComplex.Cocycle.ofHom φ) := by
  apply (kInjectiveDerivedHomAddEquivCohomologyClass K L 0).symm.injective
  rw [AddEquiv.symm_apply_apply, kInjectiveDerivedHomAddEquivCohomologyClass_symm_mk]
  have : HomComplex.Cocycle.equivHomShift.symm (HomComplex.Cocycle.ofHom φ) =
      ShiftedHom.mk₀ (0 : ℤ) rfl φ := by
    apply HomComplex.Cocycle.equivHomShift.injective
    rw [AddEquiv.apply_symm_apply]
    ext p
    simp [HomComplex.Cocycle.equivHomShift_apply, ShiftedHom.mk₀,
      HomComplex.Cochain.rightUnshift_v _ _ _ _ _ _ _ (add_zero p),
      HomComplex.Cochain.comp_v _ _ (add_zero 0) p p p (add_zero p) (add_zero p),
      CategoryTheory.shiftFunctorZero', CochainComplex.shiftFunctorZero_inv_app_f]
  rw [this, ShiftedHom.map_mk₀]

end KInjective

section Cycles

open CochainComplex

/-- Cycles of a complex of abelian groups are determined by their underlying elements. -/
lemma cycles_ext {ι : Type*} {c : ComplexShape ι} {K : HomologicalComplex AddCommGrpCat c} {i : ι}
    {a b : K.cycles i} (h : K.iCycles i a = K.iCycles i b) : a = b :=
  (ConcreteCategory.injective_of_mono_of_preservesPullback (K.iCycles i)) h

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The class of a degree-`0` cocycle of a Hom complex is the homology class of any cycle with the
same underlying cochain. -/
lemma homologyAddEquiv_symm_mk_zero {C : Type*} [Category C] [Preadditive C]
    {K L : CochainComplex C ℤ} (z : HomComplex.Cocycle K L 0) (c : (HomComplex K L).cycles 0)
    (hc : (HomComplex K L).iCycles 0 c = (z : HomComplex.Cochain K L 0)) :
    (HomComplex.homologyAddEquiv K L 0).symm (HomComplex.CohomologyClass.mk z) =
      (HomComplex K L).homologyπ 0 c := by
  apply (HomComplex.homologyAddEquiv K L 0).injective
  rw [AddEquiv.apply_symm_apply]
  change HomComplex.CohomologyClass.mk z =
    (HomComplex.leftHomologyData K L 0).homologyIso.hom ((HomComplex K L).sc 0 |>.homologyπ c)
  rw [← ConcreteCategory.comp_apply,
    ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom, ConcreteCategory.comp_apply]
  change _ = HomComplex.CohomologyClass.mk _
  congr 1
  apply Subtype.ext
  change _ = (HomComplex.leftHomologyData K L 0).i
    ((HomComplex.leftHomologyData K L 0).cyclesIso.hom c)
  rw [← ConcreteCategory.comp_apply, ShortComplex.LeftHomologyData.cyclesIso_hom_comp_i]
  exact hc.symm


open TopCat.Sheaf in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The degree-`0` cochain of `single g ≫ ι` is `g` followed by the degree-`0` component of `ι`. -/
lemma fromSingleEquiv_ofHom_single_comp {C : Type*} [Category C] [Preadditive C]
    [HasZeroObject C] {P F : C} {I : CochainComplex C ℤ} (g : P ⟶ F)
    (ι : (CochainComplex.singleFunctor C 0).obj F ⟶ I) :
    HomComplex.Cochain.fromSingleEquiv (zero_add 0)
        (HomComplex.Cochain.ofHom ((CochainComplex.singleFunctor C 0).map g ≫ ι)) =
      g ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 F).inv ≫ ι.f 0 := by
  simp [HomComplex.Cochain.fromSingleEquiv, CochainComplex.singleFunctor,
    HomologicalComplex.single_map_f_self]

end Cycles

section Bridge

open TopCat.Sheaf

variable (X : TopCat.{0}) (U V W : Opens X) (hW : V ⊓ U = W)
  [HasExt.{0} (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat)]

set_option linter.auxLemma false
attribute [local implicit_reducible] TopCat.Sheaf TopCat.instCategorySheaf._aux_1
  TopCat.instCategorySheaf._aux_3 TopCat.instCategorySheaf._aux_5

noncomputable local instance :
    HasDerivedCategory (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat) :=
  HasDerivedCategory.standard _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- In degree `0`, the class of `Ext.mk₀ g` is the class of the cocycle `g ≫ ι`. -/
theorem relHAddEquivSupportedSectionsHomology_mk₀
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat)
    (I : CochainComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat) ℤ)
    [I.IsKInjective] (ι : (CochainComplex.singleFunctor _ 0).obj F ⟶ I) [QuasiIso ι]
    (g : pairSheaf' X U V W hW ⟶ F) :
    relHAddEquivSupportedSectionsHomology X U V W hW F I ι 0 (Ext.mk₀ g) =
      (HomologicalComplex.homologyMapIso
        (homComplexPairSheafIsoSupportedSections X U V W hW I) 0).hom
        ((CochainComplex.HomComplex.homologyAddEquiv _ I 0).symm
          (CochainComplex.HomComplex.CohomologyClass.mk
            (CochainComplex.HomComplex.Cocycle.ofHom
              ((CochainComplex.singleFunctor _ 0).map g ≫ ι)))) := by
  dsimp only [relHAddEquivSupportedSectionsHomology, AddEquiv.trans_apply]
  rw [Ext.homAddEquiv_apply, Ext.mk₀_hom]
  have h1 : (isoHomCongrAddEquiv (Iso.refl _)
      ((shiftFunctor (DerivedCategory _) ((0 : ℕ) : ℤ)).mapIso
        (asIso (DerivedCategory.Q.map ι))))
      (ShiftedHom.mk₀ ((0 : ℕ) : ℤ) (by simp)
        ((DerivedCategory.singleFunctor _ 0).map g)) =
      ShiftedHom.mk₀ (0 : ℤ) rfl (DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map g ≫ ι)) := by
    rw [isoHomCongrAddEquiv_apply, Iso.refl_inv, Category.id_comp, Functor.mapIso_hom, asIso_hom,
      ShiftedHom.mk₀, ShiftedHom.mk₀, Category.assoc]
    erw [← (shiftFunctorZero' (DerivedCategory _) ((0 : ℕ) : ℤ) (by simp)).inv.naturality]
    rw [Functor.map_comp, Functor.id_map, Category.assoc]
    have : (DerivedCategory.singleFunctor (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat) 0).map g =
        DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map g) := by
      with_unfolding_all rfl
    rw [this]
    rfl
  erw [h1, kInjectiveDerivedHomAddEquivCohomologyClass_mk₀]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- In degree `0`, `Ext.mk₀ g` goes to the class of the cycle whose underlying supported section is
the evaluation of `g ≫ ι₀`, where `ι₀ : F ⟶ I⁰` is the degree-`0` component of `ι`. -/
theorem relHAddEquivSupportedSectionsHomology_mk₀_eq_homologyπ
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat)
    (I : CochainComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat) ℤ)
    [I.IsKInjective] (ι : (CochainComplex.singleFunctor _ 0).obj F ⟶ I) [QuasiIso ι]
    (g : pairSheaf' X U V W hW ⟶ F)
    (c : (((supportEvaluation X V).mapHomologicalComplex ℤᵘᵖ).obj
        (((sheafSectionsSupportedOutside X U).mapHomologicalComplex ℤᵘᵖ).obj I)).cycles 0)
    (hc : (((supportEvaluation X V).mapHomologicalComplex ℤᵘᵖ).obj
        (((sheafSectionsSupportedOutside X U).mapHomologicalComplex ℤᵘᵖ).obj I)).iCycles 0 c =
      (pairSheafHomIsoSupportedSections X U V W hW (I.X 0)).hom
        (g ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 F).inv ≫ ι.f 0)) :
    relHAddEquivSupportedSectionsHomology X U V W hW F I ι 0 (Ext.mk₀ g) =
      (((supportEvaluation X V).mapHomologicalComplex ℤᵘᵖ).obj
        (((sheafSectionsSupportedOutside X U).mapHomologicalComplex ℤᵘᵖ).obj I)).homologyπ 0 c := by
  let Φ := homComplexPairSheafIsoSupportedSections X U V W hW I
  let φ := (CochainComplex.singleFunctor _ 0).map g ≫ ι
  have hΦ : Φ.hom.f 0 (CochainComplex.HomComplex.Cochain.ofHom φ) =
      (pairSheafHomIsoSupportedSections X U V W hW (I.X 0)).hom
        (g ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 F).inv ≫ ι.f 0) := by
    rw [← fromSingleEquiv_ofHom_single_comp g ι]
    rfl
  have hc₀ : (CochainComplex.HomComplex _ I).iCycles 0 (HomologicalComplex.cyclesMap Φ.inv 0 c) =
      CochainComplex.HomComplex.Cochain.ofHom φ := by
    rw [← ConcreteCategory.comp_apply, HomologicalComplex.cyclesMap_i, ConcreteCategory.comp_apply,
      hc, ← hΦ, ← ConcreteCategory.comp_apply, ← HomologicalComplex.comp_f, Iso.hom_inv_id]
    rfl
  rw [relHAddEquivSupportedSectionsHomology_mk₀,
    homologyAddEquiv_symm_mk_zero (CochainComplex.HomComplex.Cocycle.ofHom φ) _ hc₀,
    HomologicalComplex.homologyMapIso_hom, ← ConcreteCategory.comp_apply,
    HomologicalComplex.homologyπ_naturality, ConcreteCategory.comp_apply,
    ← ConcreteCategory.comp_apply (HomologicalComplex.cyclesMap Φ.inv 0),
    ← HomologicalComplex.cyclesMap_comp, Iso.inv_hom_id, HomologicalComplex.cyclesMap_id]
  rfl

end Bridge

section Assembly

open AlgebraicGeometry ComplexPoint AlgebraicTopology.Singular

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

/-- Restriction followed by the cohomology-sheaf comparison is the restriction of the relative
sheafification unit (upstream `Other`, `PointClassNormalization.lean`). -/
theorem complexSupportInjectiveCohomologySheafIsoRelative_restriction_section
    (S : Closeds (ComplexPoint X)) (n : ℕ)
    {V W : Opens (ComplexPoint X)} (a : W ⟶ V) :
    HomologicalComplex.homologyMap
      (TopCat.Sheaf.sectionComplexRestriction (TopCat.of (ComplexPoint X)) ℤᵘᵖ
        (complexSupportInjectiveComplex X S) a) (n : ℤ) ≫
      TopCat.Sheaf.sectionCohomologyToSheafSection (TopCat.of (ComplexPoint X))
        (complexSupportInjectiveComplex X S) (n : ℤ) W ≫
      (complexSupportInjectiveCohomologySheafIsoRelative X S n).hom.hom.app (op W) =
    (complexSupportInjectiveSectionCohomologyEquiv X S V n).toAddCommGrpIso.hom ≫
      (supportRelativeCohomologyToSheaf (TopCat.of (ComplexPoint X)) S n).app (op V) ≫
      (supportRelativeCohomologySheaf (TopCat.of (ComplexPoint X)) S n).obj.map a.op := by
  rw [TopCat.Sheaf.sectionCohomologyToSheafSection_restriction_assoc,
    (complexSupportInjectiveCohomologySheafIsoRelative X S n).hom.hom.naturality,
    complexSupportInjectiveCohomologySheafIsoRelative_section_assoc]

variable (x : X.left) {p : ℕ} (hx : Order.coheight x = p)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The normalization iso sends a supported class to the restriction, to the smooth ambient open,
of the relative sheafification unit applied to its global relative class. -/
theorem cycleComponentSupportedClassNormalizationIso_eq_restrict
    (a : CycleComponentSupportedCohomology X x p) :
    cycleComponentSupportedClassNormalizationIso X x hx a =
      (supportRelativeCohomologySheaf (TopCat.of (ComplexPoint X))
        (cycleComponentSupport X x) (2 * p)).obj.map
          (homOfLE (le_top : cycleComponentSmoothSupportAmbientOpen X x ≤ ⊤)).op
        ((supportRelativeCohomologyToSheaf (TopCat.of (ComplexPoint X))
          (cycleComponentSupport X x) (2 * p)).app (op ⊤)
          (complexSupportInjectiveSectionCohomologyEquiv X
            (cycleComponentAnalyticClosedSupport X x) ⊤ (2 * p)
            (rationalSupportAddEquivSupportedInjectiveHomology X
              (cycleComponentAnalyticClosedSupport X x) (2 * p) a))) := by
  have h := cycleComponentSupportedClassNormalizationIso_apply X x hx a
  rw [cycleComponentSmoothSupportLowestSectionCohomologyComplexIso,
    TopCat.Sheaf.openRestrictedLowestSectionCohomologyIso_hom] at h
  refine h.trans ?_
  exact ConcreteCategory.congr_hom
    (complexSupportInjectiveCohomologySheafIsoRelative_restriction_section X
      (cycleComponentAnalyticClosedSupport X x) (2 * p)
      (homOfLE (show cycleComponentSmoothSupportAmbientOpen X x ≤ ⊤ from le_top)))
    (rationalSupportAddEquivSupportedInjectiveHomology X
      (cycleComponentAnalyticClosedSupport X x) (2 * p) a)


/-- `[X] = 1` reduces to the normalization iso sending a supported lift of the unit to the coclass
section. -/
theorem cycleComponentSheafClass_eq_unitClass_of_normalization (hx : Order.coheight x = 0)
    (u : CycleComponentSupportedCohomology X x 0)
    (hu : forgetSupport ℚ X (cycleComponentAnalyticClosedSupport X x) 0 u = unitClass X)
    (h : cycleComponentSupportedClassNormalizationIso X x hx u =
      cycleComponentSmoothSupportCoclassSection X x hx) :
    cycleComponentSheafClass X x hx = unitClass X := by
  calc cycleComponentSheafClass X x hx
      = forgetSupport ℚ X (cycleComponentAnalyticClosedSupport X x) 0
          ((cycleComponentSupportedClassNormalizationIso X x hx).symm
            (cycleComponentSmoothSupportCoclassSection X x hx)) := rfl
    _ = unitClass X := by rw [← h, AddEquiv.symm_apply_apply, hu]

set_option linter.auxLemma false in
omit [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] in
attribute [local implicit_reducible] TopCat.Sheaf TopCat.instCategorySheaf._aux_1
  TopCat.instCategorySheaf._aux_3 TopCat.instCategorySheaf._aux_5 in
/-- Forgetting the support `X(ℂ)` itself is surjective. -/
theorem forgetSupport_surjective_of_eq_top (Z : Closeds (ComplexPoint X)) (hZ : Z = ⊤) (n : ℕ) :
    Function.Surjective (forgetSupport ℚ X Z n) := by
  have : Fact (Z.compl = ⊥) := ⟨by rw [hZ]; ext; simp⟩
  let π := cokernel.π
      ((CategoryTheory.Sheaf.freeAbelianSheaf (Opens.grothendieckTopology
        (TopCat.of (ComplexPoint X)))).map (homOfLE (le_top : Z.compl ≤ ⊤)))
  have : IsIso π := by
    have hf : (CategoryTheory.Sheaf.freeAbelianSheaf (Opens.grothendieckTopology
        (TopCat.of (ComplexPoint X)))).map (homOfLE (le_top : Z.compl ≤ ⊤)) = 0 :=
      (TopCat.Sheaf.isZero_freeAbelianSheaf_of_eq_bot _ _ Fact.out).eq_of_src _ _
    have hπ : π = cokernel.π (0 : _ ⟶ _) ≫ (cokernelIsoOfEq hf).inv := by
      rw [← π_comp_cokernelIsoOfEq_hom hf, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [hπ]
    infer_instance
  exact (Sheaf.H'.addEquivTerminal isTerminalTop _ n).surjective.comp
    (Ext.precompAddEquiv (asIso π) _ n).surjective

end Assembly

end HodgeLean.RealDefs
