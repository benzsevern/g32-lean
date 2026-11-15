import HodgeLean.Adapters.HolomorphicPeriodsComparisonProofs
import HodgeLean.Adapters.ResolutionClassActionProofs

/-! # Unit normalization of the fixed singular comparison

The degree-zero unit fixes the scalar in every degree. HC no distance;
AV milestone no distance.
-/
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open AlgebraicTopology.Singular HodgeLean.RealDefs HodgeLean.Foundations Set Topology
namespace HodgeLean.Adapters

set_option maxRecDepth 4000
set_option maxHeartbeats 400000
set_option linter.auxLemma false
attribute [local implicit_reducible] TopCat.Sheaf TopCat.instCategorySheaf._aux_1
  TopCat.instCategorySheaf._aux_3 TopCat.instCategorySheaf._aux_5

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem bh11_constant_unit_chain (X : Over (Spec ↧ℂ)) :
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

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The singular constant unit is sent to the actual sheaf constant class one.
Source: Bredon, Sheaf Theory, second edition, III.1, augmentation by constant cochains;
CycleClassFlatComparisonProofs, the degree-zero constant-unit chain comparison. -/
theorem bh11_singular_unit_aux
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] :
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
  exact (Category.assoc _ _ _).trans (bh11_constant_unit_chain X)

/-- The fixed cup comparison has scalar one in every degree.
Source: `exists_cupComparison_eq_smul`, `cupComparison_unit`, and the constant-unit comparison. -/
theorem bh11_cupComparison_eq_raw_aux
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (n : ℕ) (v : HQ X n) :
    cupComparison X n v =
      rationalCohomologyLinearEquivSingular X n (HQ.linearEquiv X n v) := by
  let (U : Opens (ComplexPoint X)) : ParacompactSpace U := openParacompactSpace X U
  have hu : rationalCohomologyLinearEquivSingular X 0
      (HQ.linearEquiv X 0 (cupUnit X)) = Singular.unit (TopCat.of (ComplexPoint X)) := by
    apply (spec_singularToFieldCohomology_bijective ℚ X 0).injective
    rw [singularToFieldCohomology_rationalCohomologyLinearEquivSingular,
      bh11_singular_unit_aux]
    rfl
  let := pathConnectedSpace_complexPoint X
  obtain ⟨r, _, he⟩ := exists_cupComparison_eq_smul X
  have h := cupComparison_unit X
  rw [he, hu] at h
  have h1 : r = 1 := (smul_left_injective ℚ
    (Singular.unit_ne_zero (R := ℚ) (TopCat.of (ComplexPoint X))))
      (h.trans (one_smul ℚ (Singular.unit (TopCat.of (ComplexPoint X)))).symm)
  rw [he, h1, one_smul]

end HodgeLean.Adapters
