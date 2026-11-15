import HodgeLean.Foundations.Topology.RationalSheafComparisonHomComplex

/-! Resolution classes and exact functors on Ext.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CochainComplex CochainComplex.HomComplex
namespace HodgeLean.Topology.RationalSheafComparison

universe w
variable {C : Type*} [Category* C] [Abelian C] [HasExt.{w} C]
  [HasDerivedCategory C] {A B : C} (R : InjectiveResolution B) {n : ℕ}

/-- Source: Bredon, Sheaf Theory, second edition, II.4. -/
theorem resolutionClass_hom_augmentation
    (z : Cocycle ((CochainComplex.singleFunctor C 0).obj A) R.cochainComplex (n : ℤ)) :
    (R.extEquivCohomologyClass.symm (.mk z)).hom.comp
      (ShiftedHom.mk₀ 0 rfl (DerivedCategory.Q.map R.ι')) (zero_add (n : ℤ)) =
        ShiftedHom.map (Cocycle.equivHomShift.symm z) DerivedCategory.Q := by
  haveI : IsIso (DerivedCategory.Q.map R.ι') := inferInstance
  simp [InjectiveResolution.extEquivCohomologyClass_symm_mk_hom,
    DerivedCategory.singleFunctorIsoCompQ, ShiftedHom.comp_mk₀, ShiftedHom.mk₀_comp,
    ← Functor.map_comp]
  erw [Category.id_comp, IsIso.inv_hom_id, CategoryTheory.Functor.map_id, Category.comp_id]

/-- Source: Bredon, Sheaf Theory, second edition, II.4. -/
theorem resolutionTransport_derivedAugmentation
    {D : Type*} [Category* D] [Abelian D] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [Limits.PreservesFiniteLimits F]
    [Limits.PreservesFiniteColimits F] {B' : D} (S : InjectiveResolution B')
    (b : F.obj B ⟶ B')
    (c : (F.mapHomologicalComplex (.up ℤ)).obj R.cochainComplex ⟶ S.cochainComplex)
    (hc : (F.mapHomologicalComplex (.up ℤ)).map R.ι' ≫ c =
      (F.mapCochainComplexSingleFunctor 0).hom.app B ≫
        (CochainComplex.singleFunctor D 0).map b ≫ S.ι') :
    F.mapDerivedCategory.map (DerivedCategory.Q.map R.ι') ≫
        F.mapDerivedCategoryFactors.hom.app R.cochainComplex ≫ DerivedCategory.Q.map c =
      (F.mapDerivedCategorySingleFunctor 0).hom.app B ≫
        (DerivedCategory.singleFunctor D 0).map b ≫ DerivedCategory.Q.map S.ι' := by
  rw [Functor.mapDerivedCategoryFactors_hom_naturality_assoc,
    ← Functor.map_comp, hc]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Functor.mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app]
  simp only [Category.assoc]
  erw [Iso.hom_inv_id_app_assoc]
  rfl

end HodgeLean.Topology.RationalSheafComparison
