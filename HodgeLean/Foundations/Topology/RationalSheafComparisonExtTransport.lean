import HodgeLean.Foundations.Topology.RationalSheafComparisonExt

/-! Transport of resolution cocycles by an exact functor.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CochainComplex CochainComplex.HomComplex
namespace HodgeLean.Topology.RationalSheafComparison

universe w w'

/-- Source: Bredon, Sheaf Theory, second edition, II.4. -/
theorem resolutionClass_transport
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasExt.{w} C] [HasExt.{w'} D] [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [Limits.PreservesFiniteLimits F]
    [Limits.PreservesFiniteColimits F]
    {A B : C} {A' B' : D} (R : InjectiveResolution B) (S : InjectiveResolution B')
    (a : A' ⟶ F.obj A) (b : F.obj B ⟶ B')
    (c : (F.mapHomologicalComplex (.up ℤ)).obj R.cochainComplex ⟶ S.cochainComplex)
    (hc : (F.mapHomologicalComplex (.up ℤ)).map R.ι' ≫ c =
      (F.mapCochainComplexSingleFunctor 0).hom.app B ≫
        (CochainComplex.singleFunctor D 0).map b ≫ S.ι')
    {n : ℕ} (z : Cocycle ((CochainComplex.singleFunctor C 0).obj A) R.cochainComplex (n : ℤ)) :
    S.extEquivCohomologyClass.symm (.mk
      (((functorCocycle F z).precomp
        ((CochainComplex.singleFunctor D 0).map a ≫
          (F.mapCochainComplexSingleFunctor 0).inv.app A)).postcomp c)) =
      ((Abelian.Ext.mk₀ a).comp
        ((R.extEquivCohomologyClass.symm (.mk z)).mapExactFunctor F) (zero_add n)).comp
          (Abelian.Ext.mk₀ b) (add_zero n) := by
  let α := R.extEquivCohomologyClass.symm (.mk z)
  let Z := ShiftedHom.map (Cocycle.equivHomShift.symm z) DerivedCategory.Q
  have hr := congrArg
    (fun k : ShiftedHom ((DerivedCategory.singleFunctor C 0).obj A)
      (DerivedCategory.Q.obj R.cochainComplex) (n : ℤ) => k.map F.mapDerivedCategory)
    (resolutionClass_hom_augmentation R z)
  rw [ShiftedHom.map_comp, ShiftedHom.map_mk₀] at hr
  have hr' : α.hom.map F.mapDerivedCategory ≫
      (F.mapDerivedCategory.map (DerivedCategory.Q.map R.ι'))⟦(n : ℤ)⟧' =
        Z.map F.mapDerivedCategory := by
    simpa only [ShiftedHom.comp_mk₀] using hr
  have hm : α.hom.map F.mapDerivedCategory ≫
      ((F.mapDerivedCategorySingleFunctor 0).hom.app B ≫
        (DerivedCategory.singleFunctor D 0).map b ≫ DerivedCategory.Q.map S.ι')⟦(n : ℤ)⟧' =
      Z.map F.mapDerivedCategory ≫
        (F.mapDerivedCategoryFactors.hom.app R.cochainComplex ≫ DerivedCategory.Q.map c)⟦(n : ℤ)⟧' := by
    rw [← resolutionTransport_derivedAugmentation R F S b c hc]
    simpa only [CategoryTheory.Functor.map_comp, Category.assoc] using congrArg
      (fun k => k ≫
        (F.mapDerivedCategoryFactors.hom.app R.cochainComplex ≫ DerivedCategory.Q.map c)⟦(n : ℤ)⟧') hr'
  haveI : IsIso (DerivedCategory.Q.map S.ι') := inferInstance
  apply Abelian.Ext.ext
  apply (cancel_mono ((DerivedCategory.Q.map S.ι')⟦(n : ℤ)⟧')).mp
  rw [← ShiftedHom.comp_mk₀ _ (0 : ℤ) rfl]
  rw [resolutionClass_hom_augmentation,
    Cocycle.equivHomShift_symm_postcomp, Cocycle.equivHomShift_symm_precomp]
  simp only [Abelian.Ext.comp_hom, Abelian.Ext.mk₀_hom, Abelian.Ext.mapExactFunctor_hom,
    ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀, ShiftedHom.map,
    CategoryTheory.Functor.map_comp, Category.assoc]
  rw [Functor.commShiftIso_hom_naturality]
  rw [← CategoryTheory.Functor.map_comp_assoc]
  rw [← Category.assoc _ _ ((DerivedCategory.Q.map c)⟦(n : ℤ)⟧')]
  change DerivedCategory.Q.map ((CochainComplex.singleFunctor D 0).map a ≫
      (F.mapCochainComplexSingleFunctor 0).inv.app A) ≫
    ShiftedHom.map (Cocycle.equivHomShift.symm (functorCocycle F z)) DerivedCategory.Q ≫
      (DerivedCategory.Q.map c)⟦(n : ℤ)⟧' = _
  rw [functorCocycle_derivedHom]
  simp only [ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀,
    CategoryTheory.Functor.map_comp, Category.assoc]
  rw [← Functor.mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  conv_rhs => simp only [← CategoryTheory.Functor.map_comp]
  have hh := (congrArg (fun k => (DerivedCategory.singleFunctor D 0).map a ≫
      (F.mapDerivedCategorySingleFunctor 0).inv.app A ≫ k) hm).symm
  simp only [α, Z, ShiftedHom.map, CategoryTheory.Functor.map_comp, Category.assoc] at hh
  convert hh using 1 <;>
    (try simp only [ShiftedHom.map, CategoryTheory.Functor.map_comp, Category.assoc,
      DerivedCategory.Q_map_single_map]) <;> rfl

end HodgeLean.Topology.RationalSheafComparison
