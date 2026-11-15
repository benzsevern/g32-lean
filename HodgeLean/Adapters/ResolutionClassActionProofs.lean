import HodgeLean.Adapters.ResolutionClassActionDefs

/-! # Proof obligations for `ResolutionClassAction`

One `_aux` per statement of `HodgeLean.Adapters.ResolutionClassAction`, all open.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory TopologicalSpace AlgebraicTopology.Simplicial
open AlgebraicGeometry ComplexPoint Opposite
open HodgeLean.Foundations

namespace HodgeLean.Adapters

local instance resolutionClassProofsHasDerivedCategory (X : Over (Spec ↧ℂ)) :
    HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard (AnalyticAdditiveSheaf X)

theorem spec_resolutionClass_comp_mk₀_aux (X : Over (Spec ↧ℂ))
    {A K : CochainComplex (AnalyticAdditiveSheaf X) ℤ} (q : A ⟶ K)
    (hq : analyticQuasiIsomorphisms X q) (L : K ⟶ K⟦(1 : ℤ)⟧) :
    (resolutionClass X q hq L).comp
        (Localization.SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) (0 : ℤ) rfl q)
        (zero_add 1) =
      (Localization.SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) (0 : ℤ) rfl q).comp
        (Localization.SmallShiftedHom.mk (analyticQuasiIsomorphisms X)
          (show ShiftedHom K K (1 : ℤ) from L)) (add_zero 1) := by
  unfold resolutionClass
  rw [Localization.SmallShiftedHom.comp_assoc (analyticQuasiIsomorphisms X) _ _ _ (zero_add 1)
      (zero_add 0) (by simp),
    Localization.SmallShiftedHom.mk₀Inv_comp_mk₀, Localization.SmallShiftedHom.comp_mk₀_id]

theorem spec_resolutionClass_unique_aux (X : Over (Spec ↧ℂ))
    {A K : CochainComplex (AnalyticAdditiveSheaf X) ℤ} (q : A ⟶ K)
    (hq : analyticQuasiIsomorphisms X q) (L : K ⟶ K⟦(1 : ℤ)⟧)
    (e : Localization.SmallShiftedHom.{1} (analyticQuasiIsomorphisms X) A A (1 : ℤ))
    (he : e.comp (Localization.SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) (0 : ℤ) rfl q)
        (zero_add 1) =
      (Localization.SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) (0 : ℤ) rfl q).comp
        (Localization.SmallShiftedHom.mk (analyticQuasiIsomorphisms X)
          (show ShiftedHom K K (1 : ℤ) from L)) (add_zero 1)) :
    e = resolutionClass X q hq L := by
  exact (Localization.SmallShiftedHom.postcompEquiv (X := A) q hq).injective
    (he.trans (spec_resolutionClass_comp_mk₀_aux X q hq L).symm)

theorem spec_hypercohomologyMap_comp_resolutionClass_aux (X : Over (Spec ↧ℂ))
    {A K : CochainComplex (AnalyticAdditiveSheaf X) ℤ} (q : A ⟶ K)
    (hq : analyticQuasiIsomorphisms X q) (L : K ⟶ K⟦(1 : ℤ)⟧) {k m : ℤ} (h : 1 + k = m)
    (α : ℍ^k(X; A)) :
    hypercohomologyMap X q m (α.comp (resolutionClass X q hq L) h) =
      (hypercohomologyMap X q k α).comp
        (Localization.SmallShiftedHom.mk (analyticQuasiIsomorphisms X)
          (show ShiftedHom K K (1 : ℤ) from L)) h := by
  change (α.comp (resolutionClass X q hq L) h).comp _ (zero_add m) =
    (α.comp _ (zero_add k)).comp _ h
  rw [Localization.SmallShiftedHom.comp_assoc (analyticQuasiIsomorphisms X) _ _ _ h
      (zero_add 1) (by simp [h]),
    Localization.SmallShiftedHom.comp_assoc (analyticQuasiIsomorphisms X) _ _ _ (zero_add k)
      (add_zero 1) (by simp [h]),
    spec_resolutionClass_comp_mk₀_aux]

theorem spec_resolutionClass_add_aux (X : Over (Spec ↧ℂ))
    {A K : CochainComplex (AnalyticAdditiveSheaf X) ℤ} (q : A ⟶ K)
    (hq : analyticQuasiIsomorphisms X q) (L L' : K ⟶ K⟦(1 : ℤ)⟧) :
    Localization.SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q
        (resolutionClass X q hq (L + L')) =
      Localization.SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q
          (resolutionClass X q hq L) +
        Localization.SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q
          (resolutionClass X q hq L') := by
  simp only [resolutionClass, Localization.SmallShiftedHom.equiv_comp,
    Localization.SmallShiftedHom.equiv_mk, ShiftedHom.map, Functor.map_add, Preadditive.add_comp,
    ShiftedHom.add_comp, ShiftedHom.comp_add]

theorem spec_resolutionClass_zero_aux (X : Over (Spec ↧ℂ))
    {A K : CochainComplex (AnalyticAdditiveSheaf X) ℤ} (q : A ⟶ K)
    (hq : analyticQuasiIsomorphisms X q) :
    Localization.SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q
        (resolutionClass X q hq 0) = 0 := by
  simp only [resolutionClass, Localization.SmallShiftedHom.equiv_comp,
    Localization.SmallShiftedHom.equiv_mk, ShiftedHom.map, Functor.map_zero, Limits.zero_comp,
    ShiftedHom.zero_comp, ShiftedHom.comp_zero]

theorem spec_resolutionClass_eq_of_Q_map_eq_aux (X : Over (Spec ↧ℂ))
    {A K : CochainComplex (AnalyticAdditiveSheaf X) ℤ} (q : A ⟶ K)
    (hq : analyticQuasiIsomorphisms X q) (L L' : K ⟶ K⟦(1 : ℤ)⟧)
    (h : DerivedCategory.Q.map L = DerivedCategory.Q.map L') :
    resolutionClass X q hq L = resolutionClass X q hq L' := by
  apply (Localization.SmallShiftedHom.equiv (analyticQuasiIsomorphisms X)
    DerivedCategory.Q).injective
  simp only [resolutionClass, Localization.SmallShiftedHom.equiv_comp,
    Localization.SmallShiftedHom.equiv_mk, ShiftedHom.map]
  erw [h]

set_option backward.isDefEq.respectTransparency false in
theorem rcaB_q_zero (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] :
    (constantCoefficientXZeroIso X ℂ).inv ≫
        (constantsToHolomorphicDeRhamComplexInt X).f ((0 : ℕ) : ℤ) ≫ (wedgeThetaXIso X 0).hom =
      constantsToHolomorphicDeRhamZeroSheaf X (dim X.left) := by
  rw [show (constantsToHolomorphicDeRhamComplexInt X).f ((0 : ℕ) : ℤ) = _ from
    HomologicalComplex.extendMap_f _ _ (i := 0) rfl]
  dsimp only [constantCoefficientXZeroIso, Iso.trans_inv, wedgeThetaXIso]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.inv_hom_id_assoc]
  rw [constantsToHolomorphicDeRhamComplex, CochainComplex.fromSingle₀Equiv_symm_apply_f_zero]
  simp [HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq]

set_option backward.isDefEq.respectTransparency false in
theorem rcaB_comp_zero (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    (L : Ω•(X) ⟶ Ω•(X)⟦(1 : ℤ)⟧) :
    (constantCoefficientXZeroIso X ℂ).inv ≫
        (constantsToHolomorphicDeRhamComplexInt X ≫ L).f ((0 : ℕ) : ℤ) ≫
          (wedgeThetaShiftXIso X 0).hom =
      constantsToHolomorphicDeRhamZeroSheaf X (dim X.left) ≫ wedgeThetaComponent X L 0 := by
  rw [← rcaB_q_zero, HomologicalComplex.comp_f]
  dsimp only [wedgeThetaComponent]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

theorem rcaB_constantGlobalSection (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    (c : ℂ) :
    (constantsToHolomorphicDeRhamZeroSheaf X (dim X.left)).hom.app (op ⊤)
        (constantGlobalSection X ℂ c) =
      (toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
        (holomorphicDeRhamPresheaf X (dim X.left) 0)).app (op ⊤)
        (Submodule.Quotient.mk (Algebra.DeRham.ofConstant ℂ _ c)) := by
  have h := toSheafify_naturality (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
    (constantsToHolomorphicDeRhamZero X (dim X.left))
  have h2 := congrArg (fun f => (f.app (op ⊤)).hom c) h
  simp only [NatTrans.comp_app] at h2
  exact h2.symm

theorem rcaB_ofSubsingleton_symm_covectorWedgeForm_const {d : ℕ}
    (a : (Fin d → ℂ) →L[ℂ] ℂ) (c : ℂ) :
    (ContinuousAlternatingMap.ofSubsingleton ℂ (Fin d → ℂ) ℂ (0 : Fin 1)).symm
        (covectorWedgeForm a (ContinuousAlternatingMap.constOfIsEmpty ℂ (Fin d → ℂ) (Fin 0) c)) =
      c • a := by
  ext u
  simp [covectorWedgeForm, ContinuousAlternatingMap.alternatizeUncurryFin_apply, mul_comm]

set_option backward.isDefEq.respectTransparency false in
theorem spec_constantsToHolomorphicDeRham_comp_wedgeTheta_value_aux (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] (θ : GlobalHolomorphicForm X 1)
    (L : Ω•(X) ⟶ Ω•(X)⟦(1 : ℤ)⟧) (hL : IsWedgeThetaHom X θ L) (c : ℂ) (x : ComplexPoint X) :
    globalOneFormCovector X (dim X.left)
        (((constantCoefficientXZeroIso X ℂ).inv ≫
            (constantsToHolomorphicDeRhamComplexInt X ≫ L).f ((0 : ℕ) : ℤ) ≫
              (wedgeThetaShiftXIso X 0).hom).hom.app (op ⊤)
          (constantGlobalSection X ℂ c)) x =
      c • globalOneFormCovector X (dim X.left) θ x := by
  rw [rcaB_comp_zero]
  erw [ConcreteCategory.comp_apply, rcaB_constantGlobalSection]
  change (ContinuousAlternatingMap.ofSubsingleton ℂ _ ℂ (0 : Fin 1)).symm
    (formStalkValue X (dim X.left) x (0 + 1) ((holomorphicDeRhamSheaf X (dim X.left) (0 + 1)).presheaf.germ ⊤ x trivial
      ((wedgeThetaComponent X L 0).hom.app (op ⊤) _))) = _
  rw [hL 0 ⊤ x trivial, spec_formStalkValue_germ_toSheafify,
    chartEvaluation_ofConstant X (dim X.left) (op ⊤) x c
      (extChartAt_self_mem_chartSectionDomain X (dim X.left) (op ⊤) trivial),
    rcaB_ofSubsingleton_symm_covectorWedgeForm_const]

theorem rcaB_value_one (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    (θ : GlobalHolomorphicForm X 1)
    (L : Ω•(X) ⟶ Ω•(X)⟦(1 : ℤ)⟧) (hL : IsWedgeThetaHom X θ L) (x : ComplexPoint X) :
    globalOneFormCovector X (dim X.left)
        (((constantCoefficientXZeroIso X ℂ).inv ≫
            (constantsToHolomorphicDeRhamComplexInt X ≫ L).f ((0 : ℕ) : ℤ) ≫
              (wedgeThetaShiftXIso X 0).hom).hom.app (op ⊤)
          (constantGlobalSection X ℂ 1)) x =
      globalOneFormCovector X (dim X.left) θ x := by
  rw [spec_constantsToHolomorphicDeRham_comp_wedgeTheta_value_aux X θ L hL, one_smul]

set_option backward.isDefEq.respectTransparency false in
theorem rcaB_cycleDeRhamClass_eq (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    (z : (filteredGlobalSections X).cycles ((1 : ℕ) : ℤ)) :
    ∃ Z : CochainComplex.HomComplex.Cocycle
        (TopCat.Sheaf.integerConstantSingleComplex (TopCat.of (ComplexPoint X))) Ω•(X)
        ((1 : ℕ) : ℤ),
      cycleDeRhamClass X z =
        cohomologyClassToHypercohomology X Ω•(X) ((1 : ℕ) : ℤ)
          (CochainComplex.HomComplex.CohomologyClass.mk Z) ∧
      (TopCat.Sheaf.homComplexSingleIntegerIsoGlobalSections (TopCat.of (ComplexPoint X))
          Ω•(X)).hom.f ((1 : ℕ) : ℤ) Z.1 =
        ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
          (TopCat.of (ComplexPoint X))).map
            ((hodgeFilteredDeRhamInclusion X 1).f ((1 : ℕ) : ℤ))).hom
          ((filteredGlobalSections X).iCycles ((1 : ℕ) : ℤ) z) := by
  let Y := TopCat.of (ComplexPoint X)
  let G := (TopCat.Sheaf.homComplexSingleIntegerIsoGlobalSections Y Ω•(X))
  change ∃ Z, filteredToDeRhamCohomology X 1 ((1 : ℕ) : ℤ)
      (globalSectionsToHypercohomology X (F^1 Ω•(X)) ((1 : ℕ) : ℤ)
        ((filteredGlobalSections X).homologyπ ((1 : ℕ) : ℤ) z)) = _ ∧ _
  rw [filteredToDeRhamCohomology, ← globalSectionsToHypercohomology_naturality]
  erw [addCommGrp_homologyMap_homologyπ_apply]
  set w := HomologicalComplex.cyclesMap (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
            Y).mapHomologicalComplex ℤᵘᵖ).map (hodgeFilteredDeRhamInclusion X 1)) _ z with hw
  obtain ⟨Z, hZ, hZ1⟩ := cupLeft_homologyAddEquiv_homologyπ _ Ω•(X) ((1 : ℕ) : ℤ)
    (HomologicalComplex.cyclesMap G.inv _ w)
  refine ⟨Z, ?_, ?_⟩
  · change cohomologyClassToHypercohomology X Ω•(X) _
      (CochainComplex.HomComplex.homologyAddEquiv _ Ω•(X) _
        (HomologicalComplex.homologyMap G.inv _ ((TopCat.Sheaf.globalSectionsComplexInt Y Ω•(X)).homologyπ _ w))) = _
    rw [addCommGrp_homologyMap_homologyπ_apply, hZ]
  · rw [hZ1, addCommGrp_iCycles_cyclesMap_apply, ← ConcreteCategory.comp_apply,
      ← HomologicalComplex.comp_f, Iso.inv_hom_id, HomologicalComplex.id_f,
      ConcreteCategory.id_apply, hw]
    erw [addCommGrp_iCycles_cyclesMap_apply]
    rfl

theorem rcaB_equivHomShift_symm_ofHom {C : Type*} [Category* C] [Preadditive C]
    {K L : CochainComplex C ℤ} (φ : K ⟶ L) :
    CochainComplex.HomComplex.Cocycle.equivHomShift.symm
        (CochainComplex.HomComplex.Cocycle.ofHom φ) = ShiftedHom.mk₀ (0 : ℤ) rfl φ := by
  apply CochainComplex.HomComplex.Cocycle.equivHomShift.injective
  rw [AddEquiv.apply_symm_apply]
  ext p
  simp [CochainComplex.HomComplex.Cocycle.equivHomShift_apply, ShiftedHom.mk₀,
    CochainComplex.HomComplex.Cochain.rightUnshift_v _ _ _ _ _ _ _ (add_zero p),
    CochainComplex.HomComplex.Cochain.comp_v _ _ (add_zero 0) p p p (add_zero p) (add_zero p),
    CategoryTheory.shiftFunctorZero', CochainComplex.shiftFunctorZero_inv_app_f]

theorem rcaB_mk₀_eq_cohomologyClassToHypercohomology (X : Over (Spec ↧ℂ))
    {S : CochainComplex (AnalyticAdditiveSheaf X) ℤ} (f : constantIntegerSheafComplexInt X ⟶ S) :
    Localization.SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) (0 : ℤ) rfl f =
      cohomologyClassToHypercohomology X S 0
        (CochainComplex.HomComplex.CohomologyClass.mk (CochainComplex.HomComplex.Cocycle.ofHom
          ((constantIntegerSheafComplexIntIsoSingle X).inv ≫ f))) := by
  apply (Localization.SmallShiftedHom.equiv _ DerivedCategory.Q).injective
  dsimp only [cohomologyClassToHypercohomology, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [Localization.SmallShiftedHom.equiv_comp,
    CochainComplex.HomComplex.CohomologyClass.equiv_toSmallShiftedHom_mk,
    rcaB_equivHomShift_symm_ofHom, ShiftedHom.map_mk₀, Localization.SmallShiftedHom.equiv_mk₀,
    Localization.SmallShiftedHom.equiv_mk₀, ShiftedHom.mk₀_comp_mk₀, ← Functor.map_comp,
    Iso.hom_inv_id_assoc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
theorem rcaB_unit_f_zero (X : Over (Spec ↧ℂ)) :
    (constantIntegerSheafComplexIntIsoSingle X).inv.f 0 ≫
        (constantsIntToCoefficient X ℂ).f 0 ≫ (constantCoefficientXZeroIso X ℂ).hom =
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 𝓒(↧(ComplexPoint X); ℤ)).hom ≫
        (TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).map
          (AddCommGrpCat.ofHom (Int.castAddHom ℂ)) := by
  simp [constantIntegerSheafComplexIntIsoSingle, constantsIntToCoefficient,
    constantCoefficientXZeroIso]
  rw [HomologicalComplex.extendMap_f _ ComplexShape.embeddingUpNat (i := 0) (i' := 0) rfl,
    HomologicalComplex.extendSingleIso_inv_f _ _ (i := 0) (i' := 0) rfl]
  simp

theorem rcaB_N (X : Over (Spec ↧ℂ)) :
    TopCat.Sheaf.integerConstantHomAddEquivGlobalSections 𝓒(↧(ComplexPoint X); ℂ)
        ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).map
          (AddCommGrpCat.ofHom (Int.castAddHom ℂ))) =
      constantGlobalSection X ℂ 1 := by
  have h1 : TopCat.Sheaf.integerConstantHomAddEquivGlobalSections _
      (𝟙 ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj (AddCommGrpCat.of ℤ))) =
      constantGlobalSection X ℤ 1 := by
    rfl
  change ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).map
      (AddCommGrpCat.ofHom (Int.castAddHom ℂ))).hom.app (op ⊤)
    (TopCat.Sheaf.integerConstantHomAddEquivGlobalSections _
      (𝟙 ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj (AddCommGrpCat.of ℤ)))) = _
  rw [h1]
  have h2 := congrArg (fun f => (f.app (op ⊤)).hom (1 : ℤ)) (toSheafify_naturality
    (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
    ((Functor.const _).map (AddCommGrpCat.ofHom (Int.castAddHom ℂ))))
  simp only [NatTrans.comp_app] at h2
  refine h2.symm.trans ?_
  change constantGlobalSection X ℂ ((Int.castAddHom ℂ) 1) = _
  rw [Int.coe_castAddHom]
  exact congrArg _ Int.cast_one

theorem rcaB_globalOneForm_ext (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    (s t : GlobalHolomorphicForm X 1)
    (h : ∀ x, globalOneFormCovector X (dim X.left) s x = globalOneFormCovector X (dim X.left) t x) :
    s = t := by
  refine laneB_section_eq X (dim X.left) 1 ⊤ s t fun y _ => ?_
  exact (ContinuousAlternatingMap.ofSubsingleton ℂ _ ℂ (0 : Fin 1)).symm.injective (h y)

theorem rcaB_fromSingleEquiv_ofHom {C : Type*} [Category* C] [Preadditive C]
    [Limits.HasZeroObject C] {A : C} {K : CochainComplex C ℤ}
    (ψ : (CochainComplex.singleFunctor C 0).obj A ⟶ K) :
    CochainComplex.HomComplex.Cochain.fromSingleEquiv (zero_add 0)
        (CochainComplex.HomComplex.Cocycle.ofHom ψ).1 =
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 A).inv ≫ ψ.f 0 := by
  simp [CochainComplex.HomComplex.Cochain.fromSingleEquiv]

set_option backward.isDefEq.respectTransparency false in
theorem rcaB_unit_section_comp (X : Over (Spec ↧ℂ)) (F : TopCat.Sheaf AddCommGrpCat
      (TopCat.of (ComplexPoint X)))
    (g : (constantCoefficientSheafComplexInt X ℂ).X 0 ⟶ F) :
    TopCat.Sheaf.integerConstantHomAddEquivGlobalSections F
        ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 𝓒(↧(ComplexPoint X); ℤ)).inv ≫
          (constantIntegerSheafComplexIntIsoSingle X).inv.f 0 ≫
          (constantsIntToCoefficient X ℂ).f 0 ≫ g) =
      ((constantCoefficientXZeroIso X ℂ).inv ≫ g).hom.app (op ⊤) (constantGlobalSection X ℂ 1) := by
  have e : (HomologicalComplex.singleObjXSelf (.up ℤ) 0 𝓒(↧(ComplexPoint X); ℤ)).inv ≫
      (constantIntegerSheafComplexIntIsoSingle X).inv.f 0 ≫
      (constantsIntToCoefficient X ℂ).f 0 ≫ g =
      (TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).map
          (AddCommGrpCat.ofHom (Int.castAddHom ℂ)) ≫ ((constantCoefficientXZeroIso X ℂ).inv ≫ g) := by
    have h := rcaB_unit_f_zero X
    rw [← Iso.inv_comp_eq] at h
    rw [← h]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [e, ← rcaB_N]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem spec_constantsToHolomorphicDeRham_comp_wedgeTheta_aux (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] (z : (filteredGlobalSections X).cycles ((1 : ℕ) : ℤ))
    (L : Ω•(X) ⟶ Ω•(X)⟦(1 : ℤ)⟧) (hL : IsWedgeThetaHom X (cycleOneForm X z) L) :
    (Localization.SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) (0 : ℤ) rfl
        (constantsIntToCoefficient X ℂ ≫ constantsToHolomorphicDeRhamComplexInt X)).comp
      (Localization.SmallShiftedHom.mk (analyticQuasiIsomorphisms X)
        (show ShiftedHom Ω•(X) Ω•(X) (1 : ℤ) from L))
      (show (1 : ℤ) + 0 = ((1 : ℕ) : ℤ) by norm_num) =
      cycleDeRhamClass X z := by
  obtain ⟨Z, hZ, hZs⟩ := rcaB_cycleDeRhamClass_eq X z
  rw [hZ, rcaB_mk₀_eq_cohomologyClassToHypercohomology, cupLeft_cohomologyClassToHypercohomology_comp]
  congr 2
  apply CochainComplex.HomComplex.Cocycle.ext
  apply (AddCommGrpCat.mono_iff_injective
    ((TopCat.Sheaf.homComplexSingleIntegerIsoGlobalSections (TopCat.of (ComplexPoint X))
      Ω•(X)).hom.f ((1 : ℕ) : ℤ))).1 inferInstance
  rw [cupLeft_homComplexSingleIntegerIsoGlobalSections_equivHomShift_comp, hZs,
    cupLeft_homComplexSingleIntegerIsoGlobalSections_hom_f]
  rw [rcaB_fromSingleEquiv_ofHom]
  let E := (holomorphicDeRhamComplex X (dim X.left)).extendXIso ComplexShape.embeddingUpNat
    (i := 1) (i' := ((1 : ℕ) : ℤ)) rfl
  let Γ := TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
    (TopCat.of (ComplexPoint X))
  apply (AddCommGrpCat.mono_iff_injective (Γ.map E.hom)).1 inferInstance
  change TopCat.Sheaf.integerConstantHomAddEquivGlobalSections _
      ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 𝓒(↧(ComplexPoint X); ℤ)).inv ≫
        ((constantIntegerSheafComplexIntIsoSingle X).inv ≫ constantsIntToCoefficient X ℂ ≫
          constantsToHolomorphicDeRhamComplexInt X).f 0 ≫
        (L.f 0 ≫ (Ω•(X).XIsoOfEq (show (0 : ℤ) + 1 = ((1 : ℕ) : ℤ) by norm_num)).hom) ≫ E.hom) = _
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
  simp only [Category.assoc]
  rw [rcaB_unit_section_comp]
  have ha : (Ω•(X).XIsoOfEq (show (0 : ℤ) + 1 = ((1 : ℕ) : ℤ) by norm_num)).hom ≫ E.hom =
      (wedgeThetaShiftXIso X 0).hom := by
    simp [wedgeThetaShiftXIso, E, CochainComplex.shiftFunctorObjXIso]
  rw [ha]
  have hr : (Γ.map E.hom).hom ((Γ.map ((hodgeFilteredDeRhamInclusion X 1).f ((1 : ℕ) : ℤ))).hom
      ((filteredGlobalSections X).iCycles ((1 : ℕ) : ℤ) z)) = cycleOneForm X z := by
    rw [hodgeFilteredDeRhamInclusion_f_one, Functor.map_comp]
    change (Γ.map E.inv ≫ Γ.map E.hom).hom ((Γ.map (filteredDeRhamXOneIso X).hom).hom
      ((filteredGlobalSections X).iCycles ((1 : ℕ) : ℤ) z)) = _
    rw [← Functor.map_comp, Iso.inv_hom_id]
    erw [CategoryTheory.Functor.map_id]
    rfl
  refine Eq.trans ?_ hr.symm
  refine rcaB_globalOneForm_ext X _ (cycleOneForm X z) fun x => ?_
  have h7 := rcaB_value_one X (cycleOneForm X z) L hL x
  refine Eq.trans ?_ h7
  simp only [HomologicalComplex.comp_f, Category.assoc]
  rfl

theorem spec_hypercohomologyMap_resolutionClass_wedgeTheta_aux (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] (z : (filteredGlobalSections X).cycles ((1 : ℕ) : ℤ))
    (L : Ω•(X) ⟶ Ω•(X)⟦(1 : ℤ)⟧) (hL : IsWedgeThetaHom X (cycleOneForm X z) L) :
    hypercohomologyMap X (constantsToHolomorphicDeRhamComplexInt X) ((1 : ℕ) : ℤ)
        ((Localization.SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) (0 : ℤ) rfl
            (constantsIntToCoefficient X ℂ)).comp
          (resolutionClass X (constantsToHolomorphicDeRhamComplexInt X)
            (constantsToHolomorphicDeRham_mem X) L)
          (show (1 : ℤ) + 0 = ((1 : ℕ) : ℤ) by norm_num)) =
      cycleDeRhamClass X z := by
  refine (spec_hypercohomologyMap_comp_resolutionClass_aux X
    (constantsToHolomorphicDeRhamComplexInt X) (constantsToHolomorphicDeRham_mem X) L
    (show (1 : ℤ) + 0 = ((1 : ℕ) : ℤ) by norm_num)
    (Localization.SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) (0 : ℤ) rfl
      (constantsIntToCoefficient X ℂ))).trans ?_
  change ((Localization.SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) (0 : ℤ) rfl
      (constantsIntToCoefficient X ℂ)).comp
        (Localization.SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) (0 : ℤ) rfl
          (constantsToHolomorphicDeRhamComplexInt X)) (zero_add 0)).comp _ _ = _
  refine Eq.trans ?_ (spec_constantsToHolomorphicDeRham_comp_wedgeTheta_aux X z L hL)
  congr 1
  exact (smallShiftedHomMkZero_comp X (constantsIntToCoefficient X ℂ)
    (constantsToHolomorphicDeRhamComplexInt X)).symm

/-- On an open `U`, the zero-chain augmentation, read as a `0`-cochain, is the unit cochain. -/
theorem resolutionClass_openZeroAugmentation_eq_unitCochain {K : Type} [CommRing K]
    {Y : TopCat.{0}} (U : (Opens Y)ᵒᵖ) :
    ((AlgebraicTopology.Singular.openZeroAugmentation K Y U).hom :
        AlgebraicTopology.Singular.OpenCochains K Y U 0) =
      HodgeLean.Foundations.Singular.unitCochain ((Opens.toTopCat Y).obj U.unop) :=
  cupLeft_cochain_ext _ _ fun σ => by
    rw [HodgeLean.Foundations.Singular.unitCochain_apply_simplex, chainOfSimplex]
    change ((TopCat.toSSet.obj ((Opens.toTopCat Y).obj U.unop)).ιChainComplex σ ≫
      AlgebraicTopology.Singular.simplicialZeroAugmentation K _).hom 1 = 1
    rw [AlgebraicTopology.Singular.ιChainComplex_comp_simplicialZeroAugmentation]
    rfl

theorem spec_cupLeftPresheafHom_constants_aux {K : Type} [CommRing K] {Y : TopCat.{0}}
    (a : Cochain K (TopCat.toSSet.obj Y) 1) (U : (Opens Y)ᵒᵖ) (r : K) :
    (cupLeftPresheafHom a 0).app U
        ((AlgebraicTopology.Singular.constantsToSingularCochainZero K Y).app U r) =
      (r • cupLeftRestrict a U : AlgebraicTopology.Singular.OpenCochains K Y U 1) := by
  change HodgeLean.Foundations.Singular.cupCochain _ 1 0 (cupLeftRestrict a U)
    (r • (AlgebraicTopology.Singular.openZeroAugmentation K Y U).hom) = _
  rw [resolutionClass_openZeroAugmentation_eq_unitCochain]
  exact (LinearMap.map_smul _ r _).trans
    (congrArg (r • ·) (HodgeLean.Foundations.Singular.cupCochain_one _ 1 _))

set_option backward.isDefEq.respectTransparency false in
/-- The degree-`0` cocycle of a morphism of complexes is that morphism as a shifted morphism. -/
theorem resolutionClassSingular_equivHomShift_symm_ofHom {C : Type*} [Category* C]
    [Preadditive C] {F L : CochainComplex C ℤ} (g : F ⟶ L) :
    CochainComplex.HomComplex.Cocycle.equivHomShift.symm
        (CochainComplex.HomComplex.Cocycle.ofHom g) = ShiftedHom.mk₀ (0 : ℤ) rfl g := by
  apply CochainComplex.HomComplex.Cocycle.equivHomShift.injective
  rw [AddEquiv.apply_symm_apply]
  ext p
  simp [CochainComplex.HomComplex.Cocycle.equivHomShift_apply, ShiftedHom.mk₀,
    CochainComplex.HomComplex.Cochain.rightUnshift_v _ _ _ _ _ _ _ (add_zero p),
    CochainComplex.HomComplex.Cochain.comp_v _ _ (add_zero 0) p p p (add_zero p) (add_zero p),
    CategoryTheory.shiftFunctorZero', CochainComplex.shiftFunctorZero_inv_app_f]

/-- The edge-map class of the cocycle of a morphism `g : ℤ[0] ⟶ S` is `mk₀` of `g`. -/
theorem resolutionClassSingular_cohomologyClassToHypercohomology_ofHom (X : Over (Spec ↧ℂ))
    (S : CochainComplex (AnalyticAdditiveSheaf X) ℤ)
    (g : TopCat.Sheaf.integerConstantSingleComplex (TopCat.of (ComplexPoint X)) ⟶ S) :
    cohomologyClassToHypercohomology X S 0
        (CochainComplex.HomComplex.CohomologyClass.mk
          (CochainComplex.HomComplex.Cocycle.ofHom g)) =
      Localization.SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) (0 : ℤ) rfl
        ((constantIntegerSheafComplexIntIsoSingle X).hom ≫ g) := by
  apply (Localization.SmallShiftedHom.equiv _ DerivedCategory.Q).injective
  dsimp only [cohomologyClassToHypercohomology, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [Localization.SmallShiftedHom.equiv_comp, Localization.SmallShiftedHom.equiv_mk₀,
    CochainComplex.HomComplex.CohomologyClass.equiv_toSmallShiftedHom_mk,
    resolutionClassSingular_equivHomShift_symm_ofHom, ShiftedHom.map_mk₀,
    Localization.SmallShiftedHom.equiv_mk₀, ShiftedHom.mk₀_comp_mk₀, Functor.map_comp]

/-- The global section attached to a morphism out of `ℤ_Y` is the image of the constant `1`. -/
theorem resolutionClassSingular_integerConstantHomAddEquivGlobalSections {Y : TopCat.{0}}
    (F : TopCat.Sheaf AddCommGrpCat Y)
    (φ : (TopCat.Sheaf.constantFunctor Y).obj (AddCommGrpCat.of ℤ) ⟶ F) :
    TopCat.Sheaf.integerConstantHomAddEquivGlobalSections F φ =
      φ.hom.app (op ⊤)
        (((toSheafify (Opens.grothendieckTopology Y) 𝓒ᵖ(Y; ℤ)).app (op ⊤)).hom (show ℤ from 1)) := by
  rfl
set_option backward.isDefEq.respectTransparency false in
/-- The degree-`0` component of `ℤ[0] ⟶ K[0] ⟶ S•` is `ℤ_X ⟶ K_X ⟶ S^0`. -/
theorem resolutionClassSingular_unit_f_zero (X : Over (Spec ↧ℂ)) (K : Type) [CommRing K] :
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj
          (AddCommGrpCat.of ℤ))).inv ≫
      ((constantIntegerSheafComplexIntIsoSingle X).inv ≫ constantsIntToCoefficient X K ≫
        constantsToSingularCochainComplexInt X K).f 0 =
    (TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).map
        (AddCommGrpCat.ofHom (Int.castAddHom K)) ≫
      AlgebraicTopology.Singular.constantsToSingularCochainZeroSheaf K
        (TopCat.of (ComplexPoint X)) ≫
      ((AlgebraicTopology.Singular.singularCochainSheafComplex K
        (TopCat.of (ComplexPoint X))).extendXIso ComplexShape.embeddingUpNat (i := 0) rfl).inv := by
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
  dsimp only [constantIntegerSheafComplexIntIsoSingle, constantsIntToCoefficient,
    constantsToSingularCochainComplexInt]
  erw [HomologicalComplex.extendSingleIso_inv_f _ _ _ _ rfl,
    HomologicalComplex.extendMap_f _ _ (i := 0) rfl,
    HomologicalComplex.extendMap_f _ _ (i := 0) rfl]
  simp only [Category.assoc, Iso.inv_hom_id_assoc,
    AlgebraicTopology.Singular.constantsToSingularCochainSheafComplex,
    CochainComplex.fromSingle₀Equiv_symm_apply_f_zero]
  exact Iso.inv_hom_id_assoc _ _

set_option backward.isDefEq.respectTransparency false in
/-- The degree-`0` cochain of a morphism out of a single complex. -/
theorem resolutionClassSingular_fromSingleEquiv_ofHom {C : Type*} [Category* C]
    [Preadditive C] [Limits.HasZeroObject C] {F : C} {L : CochainComplex C ℤ}
    (g : (CochainComplex.singleFunctor C 0).obj F ⟶ L) :
    CochainComplex.HomComplex.Cochain.fromSingleEquiv (zero_add 0)
        (CochainComplex.HomComplex.Cochain.ofHom g) =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).inv ≫ g.f 0 := by
  simp [CochainComplex.HomComplex.Cochain.fromSingleEquiv]

set_option backward.isDefEq.respectTransparency false in
/-- `ℤ_X ⟶ K_X ⟶ S^0` sends the constant `1` to the section represented by the unit cochain. -/
theorem resolutionClassSingular_constants_globalSection (X : Over (Spec ↧ℂ)) (K : Type)
    [CommRing K] :
    ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).map
        (AddCommGrpCat.ofHom (Int.castAddHom K)) ≫
      AlgebraicTopology.Singular.constantsToSingularCochainZeroSheaf K
        (TopCat.of (ComplexPoint X))).hom.app (op ⊤)
        (((toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
          𝓒ᵖ(TopCat.of (ComplexPoint X); ℤ)).app (op ⊤)).hom (show ℤ from 1)) =
      (AlgebraicTopology.Singular.topOpenToGlobalSingularCochainSheafComplex K
        (TopCat.of (ComplexPoint X))).f 0
        (cupLeftRestrict (HodgeLean.Foundations.Singular.unitCochain
          (TopCat.of (ComplexPoint X))) (op ⊤)) := by
  let Y := TopCat.of (ComplexPoint X)
  let η := (Functor.const (Opens Y)ᵒᵖ).map (AddCommGrpCat.ofHom (Int.castAddHom K)) ≫
    AlgebraicTopology.Singular.constantsToSingularCochainZero K Y
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (toSheafify_naturality (Opens.grothendieckTopology Y) η) (op ⊤))
    (show ℤ from 1)
  have hη : ((TopCat.Sheaf.constantFunctor Y).map (AddCommGrpCat.ofHom (Int.castAddHom K)) ≫
      AlgebraicTopology.Singular.constantsToSingularCochainZeroSheaf K Y).hom =
      sheafifyMap (Opens.grothendieckTopology Y) η := by
    rw [sheafifyMap_comp]
    rfl
  rw [hη, AlgebraicTopology.Singular.topOpenToGlobalSingularCochainSheafComplex_f]
  refine (NatTrans.comp_app_apply _ _ _ _).symm.trans (h.symm.trans ?_)
  refine (ConcreteCategory.comp_apply _ _ _).trans (congrArg _ ?_)
  change ((1 : ℤ) : K) • (AlgebraicTopology.Singular.openZeroAugmentation K Y (op ⊤)).hom = _
  rw [Int.cast_one, one_smul, resolutionClass_openZeroAugmentation_eq_unitCochain]
  exact (HodgeLean.Foundations.Simplicial.cochainMap_unitCochain _ _).symm

set_option backward.isDefEq.respectTransparency false in
/-- The unit class of singular cohomology is the class of `ℤ[0] ⟶ K[0] ⟶ S•`. -/
theorem resolutionClassSingular_singularToSheafHypercohomology_unit (X : Over (Spec ↧ℂ))
    (K : Type) [CommRing K] :
    singularToSheafHypercohomology X K 0
        (HodgeLean.Foundations.Singular.unit (TopCat.of (ComplexPoint X))) =
      Localization.SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) (0 : ℤ) rfl
        (constantsIntToCoefficient X K ≫ constantsToSingularCochainComplexInt X K) := by
  obtain ⟨z, hz, hzs⟩ := cupLeft_singularToSheafHypercohomology_cohomologyClass K X 0
    ⟨HodgeLean.Foundations.Singular.unitCochain _,
      HodgeLean.Foundations.Singular.coboundary_unitCochain _⟩
  have hzg : z = CochainComplex.HomComplex.Cocycle.ofHom
      ((constantIntegerSheafComplexIntIsoSingle X).inv ≫ constantsIntToCoefficient X K ≫
        constantsToSingularCochainComplexInt X K) := by
    apply CochainComplex.HomComplex.Cocycle.ext
    apply (AddCommGrpCat.mono_iff_injective
      ((TopCat.Sheaf.homComplexSingleIntegerIsoGlobalSections (TopCat.of (ComplexPoint X))
        (singularCochainSheafComplexInt X K)).hom.f ((0 : ℕ) : ℤ))).1 inferInstance
    rw [hzs, cupLeft_homComplexSingleIntegerIsoGlobalSections_hom_f,
      resolutionClassSingular_integerConstantHomAddEquivGlobalSections]
    erw [resolutionClassSingular_fromSingleEquiv_ofHom]
    rw [resolutionClassSingular_unit_f_zero,
      cupLeft_globalSectionsSingularCochainComplexIntIsoExtendField_inv_f]
    rw [← resolutionClassSingular_constants_globalSection]
    rfl
  change singularToSheafHypercohomology X K 0
    (HodgeLean.Foundations.Singular.cohomologyClass _ 0 _) = _
  rw [hz, hzg]
  exact (resolutionClassSingular_cohomologyClassToHypercohomology_ofHom X _ _).trans
    (by rw [Iso.hom_inv_id_assoc])


theorem spec_constantsToSingular_comp_cupLeft_aux (X : Over (Spec ↧ℂ)) (K : Type) [CommRing K]
    (a : Cocycle K (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) 1) :
    (Localization.SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) (0 : ℤ) rfl
        (constantsIntToCoefficient X K ≫ constantsToSingularCochainComplexInt X K)).comp
      (Localization.SmallShiftedHom.mk (analyticQuasiIsomorphisms X)
        (show ShiftedHom (singularCochainSheafComplexInt X K) (singularCochainSheafComplexInt X K)
          (1 : ℤ) from cupLeftComplexHom X a))
      (show (1 : ℤ) + 0 = ((1 : ℕ) : ℤ) by norm_num) =
      singularToSheafHypercohomology X K 1
        (HodgeLean.Foundations.Singular.cohomologyClass _ 1 a) := by
  rw [← resolutionClassSingular_singularToSheafHypercohomology_unit]
  have h4 := spec_cupLeftHypercohomology_singularToSheafHypercohomology K X a 0 (by norm_num)
    (HodgeLean.Foundations.Singular.unit _)
  have hc : HodgeLean.Foundations.Singular.cup (TopCat.of (ComplexPoint X)) (rfl : 1 + 0 = 1 + 0)
      (HodgeLean.Foundations.Singular.cohomologyClass _ 1 a)
      (HodgeLean.Foundations.Singular.unit (R := K) _) =
      HodgeLean.Foundations.Singular.cohomologyClass _ 1 a :=
    HodgeLean.Foundations.Singular.cup_one _ _
  rw [hc] at h4
  refine Eq.trans ?_ (h4.trans ?_)
  · rfl
  · with_reducible rfl


theorem spec_hypercohomologyMap_resolutionClass_cupLeft_aux (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] (K : Type) [CommRing K]
    (a : Cocycle K (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) 1) :
    hypercohomologyMap X (constantsToSingularCochainComplexInt X K) ((1 : ℕ) : ℤ)
        ((Localization.SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) (0 : ℤ) rfl
            (constantsIntToCoefficient X K)).comp
          (resolutionClass X (constantsToSingularCochainComplexInt X K)
            (constantsToSingularCochain_mem X K) (cupLeftComplexHom X a))
          (show (1 : ℤ) + 0 = ((1 : ℕ) : ℤ) by norm_num)) =
      singularToSheafHypercohomology X K 1
        (HodgeLean.Foundations.Singular.cohomologyClass _ 1 a) := by
  rw [spec_hypercohomologyMap_comp_resolutionClass_aux]
  change ((Localization.SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) (0 : ℤ) rfl
      (constantsIntToCoefficient X K)).comp
      (Localization.SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) (0 : ℤ) rfl
        (constantsToSingularCochainComplexInt X K)) (zero_add 0)).comp _ _ = _
  rw [← smallShiftedHomMkZero_comp]
  exact spec_constantsToSingular_comp_cupLeft_aux X K a

end HodgeLean.Adapters
