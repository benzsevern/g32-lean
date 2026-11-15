import HodgeLean.Adapters.HolomorphicPeriodsDeRhamDefs
import HodgeLean.Adapters.HolomorphicPeriodsComparison
import HodgeLean.Adapters.HolomorphicOneForms

/-! # Proof obligations for `HolomorphicPeriodsDeRham`

One `_aux` per statement of `HodgeLean.Adapters.HolomorphicPeriodsDeRham`, all open.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ComplexPoint TopologicalSpace Opposite
open HodgeLean.RealDefs HodgeLean.Foundations
open scoped Simplicial

namespace HodgeLean.Adapters

/-- A map `A[0] → [X₀ → X₁]` given by `a : A → X₀` is a quasi-isomorphism when `a` is mono,
`A → X₀ → X₁` is exact and `X₀ → X₁` is epi. -/
theorem quasiIso_fromSingle₀_double {C : Type*} [Category C] [Abelian C] {A X₀ X₁ : C}
    (f : X₀ ⟶ X₁) (a : A ⟶ X₀) (w : a ≫ f = 0) (hex : (ShortComplex.mk a f w).Exact) [Mono a]
    [Epi f] (hw) :
    QuasiIso ((CochainComplex.fromSingle₀Equiv
      (HomologicalComplex.double f (show (ComplexShape.up ℕ).Rel 0 1 from rfl)) A).symm
        ⟨a ≫ (HomologicalComplex.doubleXIso₀ f
          (show (ComplexShape.up ℕ).Rel 0 1 from rfl)).inv, hw⟩) := by
  refine ⟨fun n => ?_⟩
  rcases n with _ | _ | n
  · rw [CochainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros]
    · constructor
      · refine (ShortComplex.exact_iff_of_iso ?_).2 hex
        refine ShortComplex.isoMk (Iso.refl _)
          (HomologicalComplex.doubleXIso₀ f (show (ComplexShape.up ℕ).Rel 0 1 from rfl))
          (HomologicalComplex.doubleXIso₁ f (show (ComplexShape.up ℕ).Rel 0 1 from rfl)
            (by decide)) ?_ ?_
        · simp
        · simp [HomologicalComplex.double_d _ _ (show (0 : ℕ) ≠ 1 by decide)]
      · simp only [HomologicalComplex.shortComplexFunctor'_map_τ₂,
          CochainComplex.fromSingle₀Equiv_symm_apply_f_zero]
        exact mono_comp a _
    · rfl
    · rfl
    · exact HomologicalComplex.double_d_eq_zero₁ f
        (show (ComplexShape.up ℕ).Rel 0 1 from rfl) _ _ (by decide)
  · rw [quasiIsoAt_iff_exactAt _ _ (CochainComplex.exactAt_succ_single_obj _ 0),
      HomologicalComplex.exactAt_iff' _ 0 1 2 (by simp) (by simp),
      ShortComplex.exact_iff_epi _ (HomologicalComplex.double_d_eq_zero₀ f
        (show (ComplexShape.up ℕ).Rel 0 1 from rfl) _ _ (by decide))]
    change Epi ((HomologicalComplex.double f (show (ComplexShape.up ℕ).Rel 0 1 from rfl)).d 0 1)
    rw [HomologicalComplex.double_d _ _ (by decide)]
    infer_instance
  · rw [quasiIsoAt_iff_exactAt _ _ (CochainComplex.exactAt_succ_single_obj _ (n + 1)),
      HomologicalComplex.exactAt_iff]
    exact ShortComplex.exact_of_isZero_X₂ _
      (HomologicalComplex.isZero_double_X f (show (ComplexShape.up ℕ).Rel 0 1 from rfl) _
        (by omega) (by omega))

section Poincare

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]

/-- The Poincaré lemma in degree `0`: `ℂ → Ω^0` is mono and `ℂ → Ω^0 → Ω^1` is exact. -/
theorem constantsToHolomorphicDeRhamZeroSheaf_mono_and_exact :
    Mono (constantsToHolomorphicDeRhamZeroSheaf X (dim X.left)) ∧
      (ShortComplex.mk _ _
        (constantsToHolomorphicDeRhamZeroSheaf_comp_differential X (dim X.left))).Exact := by
  have h := constantsToHolomorphicDeRhamComplex_quasiIsoAt_zero X (dim X.left)
  rw [CochainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros] at h
  · exact ⟨h.2, h.1⟩
  all_goals rfl

/-- The Poincaré lemma in degree `1`: `Ω^0 → Ω^1 → Ω^2` is exact. -/
theorem holomorphicDeRhamSheafDifferential_exact_one :
    (ShortComplex.mk _ _ (holomorphicDeRhamSheafDifferential_zero_comp_one X)).Exact := by
  have h := constantsToHolomorphicDeRhamComplex_quasiIsoAt_succ X (dim X.left) 0
  rw [quasiIsoAt_iff_exactAt _ _ (CochainComplex.exactAt_succ_single_obj _ 0),
    HomologicalComplex.exactAt_iff' _ 0 1 2 (by simp) (by simp)] at h
  exact h

end Poincare

theorem spec_constantsToClosedFormComplex_quasiIso_aux (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] :
    QuasiIso (constantsToClosedFormComplex X) := by
  obtain ⟨_, h0⟩ := constantsToHolomorphicDeRhamZeroSheaf_mono_and_exact X
  have : Epi (closedOneFormDifferential X) :=
    (holomorphicDeRhamSheafDifferential_exact_one X).epi_kernelLift
  have hex : (ShortComplex.mk _ _
      (constantsToHolomorphicDeRhamZeroSheaf_comp_closedOneFormDifferential X)).Exact := by
    let φ : ShortComplex.mk _ _
          (constantsToHolomorphicDeRhamZeroSheaf_comp_closedOneFormDifferential X) ⟶
        ShortComplex.mk _ _
          (constantsToHolomorphicDeRhamZeroSheaf_comp_differential X (dim X.left)) :=
      ShortComplex.homMk (𝟙 _) (𝟙 _) (kernel.ι _) (by simp)
        (by simp [closedOneFormDifferential])
    have : Epi φ.τ₁ := inferInstanceAs (Epi (𝟙 _))
    have : IsIso φ.τ₂ := inferInstanceAs (IsIso (𝟙 _))
    have : Mono φ.τ₃ := inferInstanceAs (Mono (kernel.ι _))
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2 h0
  exact (HomologicalComplex.quasiIso_extendMap_iff _ _).2
    (quasiIso_fromSingle₀_double _ _ _ hex _)

theorem spec_constantsToClosedFormComplex_comp_toDeRham_aux (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] :
    constantsToClosedFormComplex X ≫ closedFormComplexToDeRham X =
      constantsToHolomorphicDeRhamComplexInt X := by
  refine (HomologicalComplex.extendMap_comp ..).symm.trans
    (congrArg (HomologicalComplex.extendMap · _) ?_)
  apply HomologicalComplex.from_single_hom_ext
  change (constantsToHolomorphicDeRhamZeroSheaf X (dim X.left) ≫
      (HomologicalComplex.doubleXIso₀ _ _).inv) ≫ (closedFormComplexNatToDeRham X).f 0 =
    constantsToHolomorphicDeRhamZeroSheaf X (dim X.left)
  rw [closedFormComplexNatToDeRham]
  erw [HomologicalComplex.mkHomFromDouble_f₀]
  rw [Category.assoc]
  erw [Iso.inv_hom_id_assoc]
  exact Category.comp_id _

theorem spec_closedFormComplexToDeRham_quasiIso_aux (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] :
    QuasiIso (closedFormComplexToDeRham X) := by
  have := spec_constantsToClosedFormComplex_quasiIso_aux X
  have : QuasiIso (constantsToClosedFormComplex X ≫ closedFormComplexToDeRham X) := by
    rw [spec_constantsToClosedFormComplex_comp_toDeRham_aux]
    infer_instance
  exact quasiIso_of_comp_left (constantsToClosedFormComplex X) _

theorem spec_primitiveQuotientToClosedOneForm_isIso_aux (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] :
    IsIso (primitiveQuotientToClosedOneForm X) := by
  obtain ⟨_, h0⟩ := constantsToHolomorphicDeRhamZeroSheaf_mono_and_exact X
  have h1 := holomorphicDeRhamSheafDifferential_exact_one X
  have hm : Mono (primitiveQuotientToClosedOneForm X) := by
    have := h0.mono_cokernelDesc
    have e : primitiveQuotientToClosedOneForm X ≫ kernel.ι _ = cokernel.desc _ _
        (constantsToHolomorphicDeRhamZeroSheaf_comp_differential X (dim X.left)) := by
      ext
      simp [primitiveQuotientToClosedOneForm, closedOneFormDifferential]
    exact mono_of_mono_fac e
  have he : Epi (primitiveQuotientToClosedOneForm X) := by
    have : Epi (closedOneFormDifferential X) := h1.epi_kernelLift
    exact epi_of_epi_fac (cokernel.π_desc _ _ _)
  exact isIso_of_mono_of_epi _

theorem spec_constantsToPrimitiveComplex_comp_aux (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] :
    constantsToPrimitiveComplex X ≫ primitiveComplexToClosedFormComplex X =
      constantsToClosedFormComplex X := by
  refine (HomologicalComplex.extendMap_comp ..).symm.trans
    (congrArg (HomologicalComplex.extendMap · _) ?_)
  apply HomologicalComplex.from_single_hom_ext
  change (constantsToHolomorphicDeRhamZeroSheaf X (dim X.left) ≫
      (HomologicalComplex.doubleXIso₀ _ _).inv) ≫
        (primitiveComplexNatToClosedFormComplexNat X).f 0 =
    constantsToHolomorphicDeRhamZeroSheaf X (dim X.left) ≫ (HomologicalComplex.doubleXIso₀ _ _).inv
  rw [primitiveComplexNatToClosedFormComplexNat, HomologicalComplex.mkHomFromDouble_f₀,
    Category.assoc, Iso.inv_hom_id_assoc]

theorem spec_constantsToPrimitiveComplex_quasiIso_aux (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] :
    QuasiIso (constantsToPrimitiveComplex X) := by
  have := (constantsToHolomorphicDeRhamZeroSheaf_mono_and_exact X).1
  exact (HomologicalComplex.quasiIso_extendMap_iff _ _).2
    (quasiIso_fromSingle₀_double
      (cokernel.π (constantsToHolomorphicDeRhamZeroSheaf X (dim X.left)))
      (constantsToHolomorphicDeRhamZeroSheaf X (dim X.left)) (cokernel.condition _)
      (ShortComplex.exact_of_g_is_cokernel _
        (cokernelIsCokernel (constantsToHolomorphicDeRhamZeroSheaf X (dim X.left)))) _)

theorem spec_constantsToPrimitiveComplex_comp_toSingular_aux (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] :
    constantsToPrimitiveComplex X ≫ primitiveComplexToSingular X =
      constantsToSingularCochainComplexInt X ℂ := by
  refine (HomologicalComplex.extendMap_comp ..).symm.trans
    (congrArg (HomologicalComplex.extendMap · _) ?_)
  apply HomologicalComplex.from_single_hom_ext
  change (constantsToHolomorphicDeRhamZeroSheaf X (dim X.left) ≫
      (HomologicalComplex.doubleXIso₀ _ _).inv) ≫ (primitiveComplexNatToSingular X).f 0 =
    AlgebraicTopology.Singular.constantsToSingularCochainZeroSheaf ℂ _
  rw [primitiveComplexNatToSingular]
  erw [HomologicalComplex.mkHomFromDouble_f₀]
  rw [Category.assoc]
  erw [Iso.inv_hom_id_assoc]
  exact constantsToHolomorphicDeRhamZeroSheaf_comp_functionValueSheafMap X

theorem spec_exists_globalPrimitive_of_closed_aux (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] (θ : GlobalHolomorphicForm X 1)
    (hθ : globalHolomorphicDifferential X 1 θ = 0) :
    ∃ θ' : (TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
        (TopCat.of (ComplexPoint X))).obj (primitiveQuotientSheaf X),
      ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
          (TopCat.of (ComplexPoint X))).map
        (primitiveQuotientToClosedOneForm X ≫ kernel.ι _)).hom θ' = θ := by
  let Γ := TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
    (TopCat.of (ComplexPoint X))
  have hS : (ShortComplex.mk (kernel.ι (holomorphicDeRhamSheafDifferential X (dim X.left) 1)) _
      (kernel.condition _)).Exact :=
    ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _)
  have hΓ := hS.map_of_mono_of_preservesKernel Γ (inferInstanceAs (Mono (kernel.ι _)))
    inferInstance
  rw [ShortComplex.ab_exact_iff] at hΓ
  obtain ⟨κ, hκ⟩ := hΓ θ hθ
  have := spec_primitiveQuotientToClosedOneForm_isIso_aux X
  refine ⟨(Γ.map (inv (primitiveQuotientToClosedOneForm X))).hom κ, ?_⟩
  rw [← hκ, ← ConcreteCategory.comp_apply, ← Functor.map_comp, IsIso.inv_hom_id_assoc]
  rfl

theorem spec_globalCochainSection_eq_toSheafify_aux (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] (n : ℕ)
    (φ : AlgebraicTopology.Simplicial.Cochain ℂ
      (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) n) :
    globalCochainSection X n φ =
      ((toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
        (AlgebraicTopology.Singular.singularCochainPresheaf ℂ (TopCat.of (ComplexPoint X)) n)).app
          (op ⊤)).hom
        (((AlgebraicTopology.Singular.singularCochainComplexIsoTopOpen ℂ
          (TopCat.of (ComplexPoint X))).hom.f n).hom φ) := by
  change ((AlgebraicTopology.Singular.topOpenToGlobalSingularCochainSheafComplex ℂ
    (TopCat.of (ComplexPoint X))).f n).hom _ = _
  rw [AlgebraicTopology.Singular.topOpenToGlobalSingularCochainSheafComplex_f]
  rfl

section LaneB
open scoped Manifold

/-- The chart evaluation of a holomorphic `0`-form does not depend on the chart: two charts reading
the same point give the same value. -/
theorem chartEvaluation_zero_eq_of_symm_eq (X : Over (Spec ↧ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (θ : Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d U) 0) {z₁ z₂ : ComplexPoint X}
    {y₁ y₂ : Fin d → ℂ} (h₁ : y₁ ∈ chartSectionDomain X d U z₁)
    (h₂ : y₂ ∈ chartSectionDomain X d U z₂)
    (h : (extChartAt 𝓘(ℂ, Fin d → ℂ) z₁).symm y₁ = (extChartAt 𝓘(ℂ, Fin d → ℂ) z₂).symm y₂) :
    chartEvaluation X d U z₁ 0 θ y₁ = chartEvaluation X d U z₂ 0 θ y₂ := by
  induction θ using Algebra.DeRham.mk_induction with
  | mk a₀ v =>
    rw [chartEvaluation_mk X d U z₁ 0 a₀ v h₁, chartEvaluation_mk X d U z₂ 0 a₀ v h₂]
    simp only [chartGeneratorEvaluation, chartSection_apply_of_mem X d U _ _ h₁,
      chartSection_apply_of_mem X d U _ _ h₂, ContinuousAlternatingMap.wedgeCovectors_zero]
    exact congrArg (· • _) (congrArg _ (Subtype.ext h))
  | zero => simp
  | add a b ha hb => simp [ha, hb]
  | smul c a ha => simp [ha]

/-- In a fixed chart, the coordinate expression of a holomorphic `0`-form has derivative the chart
evaluation of its exterior derivative. -/
theorem hasFDerivAt_chartEvaluation_zero (X : Over (Spec ↧ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (z : ComplexPoint X) (θ : Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d U) 0)
    {y : Fin d → ℂ} (hy : y ∈ chartSectionDomain X d U z) :
    HasFDerivAt (fun w ↦ chartEvaluation X d U z 0 θ w 0)
      ((ContinuousAlternatingMap.ofSubsingleton ℂ (Fin d → ℂ) ℂ (0 : Fin 1)).symm
        (chartEvaluation X d U z 1 (Algebra.DeRham.differential ℂ _ 0 θ) y)) y := by
  set η := chartEvaluation X d U z 0 θ with hη
  have hopen := isOpen_chartSectionDomain X d U z
  have hdiff : DifferentiableAt ℂ η y :=
    (analyticOnNhd_chartEvaluation X d U z 0 θ y hy).differentiableAt
  have hf : DifferentiableAt ℂ (fun w ↦ η w 0) y := hdiff.continuousAlternatingMap_apply_const 0
  have hrepr := DifferentialForm.zeroForm_eq_constOfIsEmpty η
  have hd : chartEvaluation X d U z 1 (Algebra.DeRham.differential ℂ _ 0 θ) y =
      ContinuousAlternatingMap.ofSubsingleton ℂ (Fin d → ℂ) ℂ (0 : Fin 1)
        (fderiv ℂ (fun w ↦ η w 0) y) := by
    rw [chartEvaluation_differential X d U z 0 θ hy]
    rw [extDerivWithin, fderivWithin_of_isOpen hopen hy, ← extDeriv]
    have h2 : extDeriv η y = ContinuousAlternatingMap.ofSubsingleton ℂ (Fin d → ℂ) ℂ (0 : Fin 1)
        (fderiv ℂ (DifferentialForm.zeroFormCoeff η) y) := by
      conv_lhs => rw [hrepr]
      exact extDeriv_constOfIsEmpty _ _
    exact h2
  rw [hd]
  convert hf.hasFDerivAt using 1
  exact (ContinuousAlternatingMap.ofSubsingleton ℂ (Fin d → ℂ) ℂ (0 : Fin 1)).symm_apply_apply _


/-- The value of a holomorphic function `F` on `W` at a point `y`, read in the chart at `y`
(an auxiliary total function on `X(ℂ)`).
Source: Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 0 §2; upstream
`chartEvaluation`. -/
def functionValueAux (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (W : Opens (TopCat.of (ComplexPoint X)))
    (F : Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d (op W)) 0) (y : ComplexPoint X) : ℂ :=
  chartEvaluation X d (op W) y 0 F (extChartAt 𝓘(ℂ, Fin d → ℂ) y y) 0

example (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (W : Opens (TopCat.of (ComplexPoint X))) (y : ComplexPoint X) :
    functionValueAux X d W 0 y = 0 := by
  simp [functionValueAux]

/-- `functionValueAux` read through any chart whose domain contains the point. -/
theorem functionValueAux_eq (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (W : Opens (TopCat.of (ComplexPoint X)))
    (F : Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d (op W)) 0) (z : ComplexPoint X)
    {w : Fin d → ℂ} (hw : w ∈ chartSectionDomain X d (op W) z) :
    functionValueAux X d W F ((extChartAt 𝓘(ℂ, Fin d → ℂ) z).symm w) =
      chartEvaluation X d (op W) z 0 F w 0 := by
  unfold functionValueAux
  rw [chartEvaluation_zero_eq_of_symm_eq X d (op W) F
    (extChartAt_self_mem_chartSectionDomain X d (op W) (x := (extChartAt 𝓘(ℂ, Fin d → ℂ) z).symm w)
      hw.2) hw (extChartAt_to_inv _)]

open scoped CategoryTheory.MonObj in
/-- If a global `1`-form `θ` is `dF` on `W`, then `F ∘ exp` has derivative `exp^*θ` at every point
of `exp⁻¹ W`. -/
theorem hasFDerivAt_functionValueAux_comp_exp (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X]
    [IsCommMonObj X] [SmoothOfRelativeDimension d X.hom]
    (θ : (holomorphicDeRhamSheaf X d 1).presheaf.obj (op ⊤))
    (W : Opens (TopCat.of (ComplexPoint X)))
    (F : Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d (op W)) 0)
    (hF : (holomorphicDeRhamSheaf X d 1).presheaf.map (homOfLE le_top).op θ =
      (toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
        (holomorphicDeRhamPresheaf X d 1)).app (op W)
          (Submodule.Quotient.mk (Algebra.DeRham.differential ℂ _ 0 F)))
    (v : Fin d → ℂ) (hv : (complexExponential X d v).toMul ∈ W) :
    HasFDerivAt (fun u ↦ functionValueAux X d W F (complexExponential X d u).toMul)
      (expPullback X d θ v) v := by
  set y₀ := (complexExponential X d v).toMul with hy₀
  set e := extChartAt 𝓘(ℂ, Fin d → ℂ) y₀ with he
  have hE : Continuous (fun u ↦ (complexExponential X d u).toMul) :=
    (spec_mdifferentiable_complexExponential X d).continuous
  have hφd : DifferentiableAt ℂ (fun u ↦ e (complexExponential X d u).toMul) v := by
    have h := (spec_mdifferentiable_complexExponential X d v).differentiableWithinAt_writtenInExtChartAt
    simp only [ModelWithCorners.range_eq_univ, differentiableWithinAt_univ] at h
    exact h
  have hφ : fderiv ℂ (fun u ↦ e (complexExponential X d u).toMul) v =
      mfderiv 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) (fun u ↦ (complexExponential X d u).toMul) v :=
    (mfderiv_complexExponential_eq_fderiv X d v).symm
  have hy₀D : e y₀ ∈ chartSectionDomain X d (op W) y₀ :=
    extChartAt_self_mem_chartSectionDomain X d (op W) hv
  have hL := hasFDerivAt_chartEvaluation_zero X d (op W) y₀ F hy₀D
  have hcov : (ContinuousAlternatingMap.ofSubsingleton ℂ (Fin d → ℂ) ℂ (0 : Fin 1)).symm
      (chartEvaluation X d (op W) y₀ 1 (Algebra.DeRham.differential ℂ _ 0 F) (e y₀)) =
      globalOneFormCovector X d θ y₀ := by
    rw [globalOneFormCovector, globalFormValue_eq_chartEvaluation_self X d 1 θ W _ hF y₀ hv]
  rw [hcov] at hL
  have hcomp := hL.comp v (hφd.hasFDerivAt)
  rw [hφ] at hcomp
  refine hcomp.congr_of_eventuallyEq ?_
  have hopen : IsOpen ((fun u ↦ (complexExponential X d u).toMul) ⁻¹' (e.source ∩ W)) :=
    ((isOpen_extChartAt_source y₀).inter W.isOpen).preimage hE
  filter_upwards [hopen.mem_nhds ⟨mem_extChartAt_source y₀, hv⟩] with u hu
  have huD : e (complexExponential X d u).toMul ∈ chartSectionDomain X d (op W) y₀ :=
    ⟨e.map_source hu.1, by
      change e.symm (e (complexExponential X d u).toMul) ∈ (W : Set (ComplexPoint X))
      rw [e.left_inv hu.1]
      exact hu.2⟩
  have := functionValueAux_eq X d W F y₀ huD
  rw [e.left_inv hu.1] at this
  exact this


open Filter Topology in
open scoped CategoryTheory.MonObj in
/-- For abelian `X`, if `θ = dF` on `W` and `s` is a continuous section of `exp` on `U`, then
`F - exp^*θ(0) ∘ s` is locally constant on `U ∩ W`. -/
theorem eventually_functionValueAux_sub_eq (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X]
    [IsCommMonObj X] [SmoothOfRelativeDimension d X.hom] [IsIntegral X.left] [IsProjective X.hom]
    (θ : (holomorphicDeRhamSheaf X d 1).presheaf.obj (op ⊤))
    (W : Opens (TopCat.of (ComplexPoint X)))
    (F : Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d (op W)) 0)
    (hF : (holomorphicDeRhamSheaf X d 1).presheaf.map (homOfLE le_top).op θ =
      (toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
        (holomorphicDeRhamPresheaf X d 1)).app (op W)
          (Submodule.Quotient.mk (Algebra.DeRham.differential ℂ _ 0 F)))
    (U : Set (ComplexPoint X)) (s : ComplexPoint X → Fin d → ℂ) (hU : IsOpen U)
    (hs : ContinuousOn s U) (hsec : ∀ y ∈ U, (complexExponential X d (s y)).toMul = y)
    (y : ComplexPoint X) (hy : y ∈ U ∩ W) :
    ∀ᶠ y' in 𝓝 y, functionValueAux X d W F y' - expPullback X d θ 0 (s y') =
      functionValueAux X d W F y - expPullback X d θ 0 (s y) := by
  set G : (Fin d → ℂ) → ℂ := fun u ↦
    functionValueAux X d W F (complexExponential X d u).toMul - expPullback X d θ 0 u with hG
  have hE : Continuous (fun u ↦ (complexExponential X d u).toMul) :=
    (spec_mdifferentiable_complexExponential X d).continuous
  have hO : IsOpen ((fun u ↦ (complexExponential X d u).toMul) ⁻¹' (W : Set (ComplexPoint X))) :=
    W.isOpen.preimage hE
  have hderiv : ∀ u, (complexExponential X d u).toMul ∈ W → HasFDerivAt G (0 : (Fin d → ℂ) →L[ℂ] ℂ) u := by
    intro u hu
    have h1 := hasFDerivAt_functionValueAux_comp_exp X d θ W F hF u hu
    rw [spec_expPullback_eq_expPullback_zero X d θ u] at h1
    have h2 := h1.sub (expPullback X d θ 0).hasFDerivAt
    rwa [sub_self] at h2
  have hsy : (complexExponential X d (s y)).toMul ∈ W := by rw [hsec y hy.1]; exact hy.2
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hO (s y) hsy
  have hconst : ∀ u ∈ Metric.ball (s y) r, G u = G (s y) := by
    intro u hu
    refine (convex_ball (s y) r).is_const_of_fderivWithin_eq_zero (𝕜 := ℂ)
      (fun w hw ↦ (hderiv w (hball hw)).differentiableAt.differentiableWithinAt) ?_ hu
      (Metric.mem_ball_self hr)
    intro w hw
    rw [fderivWithin_of_isOpen Metric.isOpen_ball hw]
    exact (hderiv w (hball hw)).fderiv
  have hsc : ContinuousAt s y := hs.continuousAt (hU.mem_nhds hy.1)
  filter_upwards [hsc.preimage_mem_nhds (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr)),
    hU.mem_nhds hy.1] with y' hy' hy'U
  have h1 := hconst (s y') hy'
  simp only [hG, hsec y' hy'U, hsec y hy.1] at h1
  exact h1

open Filter Topology in
open scoped CategoryTheory.MonObj in
/-- Along a path in `U ∩ W`, the increment of `F` is the increment of `exp^*θ(0) ∘ s`. -/
theorem functionValueAux_sub_eq_of_path (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X]
    [IsCommMonObj X] [SmoothOfRelativeDimension d X.hom] [IsIntegral X.left] [IsProjective X.hom]
    (θ : (holomorphicDeRhamSheaf X d 1).presheaf.obj (op ⊤))
    (W : Opens (TopCat.of (ComplexPoint X)))
    (F : Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d (op W)) 0)
    (hF : (holomorphicDeRhamSheaf X d 1).presheaf.map (homOfLE le_top).op θ =
      (toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
        (holomorphicDeRhamPresheaf X d 1)).app (op W)
          (Submodule.Quotient.mk (Algebra.DeRham.differential ℂ _ 0 F)))
    (U : Set (ComplexPoint X)) (s : ComplexPoint X → Fin d → ℂ) (hU : IsOpen U)
    (hs : ContinuousOn s U) (hsec : ∀ y ∈ U, (complexExponential X d (s y)).toMul = y)
    (pth : C(unitInterval, ComplexPoint X)) (hpth : ∀ t, pth t ∈ U ∩ W) :
    functionValueAux X d W F (pth 1) - functionValueAux X d W F (pth 0) =
      expPullback X d θ 0 (s (pth 1)) - expPullback X d θ 0 (s (pth 0)) := by
  have hlc : IsLocallyConstant (fun t ↦ functionValueAux X d W F (pth t) -
      expPullback X d θ 0 (s (pth t))) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro t
    exact pth.continuous.continuousAt.eventually
      (eventually_functionValueAux_sub_eq X d θ W F hF U s hU hs hsec (pth t) (hpth t))
  have := hlc.apply_eq_of_preconnectedSpace 1 0
  linear_combination this

/-- The face `δ 0` of a singular `1`-simplex is its end point. -/
theorem toSSetObj₀Equiv_δ_zero {Y : TopCat.{0}} (σ : (TopCat.toSSet.obj Y) _⦋1⦌) :
    TopCat.toSSetObj₀Equiv ((TopCat.toSSet.obj Y).δ 0 σ) = simplexPath σ 1 := by
  rw [TopCat.toSSetObj₀Equiv_apply]
  erw [TopCat.toSSetObjEquiv_δ_apply]
  change _ = Y.toSSetObjEquiv _ σ (Convexity.StdSimplex.homeomorphI.symm 1)
  rw [Convexity.StdSimplex.homeomorphI_symm_one]
  congr 1
  rw [Subsingleton.elim (default : Convexity.StdSimplex ℝ (Fin 1)) (Convexity.StdSimplex.single 0),
    Convexity.StdSimplex.map_single]
  rfl

/-- The face `δ 1` of a singular `1`-simplex is its start point. -/
theorem toSSetObj₀Equiv_δ_one {Y : TopCat.{0}} (σ : (TopCat.toSSet.obj Y) _⦋1⦌) :
    TopCat.toSSetObj₀Equiv ((TopCat.toSSet.obj Y).δ 1 σ) = simplexPath σ 0 := by
  rw [TopCat.toSSetObj₀Equiv_apply]
  erw [TopCat.toSSetObjEquiv_δ_apply]
  change _ = Y.toSSetObjEquiv _ σ (Convexity.StdSimplex.homeomorphI.symm 0)
  rw [Convexity.StdSimplex.homeomorphI_symm_zero]
  congr 1
  rw [Subsingleton.elim (default : Convexity.StdSimplex ℝ (Fin 1)) (Convexity.StdSimplex.single 0),
    Convexity.StdSimplex.map_single]
  rfl



/-- On sheafified holomorphic functions, the integration map `Ω^0/ℂ → S^1` is the sheafified
coboundary of values. -/
theorem toSheafify_comp_primitiveQuotientToSingular (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] :
    toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
        (holomorphicDeRhamPresheaf X (dim X.left) 0) ≫
      (cokernel.π (constantsToHolomorphicDeRhamZeroSheaf X (dim X.left))).hom ≫
        (primitiveQuotientToSingular X).hom =
      (functionValuePresheafMap X ≫
        AlgebraicTopology.Singular.singularCochainCoboundary ℂ (TopCat.of (ComplexPoint X)) 0) ≫
        toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
          (AlgebraicTopology.Singular.singularCochainPresheaf ℂ (TopCat.of (ComplexPoint X)) 1) := by
  have e1 : cokernel.π (constantsToHolomorphicDeRhamZeroSheaf X (dim X.left)) ≫
      primitiveQuotientToSingular X = (presheafToSheaf _ _).map
        (functionValuePresheafMap X ≫
          AlgebraicTopology.Singular.singularCochainCoboundary ℂ (TopCat.of (ComplexPoint X)) 0) := by
    rw [primitiveQuotientToSingular, cokernel.π_desc, Functor.map_comp]
    rfl
  change _ ≫ (cokernel.π (constantsToHolomorphicDeRhamZeroSheaf X (dim X.left)) ≫
      primitiveQuotientToSingular X).hom = _
  rw [e1]
  exact (toSheafify_naturality (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
    (functionValuePresheafMap X ≫
      AlgebraicTopology.Singular.singularCochainCoboundary ℂ (TopCat.of (ComplexPoint X)) 0)).symm

/-- On sheafified holomorphic functions, `Ω^0/ℂ → Ω^1_cl → Ω^1` is the sheafified exterior
derivative. -/
theorem toSheafify_comp_primitiveQuotientToClosedOneForm (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] :
    toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
        (holomorphicDeRhamPresheaf X (dim X.left) 0) ≫
      (cokernel.π (constantsToHolomorphicDeRhamZeroSheaf X (dim X.left))).hom ≫
        (primitiveQuotientToClosedOneForm X ≫ kernel.ι _).hom =
      holomorphicDeRhamDifferential X (dim X.left) 0 ≫
        toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
          (holomorphicDeRhamPresheaf X (dim X.left) 1) := by
  have e1 : cokernel.π (constantsToHolomorphicDeRhamZeroSheaf X (dim X.left)) ≫
      primitiveQuotientToClosedOneForm X ≫ kernel.ι _ = (presheafToSheaf _ _).map
        (holomorphicDeRhamDifferential X (dim X.left) 0) := by
    rw [primitiveQuotientToClosedOneForm, cokernel.π_desc_assoc, closedOneFormDifferential,
      kernel.lift_ι]
    rfl
  change _ ≫ (cokernel.π (constantsToHolomorphicDeRhamZeroSheaf X (dim X.left)) ≫
      primitiveQuotientToClosedOneForm X ≫ kernel.ι _).hom = _
  rw [e1]
  exact (toSheafify_naturality (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
    (holomorphicDeRhamDifferential X (dim X.left) 0)).symm

/-- Two maps of simplicial sets applied to the chain of one simplex. -/
theorem chainOfSimplex_map_map {A B C : SSet.{0}} (f : A ⟶ B) (g : B ⟶ C) {n : ℕ}
    (σ : A _⦋n⦌) :
    ((SSet.chainComplexMap g (ModuleCat.of ℂ ℂ)).f n).hom
      (((SSet.chainComplexMap f (ModuleCat.of ℂ ℂ)).f n).hom
        (AlgebraicTopology.Simplicial.chainOfSimplex ℂ σ)) =
      AlgebraicTopology.Simplicial.chainOfSimplex ℂ (g.app _ (f.app _ σ)) := by
  rw [AlgebraicTopology.Simplicial.chainOfSimplex_map,
    AlgebraicTopology.Simplicial.chainOfSimplex_map]

/-- The coboundary of the values of a holomorphic function on a singular `1`-simplex is the value at
the end point minus the value at the start point. -/
theorem coboundary_functionValueCochain_chainOfSimplex (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] (W V : Opens (TopCat.of (ComplexPoint X))) (k : V ⟶ W)
    (F : Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X (dim X.left) (op W)) 0)
    (σ : (TopCat.toSSet.obj ((Opens.toTopCat (TopCat.of (ComplexPoint X))).obj V)) _⦋1⦌) :
    AlgebraicTopology.Simplicial.coboundary ℂ 0
      (functionValueCochain X (op V) (holomorphicFormRestriction X (dim X.left) k.op 0
        (Submodule.Quotient.mk F)))
      (AlgebraicTopology.Simplicial.chainOfSimplex ℂ σ) =
      functionValueAux X (dim X.left) W F (simplexPath σ 1).1 -
        functionValueAux X (dim X.left) W F (simplexPath σ 0).1 := by
  have hval : ∀ τ : (TopCat.toSSet.obj ((Opens.toTopCat (TopCat.of (ComplexPoint X))).obj V)) _⦋0⦌,
      functionValueCochain X (op V) (holomorphicFormRestriction X (dim X.left) k.op 0
        (Submodule.Quotient.mk F)) (AlgebraicTopology.Simplicial.chainOfSimplex ℂ τ) =
      functionValueAux X (dim X.left) W F (TopCat.toSSetObj₀Equiv τ).1 := by
    intro τ
    change simplexCochain ℂ _ 0 _ (AlgebraicTopology.Simplicial.chainOfSimplex ℂ τ) = _
    rw [spec_simplexCochain_chainOfSimplex, holomorphicFunctionValue_restriction]
    rfl
  have hc := AlgebraicTopology.Simplicial.coboundary_chainOfSimplex ℂ
    (functionValueCochain X (op V) (holomorphicFormRestriction X (dim X.left) k.op 0
      (Submodule.Quotient.mk F))) (n := 0) σ
  rw [hc, Fin.sum_univ_two]
  erw [hval, hval]
  rw [toSSetObj₀Equiv_δ_zero, toSSetObj₀Equiv_δ_one]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul]
  rw [← sub_eq_add_neg]

end LaneB

theorem spec_globalCochainSection_singularIntegrationCochain_aux (X : Over (Spec ↧ℂ))
    [GrpObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (θ : GlobalHolomorphicForm X 1)
    (θ' : (TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
      (TopCat.of (ComplexPoint X))).obj (primitiveQuotientSheaf X))
    (h : ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
        (TopCat.of (ComplexPoint X))).map
      (primitiveQuotientToClosedOneForm X ≫ kernel.ι _)).hom θ' = θ) :
    globalCochainSection X 1 (singularIntegrationCochain X (dim X.left) θ) =
      ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
        (TopCat.of (ComplexPoint X))).map (primitiveQuotientToSingular X)).hom θ' := by
  have : IsCommMonObj X :=
    isCommMonObj_of_complexSelfProductIntegral X (complexSelfProductIntegral_of_isIntegral X)
  set Y := TopCat.of (ComplexPoint X) with hYdef
  set J := Opens.grothendieckTopology Y with hJ
  rw [spec_globalCochainSection_eq_toSheafify_aux]
  refine TopCat.Presheaf.section_ext (AlgebraicTopology.Singular.singularCochainSheaf ℂ Y 1) ⊤
    _ _ fun x _ ↦ ?_
  -- lift `θ'` near `x` through `cokernel.π`
  have hπ : Sheaf.IsLocallySurjective
      (cokernel.π (constantsToHolomorphicDeRhamZeroSheaf X (dim X.left))) := by
    have : Epi (cokernel.π (constantsToHolomorphicDeRhamZeroSheaf X (dim X.left))) :=
      inferInstance
    exact (Sheaf.isLocallySurjective_iff_epi' _ _).2 this
  obtain ⟨W₁, i₁, ⟨f, hf⟩, hxW₁⟩ := Presheaf.imageSieve_mem J
    (cokernel.π (constantsToHolomorphicDeRhamZeroSheaf X (dim X.left))).hom θ' x trivial
  obtain ⟨W₂, i₂, ⟨F₀, hF₀⟩, hxW₂⟩ := Presheaf.imageSieve_mem J
    (toSheafify J (holomorphicDeRhamPresheaf X (dim X.left) 0)) f x hxW₁
  obtain ⟨F, rfl⟩ := Submodule.Quotient.mk_surjective _ F₀
  obtain ⟨U, s, hU, hxU, hs, hsec, hint⟩ :=
    spec_exists_local_integration_primitive X (dim X.left) θ x
  have hres : ∀ (V' : Opens Y) (k : V' ⟶ W₂),
      (primitiveQuotientSheaf X).obj.map (homOfLE le_top : V' ⟶ ⊤).op θ' =
        (cokernel.π (constantsToHolomorphicDeRhamZeroSheaf X (dim X.left))).hom.app (op V')
          ((toSheafify J (holomorphicDeRhamPresheaf X (dim X.left) 0)).app (op V')
            ((holomorphicDeRhamPresheaf X (dim X.left) 0).map k.op
              (Submodule.Quotient.mk F))) := by
    intro V' k
    rw [show (homOfLE le_top : V' ⟶ ⊤) = k ≫ i₂ ≫ i₁ from Subsingleton.elim _ _]
    rw [op_comp, op_comp, Functor.map_comp, Functor.map_comp]
    erw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
    rw [← hf]
    erw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply, ← hF₀]
    erw [NatTrans.naturality_apply (toSheafify J (holomorphicDeRhamPresheaf X (dim X.left) 0))]
    rfl
  have hFθ : (holomorphicDeRhamSheaf X (dim X.left) 1).presheaf.map
      (homOfLE le_top : W₂ ⟶ ⊤).op θ =
      (toSheafify J (holomorphicDeRhamPresheaf X (dim X.left) 1)).app (op W₂)
        (Submodule.Quotient.mk (Algebra.DeRham.differential ℂ _ 0 F)) := by
    rw [← h]
    change (holomorphicDeRhamSheaf X (dim X.left) 1).presheaf.map _
      ((primitiveQuotientToClosedOneForm X ≫ kernel.ι _).hom.app (op ⊤) θ') = _
    erw [← NatTrans.naturality_apply]
    erw [hres W₂ (𝟙 W₂)]
    have key := ConcreteCategory.congr_hom
      (NatTrans.congr_app (toSheafify_comp_primitiveQuotientToClosedOneForm X) (op W₂))
      ((holomorphicDeRhamPresheaf X (dim X.left) 0).map (𝟙 W₂).op (Submodule.Quotient.mk F))
    simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at key
    erw [key]
    rw [op_id, CategoryTheory.Functor.map_id]
    rfl
  let V : Opens Y := W₂ ⊓ ⟨U, hU⟩
  have hxV : x ∈ V := ⟨hxW₂, hxU⟩
  refine (TopCat.Presheaf.germ_res_apply _ (homOfLE le_top : V ⟶ ⊤) x hxV _).symm.trans
    (Eq.trans ?_ (TopCat.Presheaf.germ_res_apply _ (homOfLE le_top : V ⟶ ⊤) x hxV _))
  congr 1
  change _ = (AlgebraicTopology.Singular.singularCochainSheaf ℂ Y 1).presheaf.map _
    ((primitiveQuotientToSingular X).hom.app (op ⊤) θ')
  erw [← NatTrans.naturality_apply (primitiveQuotientToSingular X).hom]
  erw [hres V (homOfLE inf_le_left)]
  have key := ConcreteCategory.congr_hom
    (NatTrans.congr_app (toSheafify_comp_primitiveQuotientToSingular X) (op V))
    ((holomorphicDeRhamPresheaf X (dim X.left) 0).map (homOfLE inf_le_left : V ⟶ W₂).op
      (Submodule.Quotient.mk F))
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at key
  erw [key]
  erw [← NatTrans.naturality_apply (toSheafify J
    (AlgebraicTopology.Singular.singularCochainPresheaf ℂ Y 1))]
  rw [NatTrans.comp_app]
  erw [ConcreteCategory.comp_apply]
  refine congrArg _ ?_
  refine cochain_ext_chainOfSimplex _ _ fun σ ↦ ?_
  change singularIntegrationCochain X (dim X.left) θ
      (((SSet.chainComplexMap (TopCat.toSSet.map (Opens.inclusionTopIso Y).hom)
        (ModuleCat.of ℂ ℂ)).f 1).hom
        (((SSet.chainComplexMap (TopCat.toSSet.map ((Opens.toTopCat Y).map
          (homOfLE le_top : V ⟶ ⊤))) (ModuleCat.of ℂ ℂ)).f 1).hom
          (AlgebraicTopology.Simplicial.chainOfSimplex ℂ σ))) =
    AlgebraicTopology.Simplicial.coboundary ℂ 0
      (functionValueCochain X (op V) (holomorphicFormRestriction X (dim X.left)
        (homOfLE inf_le_left : V ⟶ W₂).op 0 (Submodule.Quotient.mk F)))
      (AlgebraicTopology.Simplicial.chainOfSimplex ℂ σ)
  refine (congrArg (singularIntegrationCochain X (dim X.left) θ)
    (chainOfSimplex_map_map _ _ σ)).trans ?_
  refine (hint _ fun t ↦ ?_).trans ?_
  · exact (simplexPath σ t).2.2
  have hR := coboundary_functionValueCochain_chainOfSimplex X W₂ V (homOfLE inf_le_left) F σ
  have hP := functionValueAux_sub_eq_of_path X (dim X.left) θ W₂ F hFθ U s hU hs hsec
    ⟨fun t ↦ (simplexPath σ t).1, continuous_subtype_val.comp (simplexPath σ).continuous⟩
    fun t ↦ ⟨(simplexPath σ t).2.2, (simplexPath σ t).2.1⟩
  exact hP.symm.trans hR.symm

set_option backward.isDefEq.respectTransparency false in
/-- The comparison `T' → T` in degree `1`: `[f] ↦ df` through the extension and double
isomorphisms. -/
theorem primitiveComplexToClosedFormComplex_f_one (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] :
    (primitiveComplexToClosedFormComplex X).f ((1 : ℕ) : ℤ) =
      ((primitiveComplexNat X).extendXIso ComplexShape.embeddingUpNat (i := 1) rfl).hom ≫
        ((HomologicalComplex.doubleXIso₁ _ _ (by decide)).hom ≫
        primitiveQuotientToClosedOneForm X ≫
          (HomologicalComplex.doubleXIso₁ _ _ (by decide)).inv) ≫
        ((closedFormComplexNat X).extendXIso ComplexShape.embeddingUpNat (i := 1) rfl).inv := by
  have h := HomologicalComplex.extendMap_f (primitiveComplexNatToClosedFormComplexNat X)
    ComplexShape.embeddingUpNat (i := 1) (i' := ((1 : ℕ) : ℤ)) rfl
  rw [primitiveComplexNatToClosedFormComplexNat, HomologicalComplex.mkHomFromDouble_f₁] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- The inclusion `T → Ω•` in degree `1`: the inclusion of closed forms. -/
theorem closedFormComplexToDeRham_f_one (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] :
    (closedFormComplexToDeRham X).f ((1 : ℕ) : ℤ) =
      ((closedFormComplexNat X).extendXIso ComplexShape.embeddingUpNat (i := 1) rfl).hom ≫
        ((HomologicalComplex.doubleXIso₁ _ _ (by decide)).hom ≫ kernel.ι _) ≫
        ((holomorphicDeRhamComplex X (dim X.left)).extendXIso ComplexShape.embeddingUpNat
          (i := 1) rfl).inv := by
  have h := HomologicalComplex.extendMap_f (closedFormComplexNatToDeRham X)
    ComplexShape.embeddingUpNat (i := 1) (i' := ((1 : ℕ) : ℤ)) rfl
  have h' : (closedFormComplexNatToDeRham X).f 1 =
      (HomologicalComplex.doubleXIso₁ _ _ (by decide)).hom ≫ kernel.ι _ := by
    unfold closedFormComplexNatToDeRham
    exact HomologicalComplex.mkHomFromDouble_f₁ ..
  rw [h'] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- The composite `T' → T → Ω•` in degree `1`. -/
theorem primitiveToDeRham_f_one (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] :
    (primitiveComplexToClosedFormComplex X ≫ closedFormComplexToDeRham X).f ((1 : ℕ) : ℤ) =
      ((primitiveComplexNat X).extendXIso ComplexShape.embeddingUpNat (i := 1) rfl).hom ≫
        (HomologicalComplex.doubleXIso₁ _ _ (by decide)).hom ≫
        primitiveQuotientToClosedOneForm X ≫ kernel.ι _ ≫
        ((holomorphicDeRhamComplex X (dim X.left)).extendXIso ComplexShape.embeddingUpNat
          (i := 1) rfl).inv := by
  rw [HomologicalComplex.comp_f, primitiveComplexToClosedFormComplex_f_one,
    closedFormComplexToDeRham_f_one]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- The inclusion `F^1 Ω• → Ω•` in degree `1`, through `filteredDeRhamXOneIso`. -/
theorem hodgeFilteredDeRhamInclusion_f_one (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] :
    (hodgeFilteredDeRhamInclusion X 1).f ((1 : ℕ) : ℤ) =
      (filteredDeRhamXOneIso X).hom ≫
        ((holomorphicDeRhamComplex X (dim X.left)).extendXIso ComplexShape.embeddingUpNat
          (i := 1) rfl).inv := by
  rw [hodgeFilteredDeRhamInclusion, HomologicalComplex.stupidTruncInclusion_f Ω•(X)
    (ComplexShape.embeddingUpIntGE 1) (i := 0) (by simp)]
  simp only [filteredDeRhamXOneIso, Iso.trans_hom, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/-- The integration map `T' → S•` in degree `1`. -/
theorem primitiveToSingular_f_one (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] :
    (primitiveComplexToSingular X).f ((1 : ℕ) : ℤ) =
      ((primitiveComplexNat X).extendXIso ComplexShape.embeddingUpNat (i := 1) rfl).hom ≫
        (HomologicalComplex.doubleXIso₁ _ _ (by decide)).hom ≫
        primitiveQuotientToSingular X ≫
        ((AlgebraicTopology.Singular.singularCochainSheafComplex ℂ
          (TopCat.of (ComplexPoint X))).extendXIso ComplexShape.embeddingUpNat
          (i := 1) rfl).inv := by
  have h := HomologicalComplex.extendMap_f (primitiveComplexNatToSingular X)
    ComplexShape.embeddingUpNat (i := 1) (i' := ((1 : ℕ) : ℤ)) rfl
  rw [primitiveComplexNatToSingular, HomologicalComplex.mkHomFromDouble_f₁, Category.assoc] at h
  exact h


/-- A chain map sends the class of a cycle to the class of its image. -/
lemma addCommGrp_homologyMap_homologyπ_apply {ι : Type*} {cs : ComplexShape ι}
    {K L : HomologicalComplex AddCommGrpCat cs} (f : K ⟶ L) (n : ι)
    (c : K.cycles n) :
    HomologicalComplex.homologyMap f n (K.homologyπ n c) =
      L.homologyπ n (HomologicalComplex.cyclesMap f n c) := by
  rw [← ConcreteCategory.comp_apply, HomologicalComplex.homologyπ_naturality,
    ConcreteCategory.comp_apply]

/-- The cycle map is the chain map on underlying elements. -/
lemma addCommGrp_iCycles_cyclesMap_apply {ι : Type*} {cs : ComplexShape ι}
    {K L : HomologicalComplex AddCommGrpCat cs} (f : K ⟶ L) (n : ι)
    (c : K.cycles n) :
    L.iCycles n (HomologicalComplex.cyclesMap f n c) = f.f n (K.iCycles n c) := by
  rw [← ConcreteCategory.comp_apply, HomologicalComplex.cyclesMap_i, ConcreteCategory.comp_apply]

/-- `extendHomologyIso` on the class of a cycle. -/
lemma addCommGrp_extendHomologyIso_inv_homologyπ_apply (K : CochainComplex AddCommGrpCat ℕ)
    (n : ℕ)
    (d : K.cycles n) :
    (K.extendHomologyIso ComplexShape.embeddingUpNat (j := n) rfl).inv (K.homologyπ n d) =
      (K.extend ComplexShape.embeddingUpNat).homologyπ n
        ((K.extendCyclesIso ComplexShape.embeddingUpNat (j := n) rfl).inv d) := by
  have h := ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_extendHomologyIso_inv K
    ComplexShape.embeddingUpNat (j := n) (j' := (n : ℤ)) rfl) d
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h
  exact h

/-- `extendCyclesIso` on underlying elements. -/
lemma addCommGrp_iCycles_extendCyclesIso_inv_apply (K : CochainComplex AddCommGrpCat ℕ)
    (n : ℕ)
    (d : K.cycles n) :
    (K.extend ComplexShape.embeddingUpNat).iCycles n
        ((K.extendCyclesIso ComplexShape.embeddingUpNat (j := n) rfl).inv d) =
      (K.extendXIso ComplexShape.embeddingUpNat (i := n) rfl).inv (K.iCycles n d) := by
  have h := ConcreteCategory.congr_hom (HomologicalComplex.extendCyclesIso_inv_iCycles K
    ComplexShape.embeddingUpNat (j := n) (j' := (n : ℤ)) rfl) d
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h
  exact h

/-- Cycles with the same underlying element are equal. -/
lemma addCommGrp_cycles_ext {K : CochainComplex AddCommGrpCat ℤ} {n : ℤ} {c d : K.cycles n}
    (h : K.iCycles n c = K.iCycles n d) : c = d :=
  (AddCommGrpCat.mono_iff_injective (K.iCycles n)).1 inferInstance h

set_option backward.isDefEq.respectTransparency false in
/-- The composite `T' → T → Ω•` in degree `1` on the degree-`1` term `Ω^0/ℂ` of `T'`. -/
theorem primitiveToDeRham_f_one_section (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] :
    ((HomologicalComplex.doubleXIso₁ _ _ (by decide)).inv ≫
          ((primitiveComplexNat X).extendXIso ComplexShape.embeddingUpNat (i := 1) rfl).inv) ≫
        (primitiveComplexToClosedFormComplex X ≫ closedFormComplexToDeRham X).f
          ((1 : ℕ) : ℤ) =
      (primitiveQuotientToClosedOneForm X ≫ kernel.ι _) ≫
        ((holomorphicDeRhamComplex X (dim X.left)).extendXIso ComplexShape.embeddingUpNat
          (i := 1) rfl).inv := by
  rw [primitiveToDeRham_f_one]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- The de Rham side of statement 11: the class of `θ'` in `H^1(Γ(T'))` and the class of `z` in
`H^1(Γ(F^1 Ω•))` have the same image in `H^1(Γ(Ω•))`. -/
theorem deRham_homologyMap_primitive_eq (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    (z : (filteredGlobalSections X).cycles ((1 : ℕ) : ℤ))
    (θ' : (TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
      (TopCat.of (ComplexPoint X))).obj (primitiveQuotientSheaf X))
    (hz : ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
        (TopCat.of (ComplexPoint X))).map
      (primitiveQuotientToClosedOneForm X ≫ kernel.ι _)).hom θ' = cycleOneForm X z)
    (c : (TopCat.Sheaf.globalSectionsComplexInt (TopCat.of (ComplexPoint X))
      (primitiveComplex X)).cycles ((1 : ℕ) : ℤ))
    (hc : (TopCat.Sheaf.globalSectionsComplexInt (TopCat.of (ComplexPoint X))
      (primitiveComplex X)).iCycles ((1 : ℕ) : ℤ) c =
      ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
        (TopCat.of (ComplexPoint X))).map
        ((HomologicalComplex.doubleXIso₁ _ _ (by decide)).inv ≫
          ((primitiveComplexNat X).extendXIso ComplexShape.embeddingUpNat (i := 1) rfl).inv)).hom
        θ') :
    HomologicalComplex.homologyMap
        (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
          (TopCat.of (ComplexPoint X))).mapHomologicalComplex _).map
            (primitiveComplexToClosedFormComplex X ≫ closedFormComplexToDeRham X)) _
        ((TopCat.Sheaf.globalSectionsComplexInt (TopCat.of (ComplexPoint X))
          (primitiveComplex X)).homologyπ ((1 : ℕ) : ℤ) c) =
      HomologicalComplex.homologyMap
        (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
          (TopCat.of (ComplexPoint X))).mapHomologicalComplex _).map
            (hodgeFilteredDeRhamInclusion X 1)) _
        ((filteredGlobalSections X).homologyπ ((1 : ℕ) : ℤ) z) := by
  let Γ := TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
    (TopCat.of (ComplexPoint X))
  erw [addCommGrp_homologyMap_homologyπ_apply, addCommGrp_homologyMap_homologyπ_apply]
  congr 1
  apply addCommGrp_cycles_ext
  erw [addCommGrp_iCycles_cyclesMap_apply, addCommGrp_iCycles_cyclesMap_apply, hc]
  change (Γ.map (((HomologicalComplex.doubleXIso₁ _ _ (by decide)).inv ≫
      ((primitiveComplexNat X).extendXIso ComplexShape.embeddingUpNat (i := 1) rfl).inv) ≫
      (primitiveComplexToClosedFormComplex X ≫ closedFormComplexToDeRham X).f
        ((1 : ℕ) : ℤ))).hom θ' =
    (Γ.map ((hodgeFilteredDeRhamInclusion X 1).f ((1 : ℕ) : ℤ))).hom _
  rw [primitiveToDeRham_f_one_section, hodgeFilteredDeRhamInclusion_f_one]
  change (Γ.map _).hom ((Γ.map (primitiveQuotientToClosedOneForm X ≫ kernel.ι _)).hom θ') =
    (Γ.map _).hom ((Γ.map (filteredDeRhamXOneIso X).hom).hom _)
  rw [hz]
  rfl


/-- The inverse of the extension comparison, in a degree coming from the original complex. -/
lemma mapExtendCanonicalIso_inv_f_of_eq {C D I J : Type*} [Category* C] [Category* D]
    [Preadditive C] [Preadditive D] [HasZeroObject C] [HasZeroObject D] {c : ComplexShape I}
    {c' : ComplexShape J} (F : C ⥤ D) [F.Additive]
    (K : HomologicalComplex C c) (e : c.Embedding c') {i : I} {j : J} (h : e.f i = j) :
    (HomologicalComplex.mapExtendCanonicalIso F K e).inv.f j =
      (((F.mapHomologicalComplex c).obj K).extendXIso e h).hom ≫
        F.map (K.extendXIso e h).inv := by
  rw [← cancel_epi ((HomologicalComplex.mapExtendCanonicalIso F K e).hom.f j),
    ← HomologicalComplex.comp_f, Iso.hom_inv_id,
    HomologicalComplex.mapExtendCanonicalIso_hom_f F K e h]
  simp [← F.map_comp]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The inverse of `globalSectionsSingularCochainComplexIntIsoExtendField` in degree `1`. -/
theorem globalSectionsSingularCochainComplexIntIsoExtendField_inv_f_one (X : Over (Spec ↧ℂ))
    (y : (TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
      (TopCat.of (ComplexPoint X))).obj
        ((AlgebraicTopology.Singular.singularCochainSheafComplex ℂ
          (TopCat.of (ComplexPoint X))).X 1)) :
    (globalSectionsSingularCochainComplexIntIsoExtendField ℂ X).inv.f ((1 : ℕ) : ℤ)
        (((AlgebraicTopology.Singular.globalSingularCochainSheafComplex ℂ
          (TopCat.of (ComplexPoint X))).extendXIso ComplexShape.embeddingUpNat
            (i := 1) rfl).inv y) =
      ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
        (TopCat.of (ComplexPoint X))).map
          ((AlgebraicTopology.Singular.singularCochainSheafComplex ℂ
            (TopCat.of (ComplexPoint X))).extendXIso ComplexShape.embeddingUpNat (i := 1) rfl).inv)
        y := by
  dsimp only [globalSectionsSingularCochainComplexIntIsoExtendField, Iso.trans_inv,
    Functor.mapIso_inv, Iso.symm_inv]
  rw [HomologicalComplex.comp_f]
  erw [HomologicalComplex.extendMap_f _ _ (i := 1) rfl,
    mapExtendCanonicalIso_inv_f_of_eq _ _ _ (i := 1) rfl]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, ConcreteCategory.comp_apply]
  erw [Iso.inv_hom_id_apply]
  rfl


set_option backward.isDefEq.respectTransparency false in
/-- The integration map `T' → S•` in degree `1` on the degree-`1` term `Ω^0/ℂ` of `T'`. -/
theorem primitiveToSingular_f_one_section (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] :
    ((HomologicalComplex.doubleXIso₁ _ _ (by decide)).inv ≫
          ((primitiveComplexNat X).extendXIso ComplexShape.embeddingUpNat (i := 1) rfl).inv) ≫
        (primitiveComplexToSingular X).f ((1 : ℕ) : ℤ) =
      primitiveQuotientToSingular X ≫
        ((AlgebraicTopology.Singular.singularCochainSheafComplex ℂ
          (TopCat.of (ComplexPoint X))).extendXIso ComplexShape.embeddingUpNat
          (i := 1) rfl).inv := by
  rw [primitiveToSingular_f_one]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- The singular side of statement 11: the first legs of `singularToFieldCohomology` send `[Ψ]` to
the image of the class of `θ'` under the integration map `T' → S•`. -/
theorem singular_homology_class_eq (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    (θ' : (TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
      (TopCat.of (ComplexPoint X))).obj (primitiveQuotientSheaf X))
    (Ψ : AlgebraicTopology.Simplicial.Cocycle ℂ
      (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) 1)
    (hΨ : globalCochainSection X 1 Ψ.1 =
      ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
        (TopCat.of (ComplexPoint X))).map (primitiveQuotientToSingular X)).hom θ')
    (c : (TopCat.Sheaf.globalSectionsComplexInt (TopCat.of (ComplexPoint X))
      (primitiveComplex X)).cycles ((1 : ℕ) : ℤ))
    (hc : (TopCat.Sheaf.globalSectionsComplexInt (TopCat.of (ComplexPoint X))
      (primitiveComplex X)).iCycles ((1 : ℕ) : ℤ) c =
      ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
        (TopCat.of (ComplexPoint X))).map
        ((HomologicalComplex.doubleXIso₁ _ _ (by decide)).inv ≫
          ((primitiveComplexNat X).extendXIso ComplexShape.embeddingUpNat (i := 1) rfl).inv)).hom
        θ') :
    (HomologicalComplex.homologyMapIso
              (globalSectionsSingularCochainComplexIntIsoExtendField ℂ X) ((1 : ℕ) : ℤ)).inv
              ((HomologicalComplex.extendHomologyIso
                (AlgebraicTopology.Singular.globalSingularCochainSheafComplex ℂ
                  (TopCat.of (ComplexPoint X))) ComplexShape.embeddingUpNat (j := 1) rfl).inv
                (HomologicalComplex.homologyMap
                  (AlgebraicTopology.Singular.topOpenToGlobalSingularCochainSheafComplex ℂ
                    (TopCat.of (ComplexPoint X))) 1
                  (AlgebraicTopology.Singular.ordinarySingularCohomologyEquivGlobalRaw ℂ
                    (TopCat.of (ComplexPoint X)) 1
                    (Singular.cohomologyClass (TopCat.of (ComplexPoint X)) 1 Ψ)))) =
      HomologicalComplex.homologyMap
        (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
          (TopCat.of (ComplexPoint X))).mapHomologicalComplex _).map
            (primitiveComplexToSingular X)) _
        ((TopCat.Sheaf.globalSectionsComplexInt (TopCat.of (ComplexPoint X))
          (primitiveComplex X)).homologyπ ((1 : ℕ) : ℤ) c) := by
  let Y := TopCat.of (ComplexPoint X)
  let Γ := TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y
  let G := AlgebraicTopology.Singular.globalSingularCochainSheafComplex ℂ Y
  obtain ⟨c0, hc0i, hc0⟩ := exists_cohomologyClass_eq_homologyπ Y ℂ 1 Ψ
  obtain ⟨c', hc'i, hc'⟩ := ordinarySingularCohomologyEquivGlobalRaw_homologyπ Y ℂ 1 c0
  rw [hc0, hc']
  erw [addCommGrp_homologyMap_homologyπ_apply, addCommGrp_extendHomologyIso_inv_homologyπ_apply]
  change HomologicalComplex.homologyMap
    (globalSectionsSingularCochainComplexIntIsoExtendField ℂ X).inv _ _ = _
  erw [addCommGrp_homologyMap_homologyπ_apply, addCommGrp_homologyMap_homologyπ_apply]
  congr 1
  apply addCommGrp_cycles_ext
  erw [addCommGrp_iCycles_cyclesMap_apply, addCommGrp_iCycles_cyclesMap_apply,
    addCommGrp_iCycles_extendCyclesIso_inv_apply,
    addCommGrp_iCycles_cyclesMap_apply, hc'i, hc0i, hc]
  change (globalSectionsSingularCochainComplexIntIsoExtendField ℂ X).inv.f ((1 : ℕ) : ℤ)
      ((G.extendXIso ComplexShape.embeddingUpNat (i := 1) rfl).inv
        (globalCochainSection X 1 Ψ.1)) =
    (Γ.map (((HomologicalComplex.doubleXIso₁ _ _ (by decide)).inv ≫
      ((primitiveComplexNat X).extendXIso ComplexShape.embeddingUpNat (i := 1) rfl).inv) ≫
      (primitiveComplexToSingular X).f ((1 : ℕ) : ℤ))).hom θ'
  rw [hΨ, primitiveToSingular_f_one_section]
  erw [globalSectionsSingularCochainComplexIntIsoExtendField_inv_f_one]
  rfl

/-- The hypercohomology part of statement 11. -/
theorem deRham_singular_assembly (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom]
    (z : (filteredGlobalSections X).cycles ((1 : ℕ) : ℤ))
    (w : (TopCat.Sheaf.globalSectionsComplexInt (TopCat.of (ComplexPoint X))
      (primitiveComplex X)).homology ((1 : ℕ) : ℤ))
    (x : AlgebraicTopology.Singular.Cohomology ℂ (TopCat.of (ComplexPoint X)) 1)
    (hS : (HomologicalComplex.homologyMapIso
              (globalSectionsSingularCochainComplexIntIsoExtendField ℂ X) ((1 : ℕ) : ℤ)).inv
              ((HomologicalComplex.extendHomologyIso
                (AlgebraicTopology.Singular.globalSingularCochainSheafComplex ℂ
                  (TopCat.of (ComplexPoint X))) ComplexShape.embeddingUpNat (j := 1) rfl).inv
                (HomologicalComplex.homologyMap
                  (AlgebraicTopology.Singular.topOpenToGlobalSingularCochainSheafComplex ℂ
                    (TopCat.of (ComplexPoint X))) 1
                  (AlgebraicTopology.Singular.ordinarySingularCohomologyEquivGlobalRaw ℂ
                    (TopCat.of (ComplexPoint X)) 1 x))) =
      HomologicalComplex.homologyMap
        (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
          (TopCat.of (ComplexPoint X))).mapHomologicalComplex _).map
            (primitiveComplexToSingular X)) _ w)
    (hD : HomologicalComplex.homologyMap
        (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
          (TopCat.of (ComplexPoint X))).mapHomologicalComplex _).map
            (primitiveComplexToClosedFormComplex X ≫ closedFormComplexToDeRham X)) _ w =
      HomologicalComplex.homologyMap
        (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
          (TopCat.of (ComplexPoint X))).mapHomologicalComplex _).map
            (hodgeFilteredDeRhamInclusion X 1)) _
        ((filteredGlobalSections X).homologyπ ((1 : ℕ) : ℤ) z)) :
    fieldToDeRhamCohomology ℂ X 1 (singularToFieldCohomology ℂ X 1 x) =
      cycleDeRhamClass X z := by
  have hq : HomologicalComplex.quasiIso _ _ (constantsToPrimitiveComplex X) := by
    rw [HomologicalComplex.mem_quasiIso_iff]
    exact spec_constantsToPrimitiveComplex_quasiIso_aux X
  obtain ⟨β, hβ⟩ := (Localization.SmallShiftedHom.postcompEquiv.{1} _ hq
    (a := ((1 : ℕ) : ℤ))).bijective.2
    (globalSectionsToHypercohomology X (primitiveComplex X) _ w)
  change hypercohomologyMap X (constantsToPrimitiveComplex X) _ β = _ at hβ
  rw [singularToFieldCohomology_apply, hS, globalSectionsToHypercohomology_naturality, ← hβ,
    ← hypercohomologyMap_comp_apply, spec_constantsToPrimitiveComplex_comp_toSingular_aux]
  change fieldToDeRhamCohomology ℂ X 1 (hypercohomologyAddEquivConstantCohomology ℂ X 1
    ((fieldHypercohomologySingularCochainAddEquiv ℂ X 1).symm
      (fieldHypercohomologySingularCochainAddEquiv ℂ X 1 β))) = _
  rw [AddEquiv.symm_apply_apply, fieldToDeRhamCohomology_complex_eq, AddEquiv.symm_apply_apply,
    ← spec_constantsToClosedFormComplex_comp_toDeRham_aux,
    ← spec_constantsToPrimitiveComplex_comp_aux, Category.assoc, hypercohomologyMap_comp_apply,
    hβ, ← globalSectionsToHypercohomology_naturality,
    hD, globalSectionsToHypercohomology_naturality]
  rfl

theorem spec_deRham_singularToFieldCohomology_of_primitive_aux (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom]
    (z : (filteredGlobalSections X).cycles ((1 : ℕ) : ℤ))
    (θ' : (TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
      (TopCat.of (ComplexPoint X))).obj (primitiveQuotientSheaf X))
    (hz : ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
        (TopCat.of (ComplexPoint X))).map
      (primitiveQuotientToClosedOneForm X ≫ kernel.ι _)).hom θ' = cycleOneForm X z)
    (Ψ : AlgebraicTopology.Simplicial.Cocycle ℂ
      (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) 1)
    (hΨ : globalCochainSection X 1 Ψ.1 =
      ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
        (TopCat.of (ComplexPoint X))).map (primitiveQuotientToSingular X)).hom θ') :
    fieldToDeRhamCohomology ℂ X 1 (singularToFieldCohomology ℂ X 1
        (Singular.cohomologyClass (TopCat.of (ComplexPoint X)) 1 Ψ)) =
      cycleDeRhamClass X z := by
  let Γ := TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
    (TopCat.of (ComplexPoint X))
  let K := TopCat.Sheaf.globalSectionsComplexInt (TopCat.of (ComplexPoint X)) (primitiveComplex X)
  have hzero : IsZero ((primitiveComplex X).X ((2 : ℕ) : ℤ)) :=
    (HomologicalComplex.isZero_double_X _ _ 2 (by decide) (by decide)).of_iso
      ((primitiveComplexNat X).extendXIso ComplexShape.embeddingUpNat (i := 2) rfl)
  have hd : K.d ((1 : ℕ) : ℤ) ((2 : ℕ) : ℤ) = 0 := by
    change Γ.map ((primitiveComplex X).d _ _) = 0
    rw [hzero.eq_of_tgt ((primitiveComplex X).d _ _) 0, Functor.map_zero]
  let x := (Γ.map ((HomologicalComplex.doubleXIso₁ _ _ (by decide)).inv ≫
    ((primitiveComplexNat X).extendXIso ComplexShape.embeddingUpNat (i := 1) rfl).inv)).hom θ'
  let c := (K.iCyclesIso ((1 : ℕ) : ℤ) ((2 : ℕ) : ℤ) (by simp) hd).inv x
  have hc : K.iCycles ((1 : ℕ) : ℤ) c = x :=
    ConcreteCategory.congr_hom
      (K.iCyclesIso_inv_hom_id ((1 : ℕ) : ℤ) ((2 : ℕ) : ℤ) (by simp) hd) x
  exact deRham_singular_assembly X z (K.homologyπ _ c) _
    (singular_homology_class_eq X θ' Ψ hΨ c hc)
    (deRham_homologyMap_primitive_eq X z θ' hz c hc)


theorem spec_deRham_singularIntegrationCochain_aux (X : Over (Spec ↧ℂ))
    [GrpObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (z : (filteredGlobalSections X).cycles ((1 : ℕ) : ℤ))
    (Ψ : AlgebraicTopology.Simplicial.Cocycle ℂ
      (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) 1)
    (hΨ : Ψ.1 = singularIntegrationCochain X (dim X.left) (cycleOneForm X z)) :
    fieldToDeRhamCohomology ℂ X 1 (singularToFieldCohomology ℂ X 1
        (Singular.cohomologyClass (TopCat.of (ComplexPoint X)) 1 Ψ)) =
      cycleDeRhamClass X z := by
  have hcl : globalHolomorphicDifferential X 1 (cycleOneForm X z) = 0 := by
    have h : cycleOneForm X z ∈ closedGlobalHolomorphicOneForms X := by
      rw [← spec_range_cycleOneForm X]
      exact ⟨z, rfl⟩
    exact h
  obtain ⟨θ', hθ'⟩ := spec_exists_globalPrimitive_of_closed_aux X _ hcl
  refine spec_deRham_singularToFieldCohomology_of_primitive_aux X z θ' hθ' Ψ ?_
  rw [hΨ]
  exact spec_globalCochainSection_singularIntegrationCochain_aux X _ θ' hθ'

end HodgeLean.Adapters
