import HodgeLean.Adapters.HolomorphicFormValuesDefs
import HodgeConjecture.Lemmas.AlgebraicGeometry.Hodge.HolomorphicPoincare

/-! # Proof obligations for pointwise values of holomorphic forms and their pullback along `exp`

One obligation per statement of `HodgeLean.Adapters.HolomorphicFormValues`. All nine are proved, by two parallel provers. -/

noncomputable section
open CategoryTheory AlgebraicGeometry ComplexPoint TopologicalSpace Opposite
open HodgeLean.Foundations
open scoped Manifold

namespace HodgeLean.Adapters

/-- The value on the presheaf stalk of the germ of a presheaf form is its chart evaluation. -/
theorem presheafFormStalkValue_germ (X : Over (Spec ↧ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] (p : ℕ) (U : Opens (TopCat.of (ComplexPoint X)))
    (x : ComplexPoint X) (hx : x ∈ U)
    (ω : Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d (op U)) p) :
    presheafFormStalkValue X d x p
        ((holomorphicDeRhamPresheaf X d p).germ U x hx (Submodule.Quotient.mk ω)) =
      chartEvaluation X d (op U) x p ω (extChartAt 𝓘(ℂ, Fin d → ℂ) x x) := by
  change ((holomorphicDeRhamPresheaf X d p).germ U x hx ≫ presheafFormStalkValue X d x p)
    (Submodule.Quotient.mk ω) = _
  rw [TopCat.Presheaf.germ, presheafFormStalkValue]
  erw [Limits.colimit.ι_desc]
  rfl

theorem spec_formStalkValue_germ_toSheafify_aux (X : Over (Spec ↧ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] (p : ℕ) (U : Opens (TopCat.of (ComplexPoint X)))
    (x : ComplexPoint X) (hx : x ∈ U)
    (ω : Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d (op U)) p) :
    formStalkValue X d x p ((holomorphicDeRhamSheaf X d p).presheaf.germ U x hx
      ((toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
        (holomorphicDeRhamPresheaf X d p)).app (op U) (Submodule.Quotient.mk ω))) =
      chartEvaluation X d (op U) x p ω (extChartAt 𝓘(ℂ, Fin d → ℂ) x x) := by
  have := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat
      (holomorphicDeRhamPresheaf X d p)
  have h := TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx
    (toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
      (holomorphicDeRhamPresheaf X d p)) (Submodule.Quotient.mk ω)
  erw [← h]
  have key : ∀ y, formStalkValue X d x p ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      (toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
        (holomorphicDeRhamPresheaf X d p)) y) = presheafFormStalkValue X d x p y := by
    intro y
    change ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      (toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
        (holomorphicDeRhamPresheaf X d p)) ≫ formStalkValue X d x p) y = _
    rw [formStalkValue]
    erw [IsIso.hom_inv_id_assoc]
    rfl
  exact (key _).trans (presheafFormStalkValue_germ X d p U x hx ω)

theorem spec_exists_local_representative_aux (X : Over (Spec ↧ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] (p : ℕ)
    (θ : (holomorphicDeRhamSheaf X d p).presheaf.obj (op ⊤)) (x : ComplexPoint X) :
    ∃ (U : Opens (TopCat.of (ComplexPoint X))) (_ : x ∈ U)
      (ω : Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d (op U)) p),
      (holomorphicDeRhamSheaf X d p).presheaf.map (homOfLE le_top).op θ =
        (toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
          (holomorphicDeRhamPresheaf X d p)).app (op U) (Submodule.Quotient.mk ω) := by
  have hS := Presheaf.imageSieve_mem (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
    (toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
      (holomorphicDeRhamPresheaf X d p)) θ
  obtain ⟨V, f, ⟨t, ht⟩, hxV⟩ := hS x trivial
  obtain ⟨ω, rfl⟩ := Submodule.Quotient.mk_surjective _ t
  refine ⟨V, hxV, ω, ?_⟩
  rw [ht]
  rfl

/-- The value of a global form at a point of an open on which it is represented by a presheaf
form is the chart evaluation of that form, in the chart at the point. -/
theorem globalFormValue_eq_chartEvaluation_self (X : Over (Spec ↧ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] (p : ℕ)
    (θ : (holomorphicDeRhamSheaf X d p).presheaf.obj (op ⊤))
    (U : Opens (TopCat.of (ComplexPoint X)))
    (ω : Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d (op U)) p)
    (hω : (holomorphicDeRhamSheaf X d p).presheaf.map (homOfLE le_top).op θ =
      (toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
        (holomorphicDeRhamPresheaf X d p)).app (op U) (Submodule.Quotient.mk ω))
    (x : ComplexPoint X) (hx : x ∈ U) :
    globalFormValue X d p x θ =
      chartEvaluation X d (op U) x p ω (extChartAt 𝓘(ℂ, Fin d → ℂ) x x) := by
  have hgerm : (holomorphicDeRhamSheaf X d p).presheaf.germ ⊤ x trivial θ =
      (holomorphicDeRhamSheaf X d p).presheaf.germ U x hx
        ((holomorphicDeRhamSheaf X d p).presheaf.map (homOfLE le_top).op θ) :=
    (TopCat.Presheaf.germ_res_apply _ _ _ _ _).symm
  change formStalkValue X d x p ((holomorphicDeRhamSheaf X d p).presheaf.germ ⊤ x trivial θ) = _
  rw [hgerm, hω, spec_formStalkValue_germ_toSheafify_aux]

theorem spec_globalFormValue_eq_chartEvaluation_aux (X : Over (Spec ↧ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] (p : ℕ)
    (θ : (holomorphicDeRhamSheaf X d p).presheaf.obj (op ⊤))
    (U : Opens (TopCat.of (ComplexPoint X)))
    (ω : Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d (op U)) p)
    (hω : (holomorphicDeRhamSheaf X d p).presheaf.map (homOfLE le_top).op θ =
      (toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
        (holomorphicDeRhamPresheaf X d p)).app (op U) (Submodule.Quotient.mk ω))
    (z x : ComplexPoint X) (hx : x ∈ U)
    (hxz : x ∈ (extChartAt 𝓘(ℂ, Fin d → ℂ) z).source) :
    globalFormValue X d p x θ =
      (chartEvaluation X d (op U) z p ω (extChartAt 𝓘(ℂ, Fin d → ℂ) z x)).compContinuousLinearMap
        (fderiv ℂ (fixedChartTransition X d z x) (extChartAt 𝓘(ℂ, Fin d → ℂ) x x)) := by
  rw [globalFormValue_eq_chartEvaluation_self X d p θ U ω hω x hx]
  have hyz : (extChartAt 𝓘(ℂ, Fin d → ℂ) x).symm (extChartAt 𝓘(ℂ, Fin d → ℂ) x x) ∈
      (extChartAt 𝓘(ℂ, Fin d → ℂ) z).source := by
    rw [extChartAt_to_inv]
    exact hxz
  rw [chartEvaluation_fixedChartTransition X d (op U) z x p ω
    (extChartAt_self_mem_chartSectionDomain X d (op U) hx) hyz]
  have hT : fixedChartTransition X d z x (extChartAt 𝓘(ℂ, Fin d → ℂ) x x) =
      extChartAt 𝓘(ℂ, Fin d → ℂ) z x := by
    change (extChartAt 𝓘(ℂ, Fin d → ℂ) z)
      ((extChartAt 𝓘(ℂ, Fin d → ℂ) x).symm (extChartAt 𝓘(ℂ, Fin d → ℂ) x x)) = _
    rw [extChartAt_to_inv]
  rw [hT]

theorem spec_eq_zero_of_globalFormValue_eq_zero_aux (X : Over (Spec ↧ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] (p : ℕ)
    (θ : (holomorphicDeRhamSheaf X d p).presheaf.obj (op ⊤))
    (hθ : ∀ x, globalFormValue X d p x θ = 0) : θ = 0 := by
  apply TopCat.Presheaf.section_ext (holomorphicDeRhamSheaf X d p) ⊤ θ 0
  intro x _
  obtain ⟨U, hxU, ω, hω⟩ := spec_exists_local_representative_aux X d p θ x
  have hmk : (Submodule.Quotient.mk ω : HolomorphicForm X d (op U) p) = 0 := by
    rw [Submodule.Quotient.mk_eq_zero, mem_chartEvaluationKernel_iff]
    intro z y hy
    have hx'U : (extChartAt 𝓘(ℂ, Fin d → ℂ) z).symm y ∈ U := hy.2
    rw [chartEvaluation_fixedChartTransition X d (op U)
      ((extChartAt 𝓘(ℂ, Fin d → ℂ) z).symm y) z p ω hy (mem_extChartAt_source _)]
    have h0 := hθ ((extChartAt 𝓘(ℂ, Fin d → ℂ) z).symm y)
    rw [globalFormValue_eq_chartEvaluation_self X d p θ U ω hω _ hx'U] at h0
    change (chartEvaluation X d (op U) _ p ω (extChartAt 𝓘(ℂ, Fin d → ℂ)
      ((extChartAt 𝓘(ℂ, Fin d → ℂ) z).symm y) ((extChartAt 𝓘(ℂ, Fin d → ℂ) z).symm y))).compContinuousLinearMap
        _ = 0
    rw [h0]
    exact ContinuousAlternatingMap.ext fun v ↦ by
      simp [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  have hgerm : (holomorphicDeRhamSheaf X d p).presheaf.germ ⊤ x trivial θ =
      (holomorphicDeRhamSheaf X d p).presheaf.germ U x hxU
        ((holomorphicDeRhamSheaf X d p).presheaf.map (homOfLE le_top).op θ) :=
    (TopCat.Presheaf.germ_res_apply _ _ _ _ _).symm
  rw [hgerm, hω, hmk, map_zero]
  erw [map_zero, map_zero]

open scoped CategoryTheory.MonObj in
theorem spec_mfderiv_complexExponential_zero_aux (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X]
    [IsCommMonObj X] [SmoothOfRelativeDimension d X.hom] (u : Fin d → ℂ) :
    mfderiv 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) (fun w ↦ (complexExponential X d w).toMul) 0 u =
      u := by
  set E : (Fin d → ℂ) → ComplexPoint X := fun v ↦ (complexExponential X d v).toMul with hE
  have hE0 : E 0 = 1 := by
    simp only [hE, complexExponential_zero]
    rfl
  have hd := (spec_eventually_differentiableAt_complexExponential_chart X d).self_of_nhds
  have heq : writtenInExtChartAt 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) 0 E =
      fun w ↦ identityChart X d (E w) + localChart X d 1 1 := by
    funext w
    simp only [writtenInExtChartAt, extChartAt, OpenPartialHomeomorph.extend,
      chartAt_self_eq, Function.comp_apply, hE0]
    change localChart X d 1 (E w) = (localChart X d 1 (E w) - localChart X d 1 1) + _
    abel
  rw [(spec_mdifferentiable_complexExponential X d 0).mfderiv, heq]
  simp only [ModelWithCorners.range_eq_univ, fderivWithin_univ, fderiv_add_const]
  have hR := hd.hasFDerivAt.restrictScalars ℝ
  have he := hR.unique (hasFDerivAt_complexExponential_chart X d)
  exact DFunLike.congr_fun he u

/-- The manifold derivative of `exp` at `v` is the derivative of `exp` read in the chart at
`exp v`. -/
theorem mfderiv_complexExponential_eq_fderiv (X : Over (Spec ↧ℂ)) (d : ℕ)
    [GrpObj X] [IsCommMonObj X] [SmoothOfRelativeDimension d X.hom] (v : Fin d → ℂ) :
    mfderiv 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) (fun u ↦ (complexExponential X d u).toMul) v =
      fderiv ℂ (fun u ↦ extChartAt 𝓘(ℂ, Fin d → ℂ) (complexExponential X d v).toMul
        (complexExponential X d u).toMul) v := by
  rw [(spec_mdifferentiable_complexExponential X d v).mfderiv]
  simp only [ModelWithCorners.range_eq_univ, fderivWithin_univ]
  rfl

open Filter Topology in
open scoped ContDiff in
theorem spec_differentiable_expPullback_aux (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X]
    [IsCommMonObj X] [SmoothOfRelativeDimension d X.hom]
    (θ : (holomorphicDeRhamSheaf X d 1).presheaf.obj (op ⊤)) :
    Differentiable ℂ (expPullback X d θ) := by
  intro v₀
  set E : (Fin d → ℂ) → ComplexPoint X := fun u ↦ (complexExponential X d u).toMul with hE
  set x₀ := E v₀ with hx₀
  obtain ⟨U, hx₀U, η, hη⟩ := spec_exists_local_representative_aux X d 1 θ x₀
  set e₀ := extChartAt 𝓘(ℂ, Fin d → ℂ) x₀ with he₀
  set φ : (Fin d → ℂ) → (Fin d → ℂ) := fun u ↦ e₀ (E u) with hφ
  set B := chartEvaluation X d (op U) x₀ 1 η with hB
  set J := (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℂ) (E := Fin d → ℂ) (F := ℂ)
    (ι := Fin 1) 0).symm with hJ
  have hEc : Continuous E := continuous_complexExponential X d
  have hφs : ContDiffAt ℂ ω φ v₀ := by
    have h := spec_contMDiff_complexExponential X d v₀
    rw [contMDiffAt_iff] at h
    have h2 := h.2
    simp only [extChartAt_model_space_eq_id, PartialEquiv.refl_symm, PartialEquiv.refl_coe,
      Function.comp_id, ModelWithCorners.range_eq_univ, contDiffWithinAt_univ] at h2
    exact h2
  have hφd : DifferentiableAt ℂ φ v₀ := hφs.differentiableAt (by simp)
  have hDφ : DifferentiableAt ℂ (fderiv ℂ φ) v₀ :=
    (hφs.fderiv_right (m := 1) le_top).differentiableAt (by simp)
  have hBd : DifferentiableAt ℂ (fun v ↦ B (φ v)) v₀ :=
    ((analyticOnNhd_chartEvaluation X d (op U) x₀ 1 η (φ v₀)
      (extChartAt_self_mem_chartSectionDomain X d (op U) hx₀U)).differentiableAt).comp v₀ hφd
  have hmain : DifferentiableAt ℂ (fun v ↦ (J (B (φ v))).comp (fderiv ℂ φ v)) v₀ :=
    have hJB : DifferentiableAt ℂ (fun v ↦ J (B (φ v))) v₀ :=
      (J.toContinuousLinearEquiv.differentiableAt (x := B (φ v₀))).comp v₀ hBd
    hJB.clm_comp hDφ
  refine hmain.congr_of_eventuallyEq ?_
  have hW : (U : Set (ComplexPoint X)) ∩ e₀.source ∈ 𝓝 x₀ :=
    inter_mem (U.isOpen.mem_nhds hx₀U) (extChartAt_source_mem_nhds x₀)
  filter_upwards [hEc.continuousAt.preimage_mem_nhds hW] with v hv
  obtain ⟨hvU, hvs⟩ := hv
  set x := E v with hx
  have hg : DifferentiableAt ℂ (fun u ↦ extChartAt 𝓘(ℂ, Fin d → ℂ) x (E u)) v := by
    have h := (spec_mdifferentiable_complexExponential X d v)
    rw [mdifferentiableAt_iff] at h
    have h2 := h.2
    simp only [extChartAt_model_space_eq_id, PartialEquiv.refl_symm, PartialEquiv.refl_coe,
      Function.comp_id, ModelWithCorners.range_eq_univ, differentiableWithinAt_univ,
      writtenInExtChartAt] at h2
    exact h2
  have hF : DifferentiableAt ℂ (fixedChartTransition X d x₀ x) (extChartAt 𝓘(ℂ, Fin d → ℂ) x x) := by
    refine (analyticAt_fixedChartTransition X d x₀ x ?_).differentiableAt
    rw [OpenPartialHomeomorph.trans_source]
    refine ⟨(localChart X d x).map_source (mem_localChart_source X d x), ?_⟩
    change (localChart X d x).symm (localChart X d x x) ∈ (localChart X d x₀).source
    rw [(localChart X d x).left_inv (mem_localChart_source X d x)]
    have h := hvs
    rw [he₀, extChartAt_source] at h
    exact h
  have heq : φ =ᶠ[𝓝 v] fixedChartTransition X d x₀ x ∘
      (fun u ↦ extChartAt 𝓘(ℂ, Fin d → ℂ) x (E u)) := by
    filter_upwards [hEc.continuousAt.preimage_mem_nhds
      (extChartAt_source_mem_nhds (I := 𝓘(ℂ, Fin d → ℂ)) x)] with u hu
    simp only [Function.comp_apply, fixedChartTransition, hφ, he₀]
    rw [(extChartAt 𝓘(ℂ, Fin d → ℂ) x).left_inv hu]
  have hchain : fderiv ℂ φ v = (fderiv ℂ (fixedChartTransition X d x₀ x)
      (extChartAt 𝓘(ℂ, Fin d → ℂ) x x)).comp
        (fderiv ℂ (fun u ↦ extChartAt 𝓘(ℂ, Fin d → ℂ) x (E u)) v) := by
    rw [heq.fderiv_eq]
    exact fderiv_comp v hF hg
  have h3 := spec_globalFormValue_eq_chartEvaluation_aux X d 1 θ U η hη x₀ x hvU hvs
  ext1 u
  unfold expPullback
  rw [mfderiv_complexExponential_eq_fderiv]
  change globalFormValue X d 1 x θ
      (fun _ ↦ fderiv ℂ (fun u ↦ extChartAt 𝓘(ℂ, Fin d → ℂ) x (E u)) v u) =
    J (B (φ v)) (fderiv ℂ φ v u)
  rw [h3, hchain]
  rfl

open scoped CategoryTheory.MonObj in
/-- Translation by a period does not change `exp`, nor its derivative in a fixed chart. -/
theorem fderiv_chart_complexExponential_eq_of_eq (X : Over (Spec ↧ℂ)) (d : ℕ)
    [GrpObj X] [IsCommMonObj X] [SmoothOfRelativeDimension d X.hom] (x : ComplexPoint X)
    (v w : Fin d → ℂ) (h : complexExponential X d v = complexExponential X d w) :
    fderiv ℂ (fun u ↦ extChartAt 𝓘(ℂ, Fin d → ℂ) x (complexExponential X d u).toMul) v =
      fderiv ℂ (fun u ↦ extChartAt 𝓘(ℂ, Fin d → ℂ) x (complexExponential X d u).toMul) w := by
  have hadd : ∀ a b, (complexExponential X d (a + b)).toMul =
      (complexExponential X d a).toMul * (complexExponential X d b).toMul := fun a b ↦ by
    change (complexExponentialHom X d (a + b)).toMul =
      (complexExponentialHom X d a).toMul * (complexExponentialHom X d b).toMul
    rw [map_add, toMul_add]
  have hl : (complexExponential X d (w - v)).toMul = 1 := by
    have := hadd v (w - v)
    rw [add_sub_cancel, ← h] at this
    exact mul_eq_left.mp this.symm
  have hfun : (fun u ↦ extChartAt 𝓘(ℂ, Fin d → ℂ) x (complexExponential X d u).toMul) =
      fun u ↦ extChartAt 𝓘(ℂ, Fin d → ℂ) x (complexExponential X d (u + (w - v))).toMul := by
    funext u
    rw [hadd, hl, mul_one]
  conv_lhs => rw [hfun]
  rw [fderiv_comp_add_right (f := fun u ↦ extChartAt 𝓘(ℂ, Fin d → ℂ) x
    (complexExponential X d u).toMul), add_sub_cancel]

theorem spec_expPullback_eq_of_complexExponential_eq_aux (X : Over (Spec ↧ℂ)) (d : ℕ)
    [GrpObj X] [IsCommMonObj X] [SmoothOfRelativeDimension d X.hom]
    (θ : (holomorphicDeRhamSheaf X d 1).presheaf.obj (op ⊤)) (v w : Fin d → ℂ)
    (h : complexExponential X d v = complexExponential X d w) :
    expPullback X d θ v = expPullback X d θ w := by
  unfold expPullback
  rw [mfderiv_complexExponential_eq_fderiv, mfderiv_complexExponential_eq_fderiv, h,
    fderiv_chart_complexExponential_eq_of_eq X d _ v w h]

theorem spec_expPullback_eq_expPullback_zero_aux (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X]
    [IsCommMonObj X] [SmoothOfRelativeDimension d X.hom] [IsIntegral X.left]
    [IsProjective X.hom] (θ : (holomorphicDeRhamSheaf X d 1).presheaf.obj (op ⊤))
    (v : Fin d → ℂ) : expPullback X d θ v = expPullback X d θ 0 := by
  classical
  let h := expPullback X d θ
  let g : ComplexPoint X → ((Fin d → ℂ) →L[ℂ] ℂ) := fun x ↦
    if hx : ∃ u, (complexExponential X d u).toMul = x then h hx.choose else 0
  have hgh : (fun u ↦ g (complexExponential X d u).toMul) = h := by
    funext u
    have hx : ∃ u', (complexExponential X d u').toMul = (complexExponential X d u).toMul :=
      ⟨u, rfl⟩
    simp only [g, hx, ↓reduceDIte]
    exact spec_expPullback_eq_of_complexExponential_eq_aux X d θ _ _
      (Additive.toMul.injective hx.choose_spec)
  have hd : Differentiable ℂ (fun u ↦ g (complexExponential X d u).toMul) := by
    rw [hgh]
    exact spec_differentiable_expPullback_aux X d θ
  have := spec_eq_of_differentiable_comp_complexExponential X d g hd
    (complexExponential X d v).toMul (complexExponential X d 0).toMul
  exact (congrFun hgh v).symm.trans (this.trans (congrFun hgh 0))

open scoped CategoryTheory.MonObj in
/-- The inverse of the identity chart is the inverse of upstream's chart at `1`, shifted. -/
theorem identityChart_symm_apply_eq (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X]
    [SmoothOfRelativeDimension d X.hom] (y : Fin d → ℂ) :
    (identityChart X d).symm y = (localChart X d 1).symm (y + localChart X d 1 1) := by
  simp [identityChart]

open Filter Topology in
open scoped CategoryTheory.MonObj in
/-- The derivative of `exp` at `v`, read in the chart at `exp v`, has a right inverse: near `v`,
`exp = (exp v * ·) ∘ exp ∘ (· - v)`, the derivative of `exp` at `0` in the identity chart is the
identity, and left translation by `exp v` read in charts has the differentiable right inverse
given by left translation by `(exp v)⁻¹`. -/
theorem exists_fderiv_chart_complexExponential_comp_eq_id (X : Over (Spec ↧ℂ)) (d : ℕ)
    [GrpObj X] [IsCommMonObj X] [SmoothOfRelativeDimension d X.hom] (v : Fin d → ℂ) :
    ∃ M : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ),
      (fderiv ℂ (fun u ↦ extChartAt 𝓘(ℂ, Fin d → ℂ) (complexExponential X d v).toMul
        (complexExponential X d u).toMul) v).comp M = ContinuousLinearMap.id ℂ _ := by
  set a : ComplexPoint X := (complexExponential X d v).toMul with ha
  set E : (Fin d → ℂ) → ComplexPoint X := fun u ↦ (complexExponential X d u).toMul with hE
  set ea := extChartAt 𝓘(ℂ, Fin d → ℂ) a with hea
  set c : Fin d → ℂ := localChart X d 1 1 with hc
  set φ : (Fin d → ℂ) → (Fin d → ℂ) := fun s ↦ identityChart X d (E s) with hφ
  set T : (Fin d → ℂ) → (Fin d → ℂ) := fun y ↦ ea (a * (identityChart X d).symm y) with hT
  set T' : (Fin d → ℂ) → (Fin d → ℂ) := fun z ↦ identityChart X d (a⁻¹ * ea.symm z) with hT'
  have hE0 : E 0 = 1 := by
    simp only [hE, complexExponential_zero]
    rfl
  have hadd : ∀ s t, E (s + t) = E s * E t := fun s t ↦ by
    change (complexExponentialHom X d (s + t)).toMul =
      (complexExponentialHom X d s).toMul * (complexExponentialHom X d t).toMul
    rw [map_add, toMul_add]
  have hφ0 : φ 0 = 0 := by
    simp only [hφ, hE0]
    exact identityChart_one X d
  have hφd : HasFDerivAt φ (ContinuousLinearMap.id ℂ (Fin d → ℂ)) 0 := by
    have hd := (spec_eventually_differentiableAt_complexExponential_chart X d).self_of_nhds
    have he := (hd.hasFDerivAt.restrictScalars ℝ).unique (hasFDerivAt_complexExponential_chart X d)
    have hid : fderiv ℂ φ 0 = ContinuousLinearMap.id ℂ (Fin d → ℂ) := by
      ext1 u
      exact DFunLike.congr_fun he u
    rw [← hid]
    exact hd.hasFDerivAt
  have hTd : DifferentiableAt ℂ T 0 := by
    have hL := ((spec_contMDiff_mul_left X d a).mdifferentiable (by simp)) 1
    rw [mdifferentiableAt_iff] at hL
    have hL2 := hL.2
    simp only [ModelWithCorners.range_eq_univ, differentiableWithinAt_univ, writtenInExtChartAt,
      mul_one] at hL2
    have hW : DifferentiableAt ℂ (↑(extChartAt 𝓘(ℂ, Fin d → ℂ) a) ∘ (fun x ↦ a * x) ∘
        ↑(extChartAt 𝓘(ℂ, Fin d → ℂ) (1 : ComplexPoint X)).symm) (0 + c) := by
      rw [zero_add]
      exact hL2
    have hplus : DifferentiableAt ℂ (fun y : Fin d → ℂ ↦ y + c) 0 :=
      differentiableAt_id.add_const c
    refine (hW.comp 0 hplus).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y ↦ ?_)
    simp only [hT, Function.comp_apply, identityChart_symm_apply_eq]
    rfl
  have hT'd : DifferentiableAt ℂ T' (ea a) := by
    have hL := ((spec_contMDiff_mul_left X d a⁻¹).mdifferentiable (by simp)) a
    rw [mdifferentiableAt_iff] at hL
    have hL2 := hL.2
    simp only [ModelWithCorners.range_eq_univ, differentiableWithinAt_univ, writtenInExtChartAt,
      inv_mul_cancel] at hL2
    exact hL2.sub_const c
  have hT'a : T' (ea a) = 0 := by
    simp only [hT', hea, extChartAt_to_inv, inv_mul_cancel]
    exact identityChart_one X d
  have hTT' : T ∘ T' =ᶠ[𝓝 (ea a)] id := by
    have hcont : ContinuousAt (fun z ↦ a⁻¹ * ea.symm z) (ea a) :=
      (spec_contMDiff_mul_left X d a⁻¹).continuous.continuousAt.comp
        (continuousAt_extChartAt_symm a)
    have hmem : (identityChart X d).source ∈ 𝓝 (a⁻¹ * ea.symm (ea a)) := by
      simp only [hea, extChartAt_to_inv, inv_mul_cancel]
      exact (identityChart X d).open_source.mem_nhds (mem_localChart_source X d 1)
    filter_upwards [hcont.preimage_mem_nhds hmem, extChartAt_target_mem_nhds a] with z hz hzt
    simp only [Function.comp_apply, hT, hT', id]
    rw [(identityChart X d).left_inv hz, mul_inv_cancel_left, ea.right_inv hzt]
  have hEq : (fun u ↦ ea (E u)) =ᶠ[𝓝 v] T ∘ φ ∘ (fun u ↦ u - v) := by
    have hcont : ContinuousAt (fun u ↦ E (u - v)) v :=
      ((continuous_complexExponential X d).comp (continuous_sub_right v)).continuousAt
    have hmem : (identityChart X d).source ∈ 𝓝 (E (v - v)) := by
      rw [sub_self, hE0]
      exact (identityChart X d).open_source.mem_nhds (mem_localChart_source X d 1)
    filter_upwards [hcont.preimage_mem_nhds hmem] with u hu
    have haE : a = E v := rfl
    simp only [Function.comp_apply, hT, hφ]
    rw [(identityChart X d).left_inv hu, haE, ← hadd, add_sub_cancel]
  refine ⟨fderiv ℂ T' (ea a), ?_⟩
  have hT0 : HasFDerivAt T (fderiv ℂ T 0) (φ (v - v)) := by
    rw [sub_self, hφ0]
    exact hTd.hasFDerivAt
  have hφ' : HasFDerivAt φ (ContinuousLinearMap.id ℂ (Fin d → ℂ)) (v - v) := by
    rw [sub_self]
    exact hφd
  have hsub : HasFDerivAt (fun u : Fin d → ℂ ↦ u - v) (ContinuousLinearMap.id ℂ (Fin d → ℂ)) v :=
    (hasFDerivAt_id v).sub_const v
  have h4 := (hT0.comp v (hφ'.comp (f := fun u : Fin d → ℂ ↦ u - v) v hsub)).congr_of_eventuallyEq hEq
  rw [h4.fderiv]
  have h5 : HasFDerivAt (T ∘ T') ((fderiv ℂ T 0).comp (fderiv ℂ T' (ea a))) (ea a) := by
    have : HasFDerivAt T (fderiv ℂ T 0) (T' (ea a)) := by
      rw [hT'a]
      exact hTd.hasFDerivAt
    exact this.comp _ hT'd.hasFDerivAt
  have h6 := (h5.congr_of_eventuallyEq hTT'.symm).unique (hasFDerivAt_id (ea a))
  simpa only [ContinuousLinearMap.comp_id] using h6

theorem spec_eq_zero_of_expPullback_zero_eq_zero_aux (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X]
    [IsCommMonObj X] [SmoothOfRelativeDimension d X.hom] [IsIntegral X.left]
    [IsProjective X.hom] (θ : (holomorphicDeRhamSheaf X d 1).presheaf.obj (op ⊤))
    (hθ : expPullback X d θ 0 = 0) : θ = 0 := by
  have hcov : ∀ v, globalOneFormCovector X d θ (complexExponential X d v).toMul = 0 := by
    intro v
    obtain ⟨M, hM⟩ := exists_fderiv_chart_complexExponential_comp_eq_id X d v
    have h0 := (spec_expPullback_eq_expPullback_zero_aux X d θ v).trans hθ
    unfold expPullback at h0
    rw [mfderiv_complexExponential_eq_fderiv] at h0
    calc globalOneFormCovector X d θ (complexExponential X d v).toMul
        = (globalOneFormCovector X d θ (complexExponential X d v).toMul).comp
            ((fderiv ℂ (fun u ↦ extChartAt 𝓘(ℂ, Fin d → ℂ) (complexExponential X d v).toMul
              (complexExponential X d u).toMul) v).comp M) := by
          rw [hM, ContinuousLinearMap.comp_id]
      _ = 0 := by
          rw [← ContinuousLinearMap.comp_assoc, h0, ContinuousLinearMap.zero_comp]
  apply spec_eq_zero_of_globalFormValue_eq_zero_aux X d 1 θ
  intro x
  obtain ⟨v, hv⟩ := surjective_complexExponential X d (Additive.ofMul x)
  have hx : x = (complexExponential X d v).toMul := by
    rw [hv]
    rfl
  subst hx
  have h1 := congrArg (ContinuousAlternatingMap.ofSubsingleton ℂ (Fin d → ℂ) ℂ (0 : Fin 1))
    (hcov v)
  rw [globalOneFormCovector, Equiv.apply_symm_apply] at h1
  rw [h1]
  ext
  simp

end HodgeLean.Adapters
