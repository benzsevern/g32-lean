import HodgeLean.Adapters.HolomorphicFormsPullbackDefs
import HodgeLean.Adapters.HolomorphicOneForms
import HodgeLean.Foundations.Uniformization
import HodgeLean.Foundations.AppellHumbertSections

/-! # Proof obligations for holomorphic functions along the uniformization

One obligation per statement of `HodgeLean.Adapters.HolomorphicFormsPullback`. All eight are proved, by two parallel provers. -/

noncomputable section
open CategoryTheory AlgebraicGeometry ComplexPoint TopologicalSpace Opposite
open HodgeLean.Foundations
open Filter Topology

namespace HodgeLean.Adapters

open scoped CategoryTheory.MonObj in
theorem spec_eq_of_differentiable_comp_complexExponential_aux (X : Over (Spec ↧ℂ)) (d : ℕ)
    [GrpObj X] [IsCommMonObj X] [SmoothOfRelativeDimension d X.hom] [IsIntegral X.left]
    [IsProjective X.hom] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (g : ComplexPoint X → F)
    (hg : Differentiable ℂ (fun v ↦ g (complexExponential X d v).toMul))
    (x y : ComplexPoint X) : g x = g y := by
  let L := complexExponentialLattice X d
  have : IsZLattice ℝ L := isZLattice_complexExponentialLattice X d
  let b := (Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L
  set h : (Fin d → ℂ) → F := fun v ↦ g (complexExponential X d v).toMul with hh
  have hper : ∀ v, h v = h (ZSpan.fract b v) := by
    intro v
    have hm : (ZSpan.floor b v : Fin d → ℂ) ∈ L := by
      exact ((Module.Free.chooseBasis ℤ L).ofZLatticeBasis_span ℝ L).le (ZSpan.floor b v).2
    have h0 : complexExponential X d (ZSpan.floor b v) = 0 := hm
    simp only [hh, ZSpan.fract_apply]
    congr 2
    change complexExponentialHom X d v = complexExponentialHom X d (v - ZSpan.floor b v)
    rw [map_sub]
    change _ = _ - complexExponential X d _
    rw [h0, sub_zero]
  have hb : Bornology.IsBounded (Set.range h) := by
    have hc : IsCompact (closure (ZSpan.fundamentalDomain b)) :=
      (ZSpan.fundamentalDomain_isBounded b).isCompact_closure
    refine (hc.image hg.continuous).isBounded.subset ?_
    rintro _ ⟨v, rfl⟩
    exact ⟨_, subset_closure (ZSpan.fract_mem_fundamentalDomain b v), (hper v).symm⟩
  obtain ⟨v, hv⟩ := surjective_complexExponential X d (Additive.ofMul x)
  obtain ⟨w, hw⟩ := surjective_complexExponential X d (Additive.ofMul y)
  have := hg.apply_eq_apply_of_bounded hb v w
  simp only [hh, hv, hw] at this
  exact this

theorem spec_exists_nonconstant_periodic_aux :
    (∃ f : ℂ → ℂ, Differentiable ℂ f ∧ (∀ (n : ℤ) (z : ℂ), f (z + n) = f z) ∧
      f 0 ≠ f Complex.I) ∧
    (∃ f : ℂ → ℂ, ContDiff ℝ (⊤ : ℕ∞) f ∧
      (∀ (m n : ℤ) (z : ℂ), f (z + m + n * Complex.I) = f z) ∧ f 0 ≠ f (1 / 2)) := by
  refine ⟨⟨fun z ↦ Complex.exp (2 * Real.pi * Complex.I * z), ?_, ?_, ?_⟩,
    ⟨fun z ↦ Complex.exp (2 * Real.pi * Complex.I * (z.re : ℂ)), ?_, ?_, ?_⟩⟩
  · fun_prop
  · intro n z
    simp only [mul_add, Complex.exp_add]
    rw [show 2 * ↑Real.pi * Complex.I * (n : ℂ) = n * (2 * Real.pi * Complex.I) by ring,
      Complex.exp_int_mul_two_pi_mul_I, mul_one]
  · simp only [mul_zero, Complex.exp_zero]
    rw [show 2 * ↑Real.pi * Complex.I * Complex.I = ((-(2 * Real.pi) : ℝ) : ℂ) by
      push_cast; ring_nf; rw [Complex.I_sq]; ring, ← Complex.ofReal_exp]
    intro h
    have h1 : Real.exp (-(2 * Real.pi)) = 1 := by exact_mod_cast h.symm
    rw [Real.exp_eq_one_iff] at h1
    linarith [Real.pi_pos]
  · have : ContDiff ℝ (⊤ : ℕ∞) (fun z : ℂ ↦ ((z.re : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp Complex.reCLM.contDiff
    exact Complex.contDiff_exp.comp (contDiff_const.mul this)
  · intro m n z
    simp only [Complex.add_re, Complex.intCast_re, Complex.mul_re, Complex.intCast_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]
    push_cast
    rw [mul_add, Complex.exp_add,
      show 2 * ↑Real.pi * Complex.I * (m : ℂ) = m * (2 * Real.pi * Complex.I) by ring,
      Complex.exp_int_mul_two_pi_mul_I, mul_one]
  · simp only [Complex.zero_re, Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    rw [show ((1 / 2 : ℂ).re : ℂ) = 1 / 2 by simp,
      show 2 * ↑Real.pi * Complex.I * (1 / 2 : ℂ) = Real.pi * Complex.I by ring,
      Complex.exp_pi_mul_I]
    norm_num

open scoped CategoryTheory.MonObj in
theorem spec_eventually_differentiableAt_complexExponential_chart_aux (X : Over (Spec ↧ℂ))
    (d : ℕ) [GrpObj X] [IsCommMonObj X] [SmoothOfRelativeDimension d X.hom] :
    ∀ᶠ v in 𝓝 (0 : Fin d → ℂ),
      DifferentiableAt ℂ (fun w ↦ identityChart X d (complexExponential X d w).toMul) v := by
  set φ : (Fin d → ℂ) → (Fin d → ℂ) :=
    fun w ↦ identityChart X d (complexExponential X d w).toMul with hφ
  let mG := chartGroupLaw X d
  have hφ0 : φ 0 = 0 := by
    simp only [hφ, complexExponential_zero]
    exact identityChart_one X d
  have hd := hasFDerivAt_complexExponential_chart X d
  have hcont : ContinuousAt φ 0 := hd.continuousAt
  have hE : ∀ᶠ v in 𝓝 (0 : Fin d → ℂ),
      (complexExponential X d v).toMul ∈ (identityChart X d).source := by
    apply (continuous_complexExponential X d).continuousAt.tendsto.eventually
    change (identityChart X d).source ∈ 𝓝 (complexExponential X d 0).toMul
    rw [complexExponential_zero]
    exact (identityChart X d).open_source.mem_nhds (mem_localChart_source X d 1)
  have hA : ∀ᶠ v in 𝓝 (0 : Fin d → ℂ), AnalyticAt ℂ mG (φ v, 0) := by
    have ht : Tendsto (fun v ↦ (φ v, (0 : Fin d → ℂ))) (𝓝 0) (𝓝 (0, 0)) := by
      have := (hcont.prodMk (continuousAt_const (y := (0 : Fin d → ℂ)))).tendsto
      rwa [hφ0] at this
    exact ht.eventually (analyticAt_chartGroupLaw X d).eventually_analyticAt
  filter_upwards [hE, hA] with v hv hav
  let g : (Fin d → ℂ) → (Fin d → ℂ) := fun u ↦ mG (φ v, u)
  have hg : HasFDerivAt g (fderiv ℂ g (φ 0)) (φ 0) := by
    rw [hφ0]
    exact (hav.comp_of_eq (analyticAt_const.prod analyticAt_id) rfl).differentiableAt.hasFDerivAt
  have hcomp := (hg.restrictScalars ℝ).comp (0 : Fin d → ℂ) hd
  have heq : (fun w ↦ φ (v + w)) =ᶠ[𝓝 0] g ∘ φ := by
    filter_upwards [hE] with w hw
    simp only [g, mG, Function.comp_apply, chartGroupLaw, hφ]
    rw [(identityChart X d).left_inv hv, (identityChart X d).left_inv hw]
    congr 1
    change (complexExponentialHom X d (v + w)).toMul = _
    rw [map_add, toMul_add]
    rfl
  have h1 := (hcomp.congr_of_eventuallyEq heq)
  rw [ContinuousLinearMap.comp_id] at h1
  have h2 := (hasFDerivAt_comp_add_left (f := φ) v).mp h1
  rw [add_zero] at h2
  exact (hasFDerivAt_of_restrictScalars ℝ h2 rfl).differentiableAt

theorem spec_isLocallyConstant_globalHolomorphicFunction_aux (X : Over (Spec ↧ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] [CompactSpace (ComplexPoint X)]
    (f : (holomorphicFunctionSheaf X d).presheaf.obj (op ⊤)) :
    IsLocallyConstant f.1 := by
  have : CompactSpace (⊤ : Opens (TopCat.of (ComplexPoint X))) :=
    isCompact_iff_compactSpace.mp (by simpa using isCompact_univ (X := ComplexPoint X))
  exact ((holomorphicFunctionSheaf_section_analytic X d f).mdifferentiable
    (by simp)).isLocallyConstant

/-- On each open, `holomorphicFunctionsToZeroForms` is bijective: every degree-`0` Kähler form is a
function, and a function whose `0`-form vanishes in every chart is zero. -/
theorem holomorphicFunctionsToZeroForms_app_bijective (X : Over (Spec ↧ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) :
    Function.Bijective ((holomorphicFunctionsToZeroForms X d).app U) := by
  constructor
  · rw [injective_iff_map_eq_zero ((holomorphicFunctionsToZeroForms X d).app U).hom]
    intro (a : OpenHolomorphicFunctions X d U) ha
    change Submodule.Quotient.mk
      (Algebra.DeRham.ofFunction ℂ (OpenHolomorphicFunctions X d U) a) = 0 at ha
    rw [Submodule.Quotient.mk_eq_zero] at ha
    refine Subtype.ext (funext fun x ↦ ?_)
    let e := extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) x.1
    have hxsource : x.1 ∈ e.source := mem_extChartAt_source x.1
    have hxe : e x.1 ∈ chartSectionDomain X d U x.1 := by
      refine ⟨mem_extChartAt_target x.1, ?_⟩
      change e.symm (e x.1) ∈ U.unop
      rw [e.left_inv hxsource]
      exact x.2
    have heval := (mem_chartEvaluationKernel_iff X d U 0 _).1 ha x.1 (e x.1) hxe
    rw [Algebra.DeRham.ofFunction_apply, chartEvaluation_mk X d U x.1 0 _ _ hxe] at heval
    have hcoeff := congrArg
      (fun f : (Fin d → ℂ) [⋀^Fin 0]→L[ℂ] ℂ ↦ f Fin.elim0) heval
    simp only [chartGeneratorEvaluation, chartSection_apply_of_mem X d U x.1 _ hxe] at hcoeff
    have hx : (⟨e.symm (e x.1), hxe.2⟩ : U.unop) = x := Subtype.ext (e.left_inv hxsource)
    rw [hx] at hcoeff
    simp at hcoeff
    exact hcoeff
  · intro z
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    have hw : w ∈ LinearMap.range (Algebra.DeRham.ofFunction ℂ (OpenHolomorphicFunctions X d U)) := by
      induction w using Algebra.DeRham.mk_induction with
      | mk a₀ v =>
        refine ⟨a₀, ?_⟩
        rw [Algebra.DeRham.ofFunction_apply, Subsingleton.elim v Fin.elim0]
      | zero => exact zero_mem _
      | add x y hx hy => exact add_mem hx hy
      | smul r x hx => exact Submodule.smul_mem _ r hx
    obtain ⟨a, rfl⟩ := hw
    exact ⟨a, rfl⟩

instance isIso_holomorphicFunctionsToZeroForms (X : Over (Spec ↧ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] : IsIso (holomorphicFunctionsToZeroForms X d) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro U
  exact (ConcreteCategory.isIso_iff_bijective _).2
    (holomorphicFunctionsToZeroForms_app_bijective X d U)

/-- The presheaf of holomorphic `0`-forms is already a sheaf. -/
theorem isSheaf_holomorphicDeRhamPresheaf_zero (X : Over (Spec ↧ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] :
    Presheaf.IsSheaf (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
      (holomorphicDeRhamPresheaf X d 0) := by
  refine (Presheaf.isSheaf_of_iso_iff (asIso (holomorphicFunctionsToZeroForms X d))).1 ?_
  rw [Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget AddCommGrpCat)]
  have h := (holomorphicFunctionSheaf X d).property
  rw [Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget CommRingCat)] at h
  exact h

theorem spec_globalHolomorphicFunctionToZeroForm_bijective_aux (X : Over (Spec ↧ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] :
    Function.Bijective (globalHolomorphicFunctionToZeroForm X d) := by
  have := isIso_toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
    (isSheaf_holomorphicDeRhamPresheaf_zero X d)
  exact ConcreteCategory.bijective_of_isIso ((holomorphicFunctionsToZeroForms X d ≫
    toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
      (holomorphicDeRhamPresheaf X d 0)).app (op ⊤))

/-- Two sections of a sheaf over `W` agree as soon as they agree under the assumption that `W` is
nonempty. -/
theorem sheaf_section_eq_of_nonempty {T : TopCat.{0}} (F : TopCat.Sheaf AddCommGrpCat T)
    (W : Opens T) (a b : F.1.obj (op W)) (h : ∀ w ∈ W, a = b) : a = b := by
  refine F.eq_of_locally_eq' (fun _ : W ↦ W) W (fun _ ↦ 𝟙 W)
    (fun w hw ↦ Opens.mem_iSup.2 ⟨⟨w, hw⟩, hw⟩) a b fun w ↦ ?_
  rw [h w.1 w.2]

theorem spec_globalHolomorphicFunctionToZeroForm_mem_range_aux (X : Over (Spec ↧ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom]
    (f : (holomorphicFunctionSheaf X d).presheaf.obj (op ⊤)) (hf : IsLocallyConstant f.1) :
    globalHolomorphicFunctionToZeroForm X d f ∈ Set.range
      ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
        (TopCat.of (ComplexPoint X))).map (constantsToHolomorphicDeRhamZeroSheaf X d)).hom := by
  let J := Opens.grothendieckTopology (TopCat.of (ComplexPoint X))
  let K := 𝓒ᵖ(↧(ComplexPoint X); ℂ)
  let P := holomorphicDeRhamPresheaf X d 0
  let η := constantsToHolomorphicDeRhamZero X d
  let φ := holomorphicFunctionsToZeroForms X d
  let Fsh : TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint X)) :=
    (presheafToSheaf J AddCommGrpCat).obj K
  let Gsh : TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint X)) :=
    (presheafToSheaf J AddCommGrpCat).obj P
  let u := toSheafify J K
  let g : ComplexPoint X → ℂ := fun x ↦ f.1 ⟨x, trivial⟩
  have hg : IsLocallyConstant g := hf.comp_continuous (by fun_prop)
  let U : ComplexPoint X → Opens (TopCat.of (ComplexPoint X)) :=
    fun x ↦ ⟨g ⁻¹' {g x}, hg.isOpen_fiber _⟩
  have hU : ∀ x y, y ∈ U x → g y = g x := fun _ _ hy ↦ hy
  have hres : ∀ {V W : Opens (TopCat.of (ComplexPoint X))} (i : W ⟶ V) (c : ℂ),
      Fsh.1.map i.op (u.app (op V) c) = u.app (op W) c := by
    intro V W i c
    rw [← ConcreteCategory.comp_apply, ← u.naturality]
    rfl
  let sf : ∀ x, Fsh.1.obj (op (U x)) := fun x ↦ u.app (op (U x)) (g x)
  have hcompat : TopCat.Presheaf.IsCompatible Fsh.1 U sf := by
    intro x y
    simp only [sf, hres]
    refine sheaf_section_eq_of_nonempty Fsh _ _ _ fun w hw ↦ ?_
    rw [← hU x w hw.1, ← hU y w hw.2]
  obtain ⟨s, hs, -⟩ := Fsh.existsUnique_gluing' U ⊤ (fun _ ↦ homOfLE le_top)
    (fun x _ ↦ Opens.mem_iSup.2 ⟨x, rfl⟩) sf hcompat
  refine ⟨s, ?_⟩
  change (sheafifyMap J η).app (op ⊤) s = (toSheafify J P).app (op ⊤) (φ.app (op ⊤) f)
  refine Gsh.eq_of_locally_eq' U ⊤ (fun _ ↦ homOfLE le_top)
    (fun x _ ↦ Opens.mem_iSup.2 ⟨x, rfl⟩) _ _ fun x ↦ ?_
  change Gsh.1.map _ _ = Gsh.1.map _ _
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    ← (sheafifyMap J η).naturality, ← (toSheafify J P).naturality,
    ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
  change (sheafifyMap J η).app _ (Fsh.1.map _ s) = _
  rw [hs x, ← ConcreteCategory.comp_apply, ← NatTrans.comp_app, ← toSheafify_naturality,
    NatTrans.comp_app, ConcreteCategory.comp_apply]
  congr 1
  let f' : ((holomorphicFunctionPresheaf X d ⋙ forget₂ CommRingCat RingCat ⋙
    forget₂ RingCat AddCommGrpCat).obj (op ⊤)) := f
  have hnat := ConcreteCategory.congr_hom (φ.naturality (homOfLE (le_top (a := U x))).op) f'
  change η.app _ (g x) = P.map _ (φ.app _ f')
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hnat
  rw [← hnat]
  change Submodule.Quotient.mk (Algebra.DeRham.ofFunction ℂ _ (algebraMap ℂ _ (g x))) =
    Submodule.Quotient.mk (Algebra.DeRham.ofFunction ℂ _ _)
  congr 2
  exact Subtype.ext (funext fun y ↦ (hU x y.1 y.2).symm)

theorem spec_zeroForms_mem_range_constants_of_compactSpace_aux (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [CompactSpace (ComplexPoint X)] :
    ∀ f : GlobalHolomorphicForm X 0, f ∈ Set.range
      ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
        (TopCat.of (ComplexPoint X))).map
          (constantsToHolomorphicDeRhamZeroSheaf X (dim X.left))).hom := by
  intro f
  obtain ⟨g, rfl⟩ := (spec_globalHolomorphicFunctionToZeroForm_bijective_aux X (dim X.left)).2 f
  exact spec_globalHolomorphicFunctionToZeroForm_mem_range_aux X (dim X.left) g
    (spec_isLocallyConstant_globalHolomorphicFunction_aux X (dim X.left) g)

theorem spec_cycleDeRhamClass_injective_of_isProjective_aux (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    Function.Injective (cycleDeRhamClass X) :=
  spec_cycleDeRhamClass_injective_of_constant X
    (spec_zeroForms_mem_range_constants_of_compactSpace_aux X)

end HodgeLean.Adapters
