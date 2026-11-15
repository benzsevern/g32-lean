import HodgeLean.Foundations.DolbeaultCurveDefs
import HodgeLean.Adapters.CurveStructureSheafVanishing

/-! # Proof obligations for the Dolbeault stage on `X(ℂ)` -/

noncomputable section
open CategoryTheory TopologicalSpace AlgebraicGeometry ComplexPoint
open scoped ContDiff Manifold
open HodgeLean.RealDefs HodgeLean.Adapters

namespace HodgeLean.Foundations

section Chart
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

lemma differentiableAt_comp_chartAt_symm {n : ℕ∞ω} (hn : n ≠ 0) {g : M → F} {y : M}
    (hg : ContMDiffAt 𝓘(𝕜, E) 𝓘(𝕜, F) n g y) :
    DifferentiableAt 𝕜 (g ∘ (chartAt E y).symm) (chartAt E y y) := by
  rw [contMDiffAt_iff] at hg
  have h := hg.2
  simp only [mfld_simps] at h
  exact (h.contDiffAt Filter.univ_mem).differentiableAt hn

lemma mfderiv_eq_fderiv_comp_chartAt_symm {g : M → F} {y : M}
    (hg : MDifferentiableAt 𝓘(𝕜, E) 𝓘(𝕜, F) g y) :
    mfderiv 𝓘(𝕜, E) 𝓘(𝕜, F) g y = fderiv 𝕜 (g ∘ (chartAt E y).symm) (chartAt E y y) := by
  rw [hg.mfderiv_abuse]
  simp only [writtenInExtChartAt, mfld_simps, fderivWithin_univ]
  rfl

end Chart

lemma exists_restrictScalars_eq_of_antiLinearPart_eq_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (L : E →L[ℝ] ℂ) (h : antiLinearPart L = 0) :
    ∃ L' : E →L[ℂ] ℂ, L'.restrictScalars ℝ = L := by
  have hI : ∀ v, L (Complex.I • v) = Complex.I * L v := by
    intro v
    have h1 := congrArg (fun T : E →L[ℝ] ℂ => T v) h
    simp only [antiLinearPart_apply, zero_apply, smul_eq_zero] at h1
    rcases h1 with h1 | h1
    · norm_num at h1
    · have h2 := congrArg (fun z => Complex.I * z) h1
      simp only [mul_add, ← mul_assoc, Complex.I_mul_I, mul_zero] at h2
      linear_combination -h2
  refine ⟨⟨⟨⟨L, L.map_add⟩, fun c v => ?_⟩, L.continuous⟩, rfl⟩
  simp only [RingHom.id_apply, smul_eq_mul]
  conv_lhs => rw [← Complex.re_add_im c, add_smul, mul_smul]
  rw [L.map_add, Complex.coe_smul, Complex.coe_smul, L.map_smul, L.map_smul, hI]
  simp only [Complex.real_smul]
  conv_rhs => rw [← Complex.re_add_im c]
  ring

section Sections

variable {X : Over (Spec ↧ℂ)} {d : ℕ} [SmoothOfRelativeDimension d X.hom]

lemma contMDiffAt_extendSection_complex {U : Opens (ComplexPoint X)}
    (f : C^ω⟮𝓘(ℂ, Fin d → ℂ), U; ℂ⟯) (x : U) :
    ContMDiffAt 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ) ω (extendSection f) x := by
  rw [← contMDiffAt_subtype_iff]
  have : (fun y : U => extendSection f y) = f := funext fun y => extendSection_of_mem _ y.2
  rw [this]
  exact f.contMDiff.contMDiffAt

lemma realDifferential_eq_fderiv {g : ComplexPoint X → ℂ} {y : ComplexPoint X}
    (hg : MDifferentiableAt 𝓘(ℝ, Fin d → ℂ) 𝓘(ℝ, ℂ) g y) :
    realDifferential X d g y =
      fderiv ℝ (g ∘ (chartAt (Fin d → ℂ) y).symm) (chartAt (Fin d → ℂ) y y) :=
  mfderiv_eq_fderiv_comp_chartAt_symm hg

lemma dbarSection_eq_zero_of_contMDiff {U : Opens (ComplexPoint X)}
    (f : C^∞⟮𝓘(ℝ, Fin d → ℂ), U; 𝓘(ℝ, ℂ), ℂ⟯)
    (hf : ContMDiff 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ) ω (f : U → ℂ)) : dbarSection X d f = 0 := by
  funext x
  have hR := contMDiffAt_extendSection f x
  have hC : ContMDiffAt 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ) ω (extendSection (f : U → ℂ)) x :=
    contMDiffAt_extendSection_complex ⟨f, hf⟩ x
  simp only [dbarSection, Pi.zero_apply]
  rw [realDifferential_eq_fderiv (hR.mdifferentiableAt (by simp)),
    (differentiableAt_comp_chartAt_symm (by simp) hC).fderiv_restrictScalars ℝ]
  exact antiLinearPart_restrictScalars _

end Sections

theorem spec_holomorphicToSmooth_comp_dbar_aux (X : Over (Spec ↧ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] :
    holomorphicToSmooth X d ≫ dbar X d = 0 := by
  apply Sheaf.hom_ext
  ext U f
  exact Subtype.ext (dbarSection_eq_zero_of_contMDiff _ f.2)

theorem spec_mono_holomorphicToSmooth_aux (X : Over (Spec ↧ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] :
    Mono (holomorphicToSmooth X d) := by
  have : Mono (holomorphicToSmooth X d).hom := by
    have (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) :
        Mono ((holomorphicToSmooth X d).hom.app U) := by
      rw [AddCommGrpCat.mono_iff_injective]
      intro f g h
      exact ContMDiffMap.ext fun x => congrArg (fun φ => φ.1 x) h
    exact NatTrans.mono_of_mono_app _
  exact Sheaf.Hom.mono_of_presheaf_mono _ _ _

section CauchyRiemann

variable {X : Over (Spec ↧ℂ)} [SmoothOfRelativeDimension 1 X.hom]

/-- Cauchy–Riemann in the chart at a point `x`: `∂̄ f = 0` gives complex derivatives of `f` read in
the chart at `x`, at every point of the chart's target lying over `U`. -/
lemma differentiableAt_comp_chartAt_symm_of_dbarSection_eq_zero {U : Opens (ComplexPoint X)}
    (f : C^∞⟮𝓘(ℝ, Fin 1 → ℂ), U; 𝓘(ℝ, ℂ), ℂ⟯) (hf : dbarSection X 1 f = 0) (x : ComplexPoint X)
    {w : Fin 1 → ℂ} (hw : w ∈ (chartAt (Fin 1 → ℂ) x).target)
    (hwU : (chartAt (Fin 1 → ℂ) x).symm w ∈ U) :
    DifferentiableAt ℂ (extendSection f ∘ (chartAt (Fin 1 → ℂ) x).symm) w := by
  set e := chartAt (Fin 1 → ℂ) x
  set y := e.symm w
  set e' := chartAt (Fin 1 → ℂ) y
  set g := extendSection (f : U → ℂ)
  have hRy := contMDiffAt_extendSection f ⟨y, hwU⟩
  -- the real derivative in the chart at `y` is complex-linear
  have hA : antiLinearPart (fderiv ℝ (g ∘ e'.symm) (e' y)) = 0 := by
    have h := congrFun hf ⟨y, hwU⟩
    simp only [dbarSection, Pi.zero_apply] at h
    rwa [realDifferential_eq_fderiv (hRy.mdifferentiableAt (by simp))] at h
  obtain ⟨L', hL'⟩ := exists_restrictScalars_eq_of_antiLinearPart_eq_zero _ hA
  -- the chart transition is holomorphic
  have hsrc : w ∈ (e.symm.trans e').source := by
    simp only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      Set.mem_inter_iff, Set.mem_preimage]
    exact ⟨hw, mem_chart_source _ y⟩
  have hT : DifferentiableAt ℂ (e' ∘ e.symm) w := by
    have h := (contDiffOn_localChart_transition X 1 x y).contDiffAt
      ((e.symm.trans e').open_source.mem_nhds hsrc)
    exact h.differentiableAt (by simp)
  have hTw : (e' ∘ e.symm) w = e' y := rfl
  have hG : DifferentiableAt ℝ (g ∘ e'.symm) ((e' ∘ e.symm) w) :=
    differentiableAt_comp_chartAt_symm (by simp) hRy
  have hcomp := hG.hasFDerivAt.comp w (hT.hasFDerivAt.restrictScalars ℝ)
  have heq : (g ∘ e'.symm) ∘ (e' ∘ e.symm) =ᶠ[nhds w] g ∘ e.symm := by
    filter_upwards [(e.symm.trans e').open_source.mem_nhds hsrc] with v hv
    simp only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      Set.mem_inter_iff, Set.mem_preimage] at hv
    simp only [Function.comp_apply, e'.left_inv hv.2]
  refine (hasFDerivAt_of_restrictScalars ℝ (hcomp.congr_of_eventuallyEq heq.symm)
    (f' := L' ∘L fderiv ℂ (e' ∘ e.symm) w) ?_).differentiableAt
  rw [hTw, ← hL']
  rfl

lemma analyticAt_comp_chartAt_symm_of_dbarSection_eq_zero {U : Opens (ComplexPoint X)}
    (f : C^∞⟮𝓘(ℝ, Fin 1 → ℂ), U; 𝓘(ℝ, ℂ), ℂ⟯) (hf : dbarSection X 1 f = 0) (x : U) :
    AnalyticAt ℂ (extendSection f ∘ (chartAt (Fin 1 → ℂ) (x : ComplexPoint X)).symm)
      (chartAt (Fin 1 → ℂ) (x : ComplexPoint X) x) := by
  set e := chartAt (Fin 1 → ℂ) (x : ComplexPoint X)
  set h := extendSection (f : U → ℂ) ∘ e.symm
  set V := e.target ∩ e.symm ⁻¹' U
  have hV : IsOpen V := e.isOpen_inter_preimage_symm U.isOpen
  have hxV : e x ∈ V := ⟨e.map_source (mem_chart_source _ _), by
    simp only [Set.mem_preimage, e.left_inv (mem_chart_source _ _)]; exact x.2⟩
  have hd : DifferentiableOn ℂ h V := fun w hw =>
    (differentiableAt_comp_chartAt_symm_of_dbarSection_eq_zero f hf x hw.1
      hw.2).differentiableWithinAt
  let φ := ContinuousLinearEquiv.funUnique (Fin 1) ℂ ℂ
  have hd' : DifferentiableOn ℂ (h ∘ φ.symm) (φ.symm ⁻¹' V) :=
    hd.comp φ.symm.differentiableOn (fun _ hz => hz)
  have hnhds : φ.symm ⁻¹' V ∈ nhds (φ (e x)) :=
    (hV.preimage φ.symm.continuous).mem_nhds (by simpa using hxV)
  have ha := (hd'.analyticAt hnhds).comp (φ.toContinuousLinearMap.analyticAt (e x))
  convert ha using 1
  funext z
  simp [h]

end CauchyRiemann

theorem spec_contMDiff_of_dbarSection_eq_zero_aux (X : Over (Spec ↧ℂ))
    [SmoothOfRelativeDimension 1 X.hom] {U : Opens (ComplexPoint X)}
    (f : C^∞⟮𝓘(ℝ, Fin 1 → ℂ), U; 𝓘(ℝ, ℂ), ℂ⟯) (hf : dbarSection X 1 f = 0) :
    ContMDiff 𝓘(ℂ, Fin 1 → ℂ) 𝓘(ℂ) ω (f : U → ℂ) := by
  intro x
  have : (fun y : U => extendSection f y) = f := funext fun y => extendSection_of_mem _ y.2
  rw [← this, contMDiffAt_subtype_iff, contMDiffAt_iff]
  refine ⟨(contMDiffAt_extendSection f x).continuousAt, ?_⟩
  simp only [mfld_simps]
  exact (analyticAt_comp_chartAt_symm_of_dbarSection_eq_zero f hf x).contDiffAt.contDiffWithinAt

theorem spec_exact_holomorphicToSmooth_dbar_aux (X : Over (Spec ↧ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] (hd : d = 1) :
    (ShortComplex.mk (holomorphicToSmooth X d) (dbar X d)
      (spec_holomorphicToSmooth_comp_dbar_aux X d)).Exact := by
  subst hd
  have := spec_mono_holomorphicToSmooth_aux X 1
  refine ShortComplex.exact_of_f_is_kernel _ (Limits.KernelFork.IsLimit.ofι _ _
    (fun {W} k hk => ⟨{
      app U := AddCommGrpCat.ofHom {
        toFun s := (⟨Subtype.val (k.hom.app U s), spec_contMDiff_of_dbarSection_eq_zero_aux X _
          (congrArg Subtype.val (congrArg (fun φ => φ.hom.app U s) hk))⟩ :
            C^ω⟮𝓘(ℂ, Fin 1 → ℂ), (Opposite.unop U : Opens (ComplexPoint X)); ℂ⟯)
        map_zero' := ContMDiffMap.ext fun x => by simp only [map_zero]; rfl
        map_add' a b := ContMDiffMap.ext fun x => by simp only [map_add]; rfl }
      naturality U V i := by
        ext s
        exact ContMDiffMap.ext fun x => congrArg (fun φ => φ.1 x)
          (congrArg (fun φ => φ s) (congrArg (fun ψ => ψ.hom) (k.hom.naturality i))) }⟩)
    (fun k hk => rfl) (fun k hk m hm => ?_))
  exact (cancel_mono (holomorphicToSmooth X 1)).1 hm

lemma chartEvaluation_ofFunction (X : Over (Spec ↧ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (x : ComplexPoint X) (a : OpenHolomorphicFunctions X d U) {y : Fin d → ℂ}
    (hy : y ∈ chartSectionDomain X d U x) :
    chartEvaluation X d U x 0 (Algebra.DeRham.ofFunction ℂ (OpenHolomorphicFunctions X d U) a) y =
      ContinuousAlternatingMap.constOfIsEmpty ℂ (Fin d → ℂ) (Fin 0) (chartSection X d U x a y) := by
  rw [Algebra.DeRham.ofFunction_apply, chartEvaluation_mk X d U x 0 _ _ hy]
  change chartSection X d U x a y • ContinuousAlternatingMap.wedgeCovectors ℂ (Fin d → ℂ) _ = _
  ext v
  simp

lemma ofFunction_surjective_zero {A : Type} [CommRing A] [Algebra ℂ A] :
    Function.Surjective (Algebra.DeRham.ofFunction ℂ A) := by
  intro θ
  induction θ using Algebra.DeRham.mk_induction with
  | mk a₀ v =>
      refine ⟨a₀, ?_⟩
      rw [Algebra.DeRham.ofFunction_apply]
      congr 1
      exact funext fun i => i.elim0
  | zero => exact ⟨0, map_zero _⟩
  | add x y hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      exact ⟨a + b, map_add _ _ _⟩
  | smul r x hx =>
      obtain ⟨a, rfl⟩ := hx
      exact ⟨r • a, map_smul _ _ _⟩

theorem spec_bijective_holomorphicForm_zero_aux (X : Over (Spec ↧ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) :
    Function.Bijective ((chartEvaluationKernel X d U 0).mkQ ∘ₗ
      Algebra.DeRham.ofFunction ℂ (OpenHolomorphicFunctions X d U)) := by
  refine ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro a ha
    rw [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      mem_chartEvaluationKernel_iff] at ha
    apply ContMDiffMap.ext
    intro x
    let e := extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) x.1
    have hxsource : x.1 ∈ e.source := mem_extChartAt_source x.1
    have hxe : e x.1 ∈ chartSectionDomain X d U x.1 := by
      refine ⟨mem_extChartAt_target x.1, ?_⟩
      change e.symm (e x.1) ∈ U.unop
      rw [e.left_inv hxsource]
      exact x.2
    have heval := ha x.1 (e x.1) hxe
    rw [chartEvaluation_ofFunction X d U x.1 a hxe, chartSection_apply_of_mem X d U x.1 a hxe]
      at heval
    have hx : (⟨e.symm (e x.1), hxe.2⟩ : (Opposite.unop U : Opens (ComplexPoint X))) = x :=
      Subtype.ext (e.left_inv hxsource)
    rw [hx] at heval
    have hcoeff := congrArg
      (fun f : (Fin d → ℂ) [⋀^Fin 0]→L[ℂ] ℂ ↦ f Fin.elim0) heval
    simp only [ContinuousAlternatingMap.constOfIsEmpty_apply] at hcoeff
    exact hcoeff
  · intro q
    obtain ⟨θ, rfl⟩ := Submodule.mkQ_surjective _ q
    obtain ⟨a, rfl⟩ := ofFunction_surjective_zero θ
    exact ⟨a, rfl⟩

theorem spec_nonempty_iso_holomorphicDeRham_zero_aux (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] :
    Nonempty (Ω•(X).X 0 ≅ holomorphicFunctionAddSheaf X (dim X.left)) := by
  let d := dim X.left
  let e : holomorphicFunctionAddPresheaf X d ≅ holomorphicDeRhamPresheaf X d 0 :=
    NatIso.ofComponents
      (fun U => (LinearEquiv.ofBijective _
        (spec_bijective_holomorphicForm_zero_aux X d U)).toAddEquiv.toAddCommGrpIso)
      (by
        intro U V i
        ext a
        change (chartEvaluationKernel X d V 0).mkQ (Algebra.DeRham.ofFunction ℂ _
            (holomorphicRestrictionAlgHom X d i a)) =
          holomorphicFormRestriction X d i 0
            ((chartEvaluationKernel X d U 0).mkQ (Algebra.DeRham.ofFunction ℂ _ a))
        exact congrArg (chartEvaluationKernel X d V 0).mkQ
          (Algebra.DeRham.map_ofFunction (f := holomorphicRestrictionAlgHom X d i)
            (a := (a : OpenHolomorphicFunctions X d U))).symm)
  refine ⟨(holomorphicDeRhamComplex X d).extendXIso ComplexShape.embeddingUpNat (i := 0) rfl ≪≫
    ?_⟩
  exact (presheafToSheaf _ _).mapIso e.symm ≪≫
    (sheafificationIso (holomorphicFunctionAddSheaf X d)).symm

theorem spec_subsingleton_hypercohomology_two_of_dbar_aux (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] (hd : dim X.left = 1)
    (hε : Epi (dbar X (dim X.left)))
    (hA : Subsingleton ℍ^2(X; (HomologicalComplex.single (AnalyticAdditiveSheaf X)
      (ComplexShape.up ℤ) 0).obj (smoothFunctionSheaf X (dim X.left))))
    (hB : Subsingleton ℍ^1(X; (HomologicalComplex.single (AnalyticAdditiveSheaf X)
      (ComplexShape.up ℤ) 0).obj (zeroOneFormSheaf X (dim X.left)))) :
    Subsingleton ℍ^2(X; holomorphicFormsShifted X 0) := by
  obtain ⟨e⟩ := spec_nonempty_iso_holomorphicDeRham_zero_aux X
  have hmono := spec_mono_holomorphicToSmooth_aux X (dim X.left)
  have hex := spec_exact_holomorphicToSmooth_dbar_aux X (dim X.left) hd
  have w : (e.hom ≫ holomorphicToSmooth X (dim X.left)) ≫ dbar X (dim X.left) = 0 := by
    rw [Category.assoc, spec_holomorphicToSmooth_comp_dbar_aux, Limits.comp_zero]
  refine spec_subsingleton_hypercohomology_two_of_shortExact X _ _ w ?_ hA hB
  have iso : ShortComplex.mk _ _ (spec_holomorphicToSmooth_comp_dbar_aux X (dim X.left)) ≅
      ShortComplex.mk _ _ w :=
    ShortComplex.isoMk e.symm (Iso.refl _) (Iso.refl _) (by simp) (by simp)
  have hex' : (ShortComplex.mk _ _ w).Exact := (ShortComplex.exact_iff_of_iso iso).1 hex
  exact ShortComplex.ShortExact.mk' hex' (mono_comp _ _) hε

theorem spec_cycleClassIsHodge_of_curve_of_dbar_aux (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [SmoothOfRelativeDimension 1 X.hom] [IsProjective X.hom]
    (hε : Epi (dbar X (dim X.left)))
    (hA : Subsingleton ℍ^2(X; (HomologicalComplex.single (AnalyticAdditiveSheaf X)
      (ComplexShape.up ℤ) 0).obj (smoothFunctionSheaf X (dim X.left))))
    (hB : Subsingleton ℍ^1(X; (HomologicalComplex.single (AnalyticAdditiveSheaf X)
      (ComplexShape.up ℤ) 0).obj (zeroOneFormSheaf X (dim X.left)))) :
    CycleClassIsHodge X :=
  spec_cycleClassIsHodge_of_curve X <| spec_subsingleton_hypercohomology_two_of_dbar_aux X
    (SmoothOfRelativeDimension.dim_eq X.hom 1) hε hA hB

/-- `v ↦ conj (v i)`: the conjugate of the `i`-th coordinate, a conjugate-linear functional. -/
lemma antiLinearPart_conj_proj {d : ℕ} (i : Fin d) :
    antiLinearPart ((Complex.conjCLE.toContinuousLinearMap.comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℂ) i))) =
      Complex.conjCLE.toContinuousLinearMap.comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℂ) i) := by
  ext v
  rw [antiLinearPart_apply]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.proj_apply, ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply,
    Pi.smul_apply, smul_eq_mul, map_mul, Complex.conj_I, Complex.real_smul]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

theorem spec_dbar_ne_zero_aux (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (hd : 0 < d) (x : ComplexPoint X) :
    dbar X d ≠ 0 := by
  intro h
  let i₀ : Fin d := ⟨0, hd⟩
  let L : (Fin d → ℂ) →L[ℝ] ℂ := Complex.conjCLE.toContinuousLinearMap.comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℂ) i₀)
  let c := chartAt (Fin d → ℂ) x
  let U : Opens (ComplexPoint X) := ⟨c.source, c.open_source⟩
  have hxU : x ∈ U := mem_chart_source _ x
  have hsm : ∀ y ∈ c.source,
      ContMDiffAt 𝓘(ℝ, Fin d → ℂ) 𝓘(ℝ, ℂ) ∞ (fun y => L (c y)) y := fun y hy =>
    (L.contDiff.contMDiff.contMDiffAt).comp y
      ((contMDiffOn_chart (I := 𝓘(ℝ, Fin d → ℂ)) (x := x)).contMDiffAt
        (c.open_source.mem_nhds hy))
  let f : C^∞⟮𝓘(ℝ, Fin d → ℂ), U; 𝓘(ℝ, ℂ), ℂ⟯ :=
    ⟨fun y => L (c y.1), fun y => contMDiffAt_subtype_iff.2 (hsm y.1 y.2)⟩
  have h0 : dbarSection X d f ⟨x, hxU⟩ = 0 := by
    have := congrArg (fun φ => (((φ : smoothFunctionSheaf X d ⟶ zeroOneFormSheaf X d).hom.app
      (Opposite.op U)) f).1 ⟨x, hxU⟩) h
    exact this
  have hext : extendSection f =ᶠ[nhds x] fun y => L (c y) := by
    filter_upwards [U.isOpen.mem_nhds hxU] with y hy
    rw [extendSection_of_mem _ hy]
    rfl
  have hdiff : realDifferential X d (extendSection f) x = L := by
    rw [realDifferential_congr hext]
    unfold realDifferential
    have hc : MDifferentiableAt 𝓘(ℝ, Fin d → ℂ) 𝓘(ℝ, Fin d → ℂ) c x :=
      mdifferentiableAt_atlas (I := 𝓘(ℝ, Fin d → ℂ)) (ChartedSpace.chart_mem_atlas _)
        (mem_chart_source _ x)
    have := mfderiv_comp (I' := 𝓘(ℝ, Fin d → ℂ)) (g := L) (f := c) x
      L.mdifferentiableAt hc
    rw [show (fun y => L (c y)) = L ∘ c from rfl, this, L.mfderiv_eq,
      mfderiv_chartAt_eq_tangentCoordChange (mem_chart_source _ x)]
    ext v
    exact congrArg L (tangentCoordChange_self (I := 𝓘(ℝ, Fin d → ℂ)) (v := (v : Fin d → ℂ))
      (mem_extChartAt_source (I := 𝓘(ℝ, Fin d → ℂ)) x))
  have h1 := congrArg (fun T : (Fin d → ℂ) →L[ℝ] ℂ => T (Pi.single i₀ 1)) h0
  simp only [dbarSection, hdiff, L, antiLinearPart_conj_proj] at h1
  simp at h1

end HodgeLean.Foundations
