import HodgeLean.Foundations.Program.CurveJacobianFormsHodgeStar

/-!
# Track B3 foundations (stage B3.4c): harmonic forms are real parts of holomorphic forms

For a real `1`-form `α` on a Riemann surface, `b3Forms_holOf α = α + i ⋆α` is a function on the
tangent bundle, complex-linear on each fibre (`b3Forms_cplxPt_smul`). If `α` is harmonic
(`dα = 0` and `d⋆α = 0`):
* its coefficient in each chart satisfies the Cauchy–Riemann equations
  (`b3Forms_hasFDerivAt_cplxPt_loc`: the derivative of the coefficient is complex-linear, from the
  symmetry of the derivatives of `α` and `⋆α`), so it is holomorphic
  (`b3Forms_contDiffOn_cplxPt_loc`);
* `α + i ⋆α ∈ Ω¹(C)` (`b3Forms_holOf_mem`), read through the charts of the tangent bundle
  (`b3Forms_extChartAt_tangent`), and `Re (α + i ⋆α) = α` (`b3Forms_reForm_harmonicHol`).

With `b3Forms_isHarmonic_reForm` this identifies harmonic `1`-forms with `Ω¹(C)`.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Set Filter Manifold ContinuousAlternatingMap MeasureTheory
open scoped Topology ContDiff

namespace HodgeLean.Foundations.Program

section Pointwise

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The complex-valued functional `v ↦ A v + i (⋆A) v = A v - i A(i v)` of a real `1`-form.
Source: Forster, *Lectures on Riemann Surfaces*, GTM 81, §19 (a harmonic 1-form is the real part of
a holomorphic form). -/
def b3Forms_cplxPt (A : E [⋀^Fin 1]→L[ℝ] ℝ) (v : E) : ℂ :=
  (b3Forms_toCLM A v : ℂ) + Complex.I * ((-b3Forms_toCLM A (Complex.I • v) : ℝ) : ℂ)

theorem b3Forms_cplxPt_eq (A : E [⋀^Fin 1]→L[ℝ] ℝ) (v : E) :
    b3Forms_cplxPt A v =
      (A (fun _ ↦ v) : ℂ) + Complex.I * (b3Forms_starPt A (fun _ ↦ v) : ℂ) := rfl

theorem b3Forms_cplxPt_add (A : E [⋀^Fin 1]→L[ℝ] ℝ) (v w : E) :
    b3Forms_cplxPt A (v + w) = b3Forms_cplxPt A v + b3Forms_cplxPt A w := by
  simp only [b3Forms_cplxPt, smul_add, map_add]
  push_cast
  ring

theorem b3Forms_cplxPt_I_smul (A : E [⋀^Fin 1]→L[ℝ] ℝ) (v : E) :
    b3Forms_cplxPt A (Complex.I • v) = Complex.I * b3Forms_cplxPt A v := by
  simp only [b3Forms_cplxPt, smul_smul, Complex.I_mul_I, neg_one_smul, map_neg]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

theorem b3Forms_cplxPt_real_smul (A : E [⋀^Fin 1]→L[ℝ] ℝ) (s : ℝ) (v : E) :
    b3Forms_cplxPt A ((s : ℂ) • v) = s * b3Forms_cplxPt A v := by
  simp only [b3Forms_cplxPt, smul_smul, mul_comm Complex.I (s : ℂ)]
  rw [← smul_smul, Complex.coe_smul, Complex.coe_smul, map_smul, map_smul, smul_eq_mul,
    smul_eq_mul]
  push_cast
  ring

/-- **The functional `A + i ⋆A` is complex-linear.** -/
theorem b3Forms_cplxPt_smul (A : E [⋀^Fin 1]→L[ℝ] ℝ) (a : ℂ) (v : E) :
    b3Forms_cplxPt A (a • v) = a * b3Forms_cplxPt A v := by
  have ha : a • v = (a.re : ℂ) • v + (a.im : ℂ) • (Complex.I • v) := by
    rw [smul_smul, ← add_smul]
    congr 1
    conv_lhs => rw [← Complex.re_add_im a]
  rw [ha, b3Forms_cplxPt_add, b3Forms_cplxPt_real_smul, b3Forms_cplxPt_real_smul,
    b3Forms_cplxPt_I_smul]
  conv_rhs => rw [← Complex.re_add_im a]
  ring_nf

theorem b3Forms_cplxPt_comp (A : E [⋀^Fin 1]→L[ℝ] ℝ) (L : E →L[ℂ] E) (w : E) :
    b3Forms_cplxPt (A.compContinuousLinearMap (L.restrictScalars ℝ)) w =
      b3Forms_cplxPt A (L w) := by
  simp only [b3Forms_cplxPt, b3Forms_toCLM_apply, compContinuousLinearMap_apply,
    Function.comp_def, ContinuousLinearMap.coe_restrictScalars', map_smul]

/-- A real-linear map satisfying the Cauchy–Riemann identity `L (i v) = i L v` is
complex-linear.
Source: Forster, *Lectures on Riemann Surfaces*, GTM 81, §19 (a harmonic 1-form is the real part of
a holomorphic form). -/
def b3Forms_cplxOfCR (L : E →L[ℝ] ℂ) (h : ∀ v, L (Complex.I • v) = Complex.I * L v) :
    E →L[ℂ] ℂ where
  toFun := L
  map_add' := L.map_add
  map_smul' a v := by
    have ha : a • v = (a.re : ℂ) • v + (a.im : ℂ) • (Complex.I • v) := by
      rw [smul_smul, ← add_smul]
      congr 1
      conv_lhs => rw [← Complex.re_add_im a]
    simp only [RingHom.id_apply, smul_eq_mul]
    rw [ha, map_add, Complex.coe_smul, Complex.coe_smul, map_smul, map_smul, h,
      Complex.real_smul, Complex.real_smul]
    conv_rhs => rw [← Complex.re_add_im a]
    ring
  cont := L.continuous

theorem b3Forms_cplxOfCR_restrictScalars (L : E →L[ℝ] ℂ)
    (h : ∀ v, L (Complex.I • v) = Complex.I * L v) :
    (b3Forms_cplxOfCR L h).restrictScalars ℝ = L := by
  ext v
  rfl

end Pointwise

section Chart

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {C : Type} [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]

attribute [local instance] b3Forms_isManifold_real

/-- **The complex form `α + i ⋆α`** of a real `1`-form, as a function on the tangent bundle.
Source: Forster, *Lectures on Riemann Surfaces*, GTM 81, §19 (a harmonic 1-form is the real part of
a holomorphic form). -/
def b3Forms_holOf (α : C → E [⋀^Fin 1]→L[ℝ] ℝ) : TangentBundle 𝓘(ℂ, E) C → ℂ :=
  fun p ↦ b3Forms_cplxPt (α p.1) p.2

theorem b3Forms_holOf_chartVec (α : C → E [⋀^Fin 1]→L[ℝ] ℝ) {x : C} {u : E}
    (hu : u ∈ (chartAt E x).target) (w : E) :
    b3Forms_holOf α (b3Forms_chartVec x w u) = b3Forms_cplxPt (b3Forms_loc α x u) w := by
  simp only [b3Forms_loc]
  rw [b3Forms_fderiv_tr_real (b3Forms_mem_trDom_self hu), b3Forms_cplxPt_comp]
  rfl

/-- **The Cauchy–Riemann equations for a harmonic form**: the coefficient of `α + i ⋆α` in a
chart is complex differentiable. -/
theorem b3Forms_hasFDerivAt_cplxPt_loc {α : C → E [⋀^Fin 1]→L[ℝ] ℝ} (hα : b3Forms_IsSmooth α)
    (hdα : b3Forms_d α = 0) (hdsα : b3Forms_d (b3Forms_star α) = 0) {x : C} {u : E}
    (hu : u ∈ (chartAt E x).target) (e : E) :
    ∃ L : E →L[ℂ] ℂ,
      HasFDerivAt (fun u' ↦ b3Forms_cplxPt (b3Forms_loc α x u') e) (L.restrictScalars ℝ) u := by
  set g : E → E → ℝ := fun w u' ↦ b3Forms_loc α x u' (fun _ ↦ w)
  have hdiff : DifferentiableAt ℝ (b3Forms_loc α x) u :=
    (hα.contDiffAt hu).differentiableAt (by simp)
  have hg : ∀ w, HasFDerivAt (g w) (fderiv ℝ (g w) u) u := fun w ↦ by
    have h := DifferentiableAt.comp (g := ⇑(ContinuousAlternatingMap.apply ℝ E ℝ (fun _ ↦ w)))
      u (ContinuousLinearMap.differentiableAt _) hdiff
    exact h.hasFDerivAt
  set a : E → E → ℝ := fun v w ↦ fderiv ℝ (g w) u v
  have hev : ∀ (β : C → E [⋀^Fin 1]→L[ℝ] ℝ), b3Forms_IsSmooth β → b3Forms_d β = 0 →
      ∀ v w, fderiv ℝ (fun u' ↦ b3Forms_loc β x u' (fun _ ↦ w)) u v =
        fderiv ℝ (fun u' ↦ b3Forms_loc β x u' (fun _ ↦ v)) u w := by
    intro β hβ hdβ v w
    have hdβ' : DifferentiableAt ℝ (b3Forms_loc β x) u :=
      (hβ.contDiffAt hu).differentiableAt (by simp)
    have h0 : extDeriv (b3Forms_loc β x) u = 0 := by
      rw [← b3Forms_loc_d hβ x hu, hdβ, b3Forms_loc_zero]
      rfl
    have h1 := congrArg (fun A : E [⋀^Fin 2]→L[ℝ] ℝ ↦ A ![v, w]) h0
    simp only [extDeriv_apply hdβ', ContinuousAlternatingMap.coe_zero, Pi.zero_apply] at h1
    rw [Fin.sum_univ_two] at h1
    have e0 : Fin.removeNth 0 ![v, w] = fun _ ↦ w := by funext i; fin_cases i; rfl
    have e1 : Fin.removeNth 1 ![v, w] = fun _ ↦ v := by funext i; fin_cases i; rfl
    rw [e0, e1] at h1
    simp at h1
    linarith
  have hsym1 : ∀ v w, a v w = a w v := fun v w ↦ hev α hα hdα v w
  have hstar : ∀ w, (fun u' ↦ b3Forms_loc (b3Forms_star α) x u' (fun _ ↦ w)) =ᶠ[𝓝 u]
      fun u' ↦ -g (Complex.I • w) u' := fun w ↦ by
    filter_upwards [(chartAt E x).open_target.mem_nhds hu] with u' hu'
    rw [b3Forms_loc_star α hu', b3Forms_starPt_apply]
  have hneg : ∀ w v, fderiv ℝ (fun u' ↦ -g w u') u v = -a v w := fun w v ↦ by
    rw [show (fun u' ↦ -g w u') = -g w from rfl, (hg w).neg.fderiv]
    rfl
  have hsym2 : ∀ v w, a v (Complex.I • w) = a w (Complex.I • v) := fun v w ↦ by
    have h := hev (b3Forms_star α) hα.star hdsα v w
    rw [(hstar w).fderiv_eq, (hstar v).fderiv_eq, hneg, hneg] at h
    linarith
  have hglin : ∀ v w, a v (-w) = -a v w := fun v w ↦ by
    have : g (-w) = fun u' ↦ -g w u' := by
      funext u'
      exact b3Forms_apply_neg_const _ w
    simp only [a, this]
    exact hneg w v
  set Lr : E →L[ℝ] ℂ := Complex.ofRealCLM.comp (fderiv ℝ (g e) u) +
    Complex.I • Complex.ofRealCLM.comp (-fderiv ℝ (g (Complex.I • e)) u)
  have hCR : ∀ v, Lr (Complex.I • v) = Complex.I * Lr v := fun v ↦ by
    have h1 : a (Complex.I • v) e = a v (Complex.I • e) := by
      rw [hsym1, hsym2 e v]
    have h2 : a (Complex.I • v) (Complex.I • e) = -a v e := by
      rw [hsym1, hsym2 (Complex.I • e) v, smul_smul, Complex.I_mul_I,
        show ((-1 : ℂ) • e) = -e by simp, hglin]
    simp only [Lr, _root_.add_apply, ContinuousLinearMap.coe_comp,
      Function.comp_apply, _root_.smul_apply, _root_.neg_apply,
      Complex.ofRealCLM_apply, smul_eq_mul]
    change ((a (Complex.I • v) e : ℝ) : ℂ) + Complex.I * ((-a (Complex.I • v) (Complex.I • e) :
      ℝ) : ℂ) = Complex.I * (((a v e : ℝ) : ℂ) + Complex.I * ((-a v (Complex.I • e) : ℝ) : ℂ))
    rw [h1, h2]
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  refine ⟨b3Forms_cplxOfCR Lr hCR, ?_⟩
  rw [b3Forms_cplxOfCR_restrictScalars]
  have h1 := Complex.ofRealCLM.hasFDerivAt.comp u (hg e)
  have h2 := (Complex.ofRealCLM.hasFDerivAt.comp u (hg (Complex.I • e)).neg).const_mul
    Complex.I
  refine (h1.add h2).congr_of_eventuallyEq ?_ |>.congr_fderiv ?_
  · filter_upwards with u'
    simp [b3Forms_cplxPt, g, b3Forms_toCLM_apply]
  · ext v
    simp [Lr]

/-- The coordinate `ℂ ≃ E`, `c ↦ c • e`, of a complex line.
Source: Forster, *Lectures on Riemann Surfaces*, GTM 81, §19 (a harmonic 1-form is the real part of
a holomorphic form). -/
def b3Forms_lineEquiv (hE : Module.finrank ℂ E = 1) {e : E} (he : e ≠ 0) : ℂ ≃L[ℂ] E :=
  (LinearEquiv.ofBijective (LinearMap.toSpanSingleton ℂ E e)
    ⟨fun a b hab ↦ by
      simp only [LinearMap.toSpanSingleton_apply] at hab
      exact smul_left_injective ℂ he hab,
     fun w ↦ by
      obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' e he).1 hE w
      exact ⟨c, hc⟩⟩).toContinuousLinearEquiv

theorem b3Forms_lineEquiv_apply (hE : Module.finrank ℂ E = 1) {e : E} (he : e ≠ 0) (c : ℂ) :
    b3Forms_lineEquiv hE he c = c • e := rfl

/-- **A complex-differentiable function on an open subset of a complex line is analytic.** -/
theorem b3Forms_contDiffOn_of_differentiableOn (hE : Module.finrank ℂ E = 1) {f : E → ℂ}
    {s : Set E} (hs : IsOpen s) (hf : DifferentiableOn ℂ f s) : ContDiffOn ℂ ω f s := by
  obtain ⟨e, he, -⟩ := finrank_eq_one_iff'.1 hE
  set φ := b3Forms_lineEquiv hE he
  have hs' : IsOpen (φ ⁻¹' s) := hs.preimage φ.continuous
  have h1 : DifferentiableOn ℂ (f ∘ φ) (φ ⁻¹' s) :=
    hf.comp φ.differentiableOn fun _ h ↦ h
  have h2 : ContDiffOn ℂ ω (f ∘ φ) (φ ⁻¹' s) := h1.contDiffOn hs'
  have h3 := h2.comp_continuousLinearMap (φ.symm : E →L[ℂ] ℂ)
  refine h3.congr_mono ?_ ?_
  · intro u _
    simp
  · intro u hu
    simpa using hu

/-- **The coefficient of `α + i ⋆α` in a chart is holomorphic** for a harmonic form. -/
theorem b3Forms_contDiffOn_cplxPt_loc (hE : Module.finrank ℂ E = 1)
    {α : C → E [⋀^Fin 1]→L[ℝ] ℝ} (hα : b3Forms_IsSmooth α) (hdα : b3Forms_d α = 0)
    (hdsα : b3Forms_d (b3Forms_star α) = 0) (x : C) (e : E) :
    ContDiffOn ℂ ω (fun u ↦ b3Forms_cplxPt (b3Forms_loc α x u) e) (chartAt E x).target := by
  refine b3Forms_contDiffOn_of_differentiableOn hE (chartAt E x).open_target fun u hu ↦ ?_
  obtain ⟨L, hL⟩ := b3Forms_hasFDerivAt_cplxPt_loc hα hdα hdsα hu e
  exact (hasFDerivAt_of_restrictScalars ℝ hL rfl).differentiableAt.differentiableWithinAt

theorem b3Forms_fderiv_tr_self_complex {x : C} {u : E} (hu : u ∈ (chartAt E x).target) :
    fderiv ℂ (b3Forms_tr (E := E) x x) u = ContinuousLinearMap.id ℂ E := by
  rw [(b3Forms_tr_self_eventuallyEq hu).fderiv_eq, fderiv_id]

/-- The chart of the tangent bundle at `p`, on a point `q` over the chart domain. -/
theorem b3Forms_extChartAt_tangent (p q : TangentBundle 𝓘(ℂ, E) C) :
    extChartAt 𝓘(ℂ, E).tangent p q =
      (chartAt E p.1 q.1,
        fderiv ℂ (b3Forms_tr (E := E) q.1 p.1) (chartAt E q.1 q.1) q.2) := by
  rw [extChartAt_coe]
  simp only [Function.comp_apply, ModelWithCorners.tangent, modelWithCorners_prod_coe,
    modelWithCornersSelf_coe, Prod.map_apply, id_eq]
  refine Prod.ext rfl ?_
  show (trivializationAt E (TangentSpace 𝓘(ℂ, E)) p.1 q).2 = _
  rw [TangentBundle.trivializationAt_apply]
  simp only [OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm,
    modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, range_id, fderivWithin_univ,
    Function.id_comp, Function.comp_id]
  rfl

/-- **The complex form of a harmonic `1`-form is holomorphic**: `α + i ⋆α ∈ Ω¹(C)`. -/
theorem b3Forms_holOf_mem (hE : Module.finrank ℂ E = 1) {α : C → E [⋀^Fin 1]→L[ℝ] ℝ}
    (hα : b3Forms_IsHarmonic α) : b3Forms_holOf α ∈ b3_HolForm E C := by
  obtain ⟨hs, hd, hds⟩ := hα
  refine ⟨?_, fun x a v w ↦ ?_⟩
  · have : IsManifold 𝓘(ℂ, E) (ω + 1) C := by
      rw [show (ω : WithTop ℕ∞) + 1 = ω from rfl]; infer_instance
    intro p
    set x := p.1
    obtain ⟨e, he, -⟩ := finrank_eq_one_iff'.1 hE
    set φ := b3Forms_lineEquiv hE he
    set f : E → ℂ := fun u ↦ b3Forms_cplxPt (b3Forms_loc α x u) e
    set Φ : E × E → ℂ := fun uw ↦ φ.symm uw.2 * f uw.1
    have hx := (chartAt E x).map_source (mem_chart_source E x)
    have hf : ContDiffAt ℂ ω f (chartAt E x x) :=
      (b3Forms_contDiffOn_cplxPt_loc hE hs hd hds x e).contDiffAt
        ((chartAt E x).open_target.mem_nhds hx)
    have hp1 : (extChartAt 𝓘(ℂ, E).tangent p p).1 = chartAt E x x := by
      rw [b3Forms_extChartAt_tangent]
    have hΦ : ContDiffAt ℂ ω Φ (extChartAt 𝓘(ℂ, E).tangent p p) := by
      refine ((φ.symm : E →L[ℂ] ℂ).contDiff.comp contDiff_snd).contDiffAt.mul ?_
      rw [← hp1] at hf
      exact hf.comp _ contDiffAt_fst
    refine (hΦ.comp_contMDiffAt contMDiffAt_extChartAt).congr_of_eventuallyEq ?_
    filter_upwards [chart_source_mem_nhds (ModelProd E E) p] with q hq
    rw [TangentBundle.mem_chart_source_iff] at hq
    simp only [Function.comp_apply, b3Forms_extChartAt_tangent, Φ, f]
    set u := chartAt E x q.1
    set w := fderiv ℂ (b3Forms_tr (E := E) q.1 x) (chartAt E q.1 q.1) q.2
    have hu : u ∈ (chartAt E x).target := (chartAt E x).map_source hq
    have hsym : (chartAt E x).symm u = q.1 := (chartAt E x).left_inv hq
    have hq1 := (chartAt E q.1).map_source (mem_chart_source E q.1)
    have hdom : chartAt E q.1 q.1 ∈ b3Forms_trDom q.1 x :=
      ⟨hq1, by rw [mem_preimage, (chartAt E q.1).left_inv (mem_chart_source E q.1)]; exact hq⟩
    have hchain := b3Forms_fderiv_tr_comp_complex (z := q.1) hdom
      (by rw [(chartAt E q.1).left_inv (mem_chart_source E q.1)]; exact mem_chart_source E q.1)
    rw [b3Forms_fderiv_tr_self_complex hq1] at hchain
    have htr : b3Forms_tr q.1 x (chartAt E q.1 q.1) = u := by
      simp [b3Forms_tr, u, (chartAt E q.1).left_inv (mem_chart_source E q.1)]
    rw [htr] at hchain
    have hvec : b3Forms_chartVec x w u = q := by
      refine Bundle.TotalSpace.ext hsym ?_
      simp only [b3Forms_chartVec]
      rw [hsym]
      apply heq_of_eq
      have := congrArg (fun L : E →L[ℂ] E ↦ L q.2) hchain
      exact this.symm
    rw [← hvec, b3Forms_holOf_chartVec α hu, ← b3Forms_cplxPt_smul]
    congr 1
    show w = φ (φ.symm w)
    simp
  · simp only [b3Forms_holOf]
    have h1 := b3Forms_cplxPt_add (α x) (a • (v : E)) (w : E)
    exact h1.trans (congrArg (· + b3Forms_cplxPt (α x) w) (b3Forms_cplxPt_smul (α x) a v))

/-- **The holomorphic form of a harmonic `1`-form.**
Source: Forster, *Lectures on Riemann Surfaces*, GTM 81, §19 (a harmonic 1-form is the real part of
a holomorphic form). -/
def b3Forms_harmonicHol (hE : Module.finrank ℂ E = 1) {α : C → E [⋀^Fin 1]→L[ℝ] ℝ}
    (hα : b3Forms_IsHarmonic α) : b3_HolForm E C :=
  ⟨b3Forms_holOf α, b3Forms_holOf_mem hE hα⟩

/-- **Every harmonic `1`-form is the real part of a holomorphic form.** -/
theorem b3Forms_reForm_harmonicHol (hE : Module.finrank ℂ E = 1)
    {α : C → E [⋀^Fin 1]→L[ℝ] ℝ} (hα : b3Forms_IsHarmonic α) :
    b3Forms_reForm (b3Forms_harmonicHol hE hα) = α := by
  funext z
  ext v
  have : v = fun _ ↦ v 0 := funext fun i ↦ by fin_cases i; rfl
  rw [this, b3Forms_reForm_apply]
  simp [b3Forms_harmonicHol, b3Forms_holOf, b3Forms_cplxPt, b3Forms_toCLM_apply]

end Chart

end HodgeLean.Foundations.Program
