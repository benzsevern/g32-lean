import HodgeLean.Foundations.Program.PrymVariationFramesDefs

noncomputable section
open Set Filter Topology
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Program

/-- The point of the fibre at `t` with vertical coordinate `z` in a parameter chart `φ`. -/
def b63e_slice (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b) (t : V)
    (φ : OpenPartialHomeomorph (b6t_polydisc b × C) ((Fin 10 → ℂ) × ℂ)) (z : ℂ) :
    b63l_parameterFibre b C V hV t :=
  (b6m_coordinate b C ⟨t.val, hV t.property⟩).symm ((φ.symm (t.val, z)).2)

theorem b63e_slice_val (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b) (t : V)
    (φ : OpenPartialHomeomorph (b6t_polydisc b × C) ((Fin 10 → ℂ) × ℂ))
    (hfp : ∀ y ∈ φ.source, (φ y).1 = y.1.val) {z : ℂ} (hz : (t.val, z) ∈ φ.target) :
    (b63e_slice b C V hV t φ z).val = φ.symm (t.val, z) := by
  have h1 : (φ.symm (t.val, z)).1.val = t.val := by
    rw [← hfp _ (φ.map_target hz), φ.right_inv hz]
  apply Prod.ext
  · exact Subtype.ext h1.symm
  · rfl

theorem b63e_slice_coord (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b) (t : V)
    (φ : OpenPartialHomeomorph (b6t_polydisc b × C) ((Fin 10 → ℂ) × ℂ))
    (hfp : ∀ y ∈ φ.source, (φ y).1 = y.1.val) {z : ℂ} (hz : (t.val, z) ∈ φ.target) :
    φ (b63e_slice b C V hV t φ z).val = (t.val, z) := by
  rw [b63e_slice_val b C V hV t φ hfp hz, φ.right_inv hz]

theorem b63e_continuous_slice (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b) (t : V)
    (φ : OpenPartialHomeomorph (b6t_polydisc b × C) ((Fin 10 → ℂ) × ℂ)) {z : ℂ}
    (hz : (t.val, z) ∈ φ.target) :
    ContinuousAt (b63e_slice b C V hV t φ) z := by
  refine (b6m_coordinate b C ⟨t.val, hV t.property⟩).symm.continuous.continuousAt.comp ?_
  refine continuous_snd.continuousAt.comp ?_
  exact (φ.continuousAt_symm hz).comp (continuous_const.prodMk continuous_id).continuousAt

theorem b63e_vertical_contMDiffAt (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)]
    [IsManifold 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω (b6t_polydisc b × C)]
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b) (t : V)
    [ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    (hincl : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω
      (fun x : b63l_parameterFibre b C V hV t ↦ x.val))
    {φ : OpenPartialHomeomorph (b6t_polydisc b × C) ((Fin 10 → ℂ) × ℂ)}
    (hφ : φ ∈ atlas ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C))
    (x : b63l_parameterFibre b C V hV t) (hx : x.val ∈ φ.source) :
    ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : b63l_parameterFibre b C V hV t ↦ (φ x.val).2) x := by
  have h1 : ContMDiffAt 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω φ x.val :=
    contMDiffAt_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas hφ) hx
  have h2 : ContMDiff 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) 𝓘(ℂ, ℂ) ω (Prod.snd : (Fin 10 → ℂ) × ℂ → ℂ) :=
    contDiff_snd.contMDiff
  exact h2.contMDiffAt.comp x (h1.comp x (hincl x))

theorem b63e_slice_contMDiffAt (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)]
    [IsManifold 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω (b6t_polydisc b × C)]
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b) (t : V)
    [ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    (hincl : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω
      (fun x : b63l_parameterFibre b C V hV t ↦ x.val))
    {φ : OpenPartialHomeomorph (b6t_polydisc b × C) ((Fin 10 → ℂ) × ℂ)}
    (hφ : φ ∈ atlas ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C))
    (hfp : ∀ y ∈ φ.source, (φ y).1 = y.1.val) {z : ℂ} (hz : (t.val, z) ∈ φ.target) :
    ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (b63e_slice b C V hV t φ) z := by
  set F := b63l_parameterFibre b C V hV t
  set j := b63e_slice b C V hV t φ
  set ψ : F → ℂ := fun x ↦ (φ x.val).2
  set x := j z
  set y := chartAt ℂ x
  have hxs : x.val ∈ φ.source := by
    rw [b63e_slice_val b C V hV t φ hfp hz]
    exact φ.map_target hz
  have hψx : ψ x = z := by
    simp only [ψ, x, j, b63e_slice_coord b C V hV t φ hfp hz]
  have hyx : y x ∈ y.target := y.map_source (mem_chart_source ℂ x)
  have hysymm : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω y.symm (y x) :=
    contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas x) hyx
  have hyy : y.symm (y x) = x := y.left_inv (mem_chart_source ℂ x)
  have hψ := b63e_vertical_contMDiffAt b C V hV t hincl hφ x hxs
  have ha : AnalyticAt ℂ (ψ ∘ y.symm) (y x) := by
    have hψ' : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω ψ (y.symm (y x)) := by rw [hyy]; exact hψ
    have h := hψ'.comp (y x) hysymm
    exact h.contDiffAt.analyticAt
  have hopen : IsOpen {x' : F | x'.val ∈ φ.source} :=
    φ.open_source.preimage continuous_subtype_val
  have hs : y.target ∩ y.symm ⁻¹' {x' : F | x'.val ∈ φ.source} ∈ 𝓝 (y x) := by
    refine inter_mem (y.open_target.mem_nhds hyx) ?_
    refine (y.continuousAt_symm hyx).preimage_mem_nhds ?_
    rw [hyy]
    exact hopen.mem_nhds hxs
  have hinj : InjOn (ψ ∘ y.symm) (y.target ∩ y.symm ⁻¹' {x' : F | x'.val ∈ φ.source}) := by
    intro p hp q hq hpq
    have hp' : (y.symm p).val ∈ φ.source := hp.2
    have hq' : (y.symm q).val ∈ φ.source := hq.2
    have e1 : φ (y.symm p).val = φ (y.symm q).val := by
      refine Prod.ext ?_ hpq
      rw [hfp _ hp', hfp _ hq', (y.symm p).property, (y.symm q).property]
    exact y.symm.injOn hp.1 hq.1 (Subtype.ext (φ.injOn hp' hq' e1))
  obtain ⟨e, hex, hef⟩ :=
    RiemannRochTop_injective_analytic_local_homeomorph (ψ ∘ y.symm) (y x) ha _ hs hinj
  have hea : AnalyticAt ℂ e (y x) := by rw [hef]; exact ha
  have hinv := RiemannRochTop_analytic_local_homeomorph_inverse e (y x) hex hea
  have hez : e (y x) = z := by
    rw [hef, Function.comp_apply, hyy, hψx]
  rw [hez] at hinv
  have hesymm : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω e.symm z := hinv.contDiffAt.contMDiffAt
  have hez' : e.symm z = y x := by rw [← hez]; exact e.left_inv hex
  have hysymm' : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω y.symm (e.symm z) := by rw [hez']; exact hysymm
  have hcomp : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (y.symm ∘ e.symm) z := hysymm'.comp z hesymm
  refine hcomp.congr_of_eventuallyEq ?_
  have hjc := b63e_continuous_slice b C V hV t φ hz
  have h1 : ∀ᶠ z' in 𝓝 z, j z' ∈ y.source :=
    hjc (y.open_source.mem_nhds (mem_chart_source ℂ x))
  have h2 : ∀ᶠ z' in 𝓝 z, y (j z') ∈ e.source := by
    have : ContinuousAt (y ∘ j) z := (y.continuousAt (mem_chart_source ℂ x)).comp hjc
    exact this (e.open_source.mem_nhds hex)
  have h3 : ∀ᶠ z' in 𝓝 z, (t.val, z') ∈ φ.target :=
    ((continuous_const.prodMk continuous_id).tendsto z).eventually (φ.open_target.mem_nhds hz)
  filter_upwards [h1, h2, h3] with z' h1 h2 h3
  have he : e (y (j z')) = z' := by
    rw [hef, Function.comp_apply, y.left_inv h1]
    simp only [ψ, j, b63e_slice_coord b C V hV t φ hfp h3]
  have h4 : e.symm z' = y (j z') := by
    conv_lhs => rw [← he]
    exact e.left_inv h2
  show j z' = y.symm (e.symm z')
  rw [h4, y.left_inv h1]

theorem b63e_slice_comp_contMDiff (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)]
    [IsManifold 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω (b6t_polydisc b × C)]
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b) (t : V)
    [ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    (hincl : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω
      (fun x : b63l_parameterFibre b C V hV t ↦ x.val))
    {φ : OpenPartialHomeomorph (b6t_polydisc b × C) ((Fin 10 → ℂ) × ℂ)}
    (hφ : φ ∈ atlas ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C))
    (hfp : ∀ y ∈ φ.source, (φ y).1 = y.1.val) {w : ℝ → ℂ} (hw : ContDiff ℝ 1 w)
    (hwt : ∀ τ, (t.val, w τ) ∈ φ.target) :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) 1 (b63e_slice b C V hV t φ ∘ w) := fun τ ↦
  (show ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) 1 (b63e_slice b C V hV t φ) (w τ) from
    (b3A_contMDiffWithinAt_real
      (b63e_slice_contMDiffAt b C V hV t hincl hφ hfp (hwt τ))).of_le le_top).comp τ
    (hw.contMDiff τ)

theorem b63e_slice_integrand (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)]
    [IsManifold 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω (b6t_polydisc b × C)]
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b) (t : V)
    [ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    (hincl : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω
      (fun x : b63l_parameterFibre b C V hV t ↦ x.val))
    {φ : OpenPartialHomeomorph (b6t_polydisc b × C) ((Fin 10 → ℂ) × ℂ)}
    (hφ : φ ∈ atlas ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C))
    (hfp : ∀ y ∈ φ.source, (φ y).1 = y.1.val)
    (θ : TangentBundle 𝓘(ℂ, ℂ) (b63l_parameterFibre b C V hV t) → ℂ)
    (A : (Fin 10 → ℂ) × ℂ → ℂ)
    (hθ : ∀ x : b63l_parameterFibre b C V hV t, x.val ∈ φ.source →
      ∀ v : TangentSpace 𝓘(ℂ, ℂ) x, θ ⟨x, v⟩ = A (φ x.val) * (show ℂ from
        mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
          (fun z : b63l_parameterFibre b C V hV t ↦ (φ z.val).2) x v))
    {w : ℝ → ℂ} (hw : ContDiff ℝ 1 w) (hwt : ∀ τ, (t.val, w τ) ∈ φ.target) (τ : ℝ) :
    b3A_integrand θ (b63e_slice b C V hV t φ ∘ w) τ = A (t.val, w τ) * deriv w τ := by
  set F := b63l_parameterFibre b C V hV t
  set g := b63e_slice b C V hV t φ ∘ w
  set ψ : F → ℂ := fun z ↦ (φ z.val).2
  have hg := b63e_slice_comp_contMDiff b C V hV t hincl hφ hfp hw hwt
  have hx : (g τ).val ∈ φ.source := by
    simp only [g, Function.comp_apply, b63e_slice_val b C V hV t φ hfp (hwt τ)]
    exact φ.map_target (hwt τ)
  have hφx : φ (g τ).val = (t.val, w τ) := b63e_slice_coord b C V hV t φ hfp (hwt τ)
  have hψ : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω ψ (g τ) :=
    b63e_vertical_contMDiffAt b C V hV t hincl hφ (g τ) hx
  have hψR := b3A_mdifferentiableAt_real (hψ.mdifferentiableAt (by simp))
  have hψg : ψ ∘ g = w := by
    funext σ
    simp only [ψ, g, Function.comp_apply, b63e_slice_coord b C V hV t φ hfp (hwt σ)]
  have hchain := mfderiv_comp_apply τ hψR.1 ((hg τ).mdifferentiableAt one_ne_zero) 1
  rw [hψg] at hchain
  unfold b3A_integrand
  rw [hθ (g τ) hx, hφx]
  congr 1
  change mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ψ (g τ) (b3_velocity ℂ F g τ) = deriv w τ
  have e1 := (hψR.2 (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) g τ 1)).symm
  have e2 : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) w τ 1 = deriv w τ := by rw [mfderiv_eq_fderiv]; rfl
  exact e1.trans (hchain.symm.trans e2)

theorem b63e_slice_segment_integral (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)]
    [IsManifold 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω (b6t_polydisc b × C)]
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b) (t : V)
    [ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    (hincl : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω
      (fun x : b63l_parameterFibre b C V hV t ↦ x.val))
    {φ : OpenPartialHomeomorph (b6t_polydisc b × C) ((Fin 10 → ℂ) × ℂ)}
    (hφ : φ ∈ atlas ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C))
    (hfp : ∀ y ∈ φ.source, (φ y).1 = y.1.val)
    (θ : TangentBundle 𝓘(ℂ, ℂ) (b63l_parameterFibre b C V hV t) → ℂ)
    (A : (Fin 10 → ℂ) × ℂ → ℂ)
    (hθ : ∀ x : b63l_parameterFibre b C V hV t, x.val ∈ φ.source →
      ∀ v : TangentSpace 𝓘(ℂ, ℂ) x, θ ⟨x, v⟩ = A (φ x.val) * (show ℂ from
        mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
          (fun z : b63l_parameterFibre b C V hV t ↦ (φ z.val).2) x v))
    (a c : ℂ) (hseg : ∀ s ∈ Icc (0 : ℝ) 1, (t.val, a + (s : ℂ) * (c - a)) ∈ φ.target)
    (hA : ∀ s ∈ Icc (0 : ℝ) 1, ContinuousAt A (t.val, a + (s : ℂ) * (c - a))) :
    b3_pathIntegral ℂ _ (b63e_slice b C V hV t φ ∘ fun τ ↦ a + (b3A_step τ : ℂ) * (c - a)) θ =
      ∫ s in (0 : ℝ)..1, A (t.val, a + (s : ℂ) * (c - a)) * (c - a) := by
  have hst : ∀ τ, b3A_step τ ∈ Icc (0 : ℝ) 1 := fun τ ↦
    ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  have hd : Differentiable ℝ b3A_step := b3A_step_contDiff.differentiable one_ne_zero
  have hw : ContDiff ℝ 1 (fun τ ↦ a + (b3A_step τ : ℂ) * (c - a)) :=
    contDiff_const.add ((Complex.ofRealCLM.contDiff.comp b3A_step_contDiff).mul contDiff_const)
  have hwt : ∀ τ, (t.val, a + (b3A_step τ : ℂ) * (c - a)) ∈ φ.target := fun τ ↦
    hseg _ (hst τ)
  have hderiv : ∀ τ, deriv (fun τ ↦ a + (b3A_step τ : ℂ) * (c - a)) τ =
      ((deriv b3A_step τ : ℝ) : ℂ) * (c - a) := by
    intro τ
    have h1 : HasDerivAt (fun τ ↦ a + (b3A_step τ : ℂ) * (c - a))
        (((deriv b3A_step τ : ℝ) : ℂ) * (c - a)) τ :=
      (((hd τ).hasDerivAt.ofReal_comp).mul_const (c - a)).const_add a
    exact h1.deriv
  unfold b3_pathIntegral
  change ∫ τ in (0 : ℝ)..1, b3A_integrand θ _ τ = _
  simp_rw [b63e_slice_integrand b C V hV t hincl hφ hfp θ A hθ hw hwt, hderiv]
  set G : ℝ → ℂ := fun s ↦ A (t.val, a + (s : ℂ) * (c - a)) * (c - a)
  have hrw : ∀ τ, A (t.val, a + (b3A_step τ : ℂ) * (c - a)) * (((deriv b3A_step τ : ℝ) : ℂ) * (c - a)) =
      deriv b3A_step τ • (G ∘ b3A_step) τ := by
    intro τ
    simp only [G, Function.comp_apply, Complex.real_smul]
    ring
  simp_rw [hrw]
  have h0 : b3A_step 0 = 0 := Real.smoothTransition.zero_of_nonpos (by norm_num)
  have h1 : b3A_step 1 = 1 := Real.smoothTransition.one_of_one_le (by norm_num)
  rw [intervalIntegral.integral_deriv_smul_comp' (fun τ _ ↦ (hd τ).hasDerivAt)
    (b3A_step_contDiff.continuous_deriv le_rfl).continuousOn, h0, h1]
  rintro _ ⟨τ, -, rfl⟩
  have hc : ContinuousAt (fun s : ℝ ↦ (t.val, a + (s : ℂ) * (c - a))) (b3A_step τ) := by
    fun_prop
  have h2 : ContinuousAt (A ∘ fun s : ℝ ↦ (t.val, a + (s : ℂ) * (c - a))) (b3A_step τ) :=
    ContinuousAt.comp (g := A) (hA _ (hst τ)) hc
  exact (h2.mul continuousAt_const).continuousWithinAt

end HodgeLean.Foundations.Program
