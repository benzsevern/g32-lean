import HodgeLean.Foundations.Program.HurwitzPrymCovInvariant

set_option maxHeartbeats 400000

/-! # Track B4, lane `b4-cov`: coefficients of forms in charts

For a function `θ` on the tangent bundle and a point `x₀`, the coefficient of `θ` in the chart at
`x₀` is `t ↦ θ(∂_t)`, the value on the vector with coordinate `u` in the trivialization at `x₀`
over the chart point `t`. A holomorphic form has analytic coefficients; conversely a fibrewise
linear function with analytic coefficients at every chart centre is a holomorphic form. Pulling
back along a holomorphic map multiplies coefficients by the derivative of the chart expression.
HC no distance; AV milestone no distance.
-/

noncomputable section

open Manifold Set Filter Topology
open scoped ContDiff

namespace HodgeLean.Foundations.Program

section Coef

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F]
variable {M : Type} [TopologicalSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℂ, F) ω M]

/-- The vector with coordinate `u` in the trivialization at `x₀`, at the point `x`. -/
def b4cov_vec (x₀ x : M) (u : F) : TangentSpace 𝓘(ℂ, F) x :=
  (trivializationAt F (TangentSpace 𝓘(ℂ, F)) x₀).symm x u

/-- **The coefficient of `θ` in the chart at `x₀`**: `t ↦ θ(∂_t)`. -/
def b4cov_coef (θ : TangentBundle 𝓘(ℂ, F) M → ℂ) (x₀ : M) (u : F) : F → ℂ :=
  fun t ↦ θ ⟨(extChartAt 𝓘(ℂ, F) x₀).symm t, b4cov_vec x₀ ((extChartAt 𝓘(ℂ, F) x₀).symm t) u⟩

theorem b4cov_mem_baseSet (x₀ x : M) (hx : x ∈ (extChartAt 𝓘(ℂ, F) x₀).source) :
    x ∈ (trivializationAt F (TangentSpace 𝓘(ℂ, F)) x₀).baseSet := by
  rwa [TangentBundle.trivializationAt_baseSet, ← extChartAt_source 𝓘(ℂ, F)]

theorem b4cov_triv_vec (x₀ x : M) (hx : x ∈ (extChartAt 𝓘(ℂ, F) x₀).source) (u : F) :
    (trivializationAt F (TangentSpace 𝓘(ℂ, F)) x₀ ⟨x, b4cov_vec x₀ x u⟩).2 = u := by
  rw [b4cov_vec, Bundle.Trivialization.apply_mk_symm _ (b4cov_mem_baseSet x₀ x hx)]

theorem b4cov_vec_triv (x₀ x : M) (hx : x ∈ (extChartAt 𝓘(ℂ, F) x₀).source)
    (v : TangentSpace 𝓘(ℂ, F) x) :
    b4cov_vec x₀ x (trivializationAt F (TangentSpace 𝓘(ℂ, F)) x₀ ⟨x, v⟩).2 = v :=
  Bundle.Trivialization.symm_apply_apply_mk _ (b4cov_mem_baseSet x₀ x hx) v

/-- **Coefficients of a holomorphic form are analytic.** -/
theorem b4cov_coef_analyticAt (θ : TangentBundle 𝓘(ℂ, F) M → ℂ)
    (hθ : ContMDiff 𝓘(ℂ, F).tangent 𝓘(ℂ, ℂ) ω θ) (x₀ : M) (u : F) (t : F)
    (ht : t ∈ (extChartAt 𝓘(ℂ, F) x₀).target) : AnalyticAt ℂ (b4cov_coef θ x₀ u) t := by
  let σ : F → TangentBundle 𝓘(ℂ, F) M := fun s ↦
    ⟨(extChartAt 𝓘(ℂ, F) x₀).symm s, b4cov_vec x₀ ((extChartAt 𝓘(ℂ, F) x₀).symm s) u⟩
  have hsrc : (σ t) ∈ (trivializationAt F (TangentSpace 𝓘(ℂ, F)) x₀).source := by
    rw [TangentBundle.trivializationAt_source]
    change (extChartAt 𝓘(ℂ, F) x₀).symm t ∈ (chartAt F x₀).source
    rw [← extChartAt_source 𝓘(ℂ, F)]
    exact (extChartAt 𝓘(ℂ, F) x₀).map_target ht
  have hσ : ContMDiffAt 𝓘(ℂ, F) 𝓘(ℂ, F).tangent ω σ t := by
    rw [(trivializationAt F (TangentSpace 𝓘(ℂ, F)) x₀).contMDiffAt_iff hsrc]
    refine ⟨?_, ?_⟩
    · exact (contMDiffOn_extChartAt_symm x₀).contMDiffAt
        ((isOpen_extChartAt_target x₀).mem_nhds ht)
    · refine (contMDiffAt_const (c := u)).congr_of_eventuallyEq ?_
      filter_upwards [(isOpen_extChartAt_target x₀).mem_nhds ht] with s hs
      exact b4cov_triv_vec x₀ _ ((extChartAt 𝓘(ℂ, F) x₀).map_target hs) u
  have := (hθ (σ t)).comp t hσ
  exact (contMDiffAt_iff_contDiffAt.1 this).analyticAt

/-- Trivialization coordinates are the derivative of the chart. -/
theorem b4cov_triv_eq_mfderiv (x₀ x : M) (hx : x ∈ (extChartAt 𝓘(ℂ, F) x₀).source)
    (v : TangentSpace 𝓘(ℂ, F) x) :
    (trivializationAt F (TangentSpace 𝓘(ℂ, F)) x₀ ⟨x, v⟩).2 =
      mfderiv 𝓘(ℂ, F) 𝓘(ℂ, F) (extChartAt 𝓘(ℂ, F) x₀) x v := by
  have hx' : x ∈ (chartAt F x₀).source := by rwa [← extChartAt_source 𝓘(ℂ, F)]
  rw [TangentBundle.trivializationAt_apply, (mdifferentiableAt_extChartAt hx').mfderiv_abuse]
  simp only [writtenInExtChartAt, extChartAt_model_space_eq_id, PartialEquiv.refl_coe,
    Function.id_comp]
  rfl

theorem b4cov_vec_smul (x₀ x : M) (hx : x ∈ (extChartAt 𝓘(ℂ, F) x₀).source) (c : ℂ) (u : F) :
    b4cov_vec x₀ x (c • u) = c • b4cov_vec x₀ x u := by
  have hb := b4cov_mem_baseSet x₀ x hx
  simp only [b4cov_vec]
  rw [← Bundle.Trivialization.symmL_apply (R := ℂ) _ hb,
    ← Bundle.Trivialization.symmL_apply (R := ℂ) _ hb, map_smul]

/-- **A fibrewise linear function with analytic chart coefficients is a holomorphic form.** -/
theorem b4cov_mem_holForm_of_coef (hF : Module.finrank ℂ F = 1)
    (θ : TangentBundle 𝓘(ℂ, F) M → ℂ)
    (hlin : ∀ (x : M) (a : ℂ) (v w : TangentSpace 𝓘(ℂ, F) x),
      θ ⟨x, a • v + w⟩ = a * θ ⟨x, v⟩ + θ ⟨x, w⟩)
    (hcoef : ∀ x₀ : M, AnalyticAt ℂ (b4cov_coef θ x₀ (b4cov_lineEquiv hF 1))
      (extChartAt 𝓘(ℂ, F) x₀ x₀)) :
    θ ∈ b3_HolForm F M := by
  refine ⟨fun p₀ ↦ ?_, hlin⟩
  set x₀ := p₀.proj
  set L := b4cov_lineEquiv hF
  set e := trivializationAt F (TangentSpace 𝓘(ℂ, F)) x₀
  have h0 : ∀ x (w : TangentSpace 𝓘(ℂ, F) x), θ ⟨x, 0⟩ = 0 := fun x _ ↦ by
    have := hlin x 1 0 0
    simp only [one_smul, add_zero, one_mul] at this
    linear_combination -this
  have hsrc : e.source ∈ 𝓝 p₀ := e.open_source.mem_nhds (FiberBundle.mem_trivializationAt_proj_source)
  have hloc : θ =ᶠ[𝓝 p₀] fun p ↦ L.symm (e p).2 *
      b4cov_coef θ x₀ (L 1) (extChartAt 𝓘(ℂ, F) x₀ p.proj) := by
    filter_upwards [hsrc] with p hp
    have hp' : p.proj ∈ (extChartAt 𝓘(ℂ, F) x₀).source := by
      rw [extChartAt_source]
      rw [TangentBundle.trivializationAt_source] at hp
      exact hp
    have hv : p.2 = b4cov_vec x₀ p.proj (L.symm (e p).2 • L 1) := by
      rw [← map_smul, smul_eq_mul, mul_one, ContinuousLinearEquiv.apply_symm_apply]
      exact (b4cov_vec_triv x₀ p.proj hp' p.2).symm
    rw [b4cov_coef, (extChartAt 𝓘(ℂ, F) x₀).left_inv hp']
    conv_lhs => rw [show p = ⟨p.proj, p.2⟩ from rfl, hv, b4cov_vec_smul x₀ _ hp']
    rw [← add_zero (L.symm (e p).2 • b4cov_vec x₀ p.proj (L 1)), hlin, h0 _ 0, add_zero]
  refine ContMDiffAt.congr_of_eventuallyEq ?_ hloc
  have h1 : ContMDiffAt 𝓘(ℂ, F).tangent 𝓘(ℂ, ℂ) ω (fun p : TangentBundle 𝓘(ℂ, F) M ↦
      L.symm (e p).2) p₀ := by
    have := (e.contMDiffOn (IB := 𝓘(ℂ, F)) (n := ω)).contMDiffAt hsrc
    exact (L.symm.contDiff.contMDiff.contMDiffAt).comp p₀ (contMDiffAt_snd.comp p₀ this)
  have h2 : ContMDiffAt 𝓘(ℂ, F).tangent 𝓘(ℂ, ℂ) ω (fun p : TangentBundle 𝓘(ℂ, F) M ↦
      b4cov_coef θ x₀ (L 1) (extChartAt 𝓘(ℂ, F) x₀ p.proj)) p₀ := by
    have hc : ContMDiffAt 𝓘(ℂ, F) 𝓘(ℂ, ℂ) ω (b4cov_coef θ x₀ (L 1))
        (extChartAt 𝓘(ℂ, F) x₀ x₀) := (hcoef x₀).contDiffAt.contMDiffAt
    have hφ : ContMDiffAt 𝓘(ℂ, F) 𝓘(ℂ, F) ω (extChartAt 𝓘(ℂ, F) x₀) x₀ :=
      contMDiffAt_extChartAt
    exact ContMDiffAt.comp (g := b4cov_coef θ x₀ (L 1))
      (f := fun p : TangentBundle 𝓘(ℂ, F) M ↦ extChartAt 𝓘(ℂ, F) x₀ p.proj) p₀ hc
      (hφ.comp p₀ (Bundle.contMDiffAt_proj (TangentSpace 𝓘(ℂ, F))))
  exact h1.mul h2

/-- At its own base point the trivialization is the identity on the fibre. -/
theorem b4cov_vec_self (y₀ : M) (u : F) : b4cov_vec y₀ y₀ u = u := by
  have h2 := b4cov_triv_eq_mfderiv y₀ y₀ (mem_extChartAt_source y₀)
    (u : TangentSpace 𝓘(ℂ, F) y₀)
  rw [mfderiv_extChartAt_self] at h2
  have h1 := b4cov_vec_triv y₀ y₀ (mem_extChartAt_source y₀) (u : TangentSpace 𝓘(ℂ, F) y₀)
  exact (congrArg (b4cov_vec y₀ y₀) h2).symm.trans h1

end Coef

section Pull

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {C : Type} [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
variable {E' : Type} [NormedAddCommGroup E'] [NormedSpace ℂ E']
variable {Y : Type} [TopologicalSpace Y] [ChartedSpace E' Y] [IsManifold 𝓘(ℂ, E') ω Y]

/-- The chart expression of `f` in the charts at `x₀` and `y₀`. -/
def b4cov_expr (E E' : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [ChartedSpace E C]
    [NormedAddCommGroup E'] [NormedSpace ℂ E'] [ChartedSpace E' Y] (f : C → Y) (x₀ : C)
    (y₀ : Y) : E → E' :=
  extChartAt 𝓘(ℂ, E') y₀ ∘ f ∘ (extChartAt 𝓘(ℂ, E) x₀).symm

/-- **The derivative in trivialization coordinates is the derivative of the chart expression.** -/
theorem b4cov_triv_mfderiv (f : C → Y) (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω f) (x₀ : C) (y₀ : Y)
    (x : C) (hx : x ∈ (extChartAt 𝓘(ℂ, E) x₀).source)
    (hfx : f x ∈ (extChartAt 𝓘(ℂ, E') y₀).source) (v : TangentSpace 𝓘(ℂ, E) x) :
    (trivializationAt E' (TangentSpace 𝓘(ℂ, E')) y₀ ⟨f x, mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E') f x v⟩).2 =
      fderiv ℂ (b4cov_expr E E' f x₀ y₀) (extChartAt 𝓘(ℂ, E) x₀ x)
        (trivializationAt E (TangentSpace 𝓘(ℂ, E)) x₀ ⟨x, v⟩).2 := by
  rw [b4cov_triv_eq_mfderiv y₀ (f x) hfx, b4cov_triv_eq_mfderiv x₀ x hx]
  have hx' : x ∈ (chartAt E x₀).source := by rwa [← extChartAt_source 𝓘(ℂ, E)]
  have hfx' : f x ∈ (chartAt E' y₀).source := by rwa [← extChartAt_source 𝓘(ℂ, E')]
  have hG : DifferentiableAt ℂ (b4cov_expr E E' f x₀ y₀) (extChartAt 𝓘(ℂ, E) x₀ x) := by
    have := b4cov_analyticAt_chart f hf x₀ y₀ (extChartAt 𝓘(ℂ, E) x₀ x)
      ((extChartAt 𝓘(ℂ, E) x₀).map_source hx) (by rwa [(extChartAt 𝓘(ℂ, E) x₀).left_inv hx])
    exact this.differentiableAt
  have hopen : IsOpen ((extChartAt 𝓘(ℂ, E) x₀).source ∩
      f ⁻¹' (extChartAt 𝓘(ℂ, E') y₀).source) :=
    (isOpen_extChartAt_source x₀).inter (hf.continuous.isOpen_preimage _
      (isOpen_extChartAt_source _))
  have heq : (extChartAt 𝓘(ℂ, E') y₀ ∘ f) =ᶠ[𝓝 x]
      b4cov_expr E E' f x₀ y₀ ∘ extChartAt 𝓘(ℂ, E) x₀ := by
    filter_upwards [hopen.mem_nhds ⟨hx, hfx⟩] with z hz
    simp only [b4cov_expr, Function.comp_apply, (extChartAt 𝓘(ℂ, E) x₀).left_inv hz.1]
  have h1 := mfderiv_comp_apply (g := extChartAt 𝓘(ℂ, E') y₀) (f := f) x
    (mdifferentiableAt_extChartAt hfx') ((hf x).mdifferentiableAt (by simp)) v
  rw [← h1, heq.mfderiv_eq]
  change (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E') (b4cov_expr E E' f x₀ y₀ ∘ extChartAt 𝓘(ℂ, E) x₀) x v : E') = _
  rw [mfderiv_comp_apply x hG.mdifferentiableAt (mdifferentiableAt_extChartAt hx'),
    mfderiv_eq_fderiv]
  rfl

theorem b4cov_vec_zero (y₀ y : Y) (hy : y ∈ (extChartAt 𝓘(ℂ, E') y₀).source) :
    b4cov_vec y₀ y (0 : E') = 0 := by
  have := b4cov_vec_smul y₀ y hy 0 (0 : E')
  rwa [zero_smul, zero_smul] at this

/-- **Non-critical points in arbitrary charts.** -/
theorem b4cov_mfderiv_ne_zero_iff_expr (f : C → Y) (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω f)
    (x₀ : C) (y₀ : Y) (x : C) (hx : x ∈ (extChartAt 𝓘(ℂ, E) x₀).source)
    (hfx : f x ∈ (extChartAt 𝓘(ℂ, E') y₀).source) :
    mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E') f x ≠ 0 ↔
      fderiv ℂ (b4cov_expr E E' f x₀ y₀) (extChartAt 𝓘(ℂ, E) x₀ x) ≠ 0 := by
  constructor
  · intro hd h0
    apply hd
    ext v
    have h1 := b4cov_triv_mfderiv f hf x₀ y₀ x hx hfx v
    rw [h0, ContinuousLinearMap.zero_apply] at h1
    have h2 := b4cov_vec_triv y₀ (f x) hfx (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E') f x v)
    rw [h1, b4cov_vec_zero y₀ (f x) hfx] at h2
    exact h2.symm
  · intro hG h0
    apply hG
    ext u
    have h1 := b4cov_triv_mfderiv f hf x₀ y₀ x hx hfx (b4cov_vec x₀ x u)
    rw [b4cov_triv_vec x₀ x hx u] at h1
    rw [← h1, h0, b4cov_triv_eq_mfderiv y₀ (f x) hfx]
    exact map_zero _

end Pull

section LocalInverse

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {E' : Type} [NormedAddCommGroup E'] [NormedSpace ℂ E']

/-- Complex differentiability near a point of a complex line gives analyticity. -/
theorem b4cov_analyticAt_of_differentiableOn (hE : Module.finrank ℂ E = 1) [CompleteSpace E']
    {g : E → E'} {S : Set E} {z : E} (hd : DifferentiableOn ℂ g S) (hS : S ∈ 𝓝 z) :
    AnalyticAt ℂ g z := by
  set L := b4cov_lineEquiv hE
  have h1 : DifferentiableOn ℂ (g ∘ L) (L ⁻¹' S) := hd.comp L.differentiableOn (fun _ h ↦ h)
  have h2 : L ⁻¹' S ∈ 𝓝 (L.symm z) :=
    L.continuous.continuousAt.preimage_mem_nhds (by rwa [L.apply_symm_apply])
  have h3 := h1.analyticAt h2
  have h4 : g = (g ∘ L) ∘ L.symm := by funext w; simp
  rw [h4]
  exact h3.comp (L.symm.toContinuousLinearMap.analyticAt z)

/-- **Analytic local inverse** of an analytic map of complex lines with nonzero derivative. -/
theorem b4cov_exists_localInverse (hE : Module.finrank ℂ E = 1) (hE' : Module.finrank ℂ E' = 1)
    {G : E → E'} {t₁ : E} (hG : AnalyticAt ℂ G t₁) (hG' : fderiv ℂ G t₁ ≠ 0) :
    ∃ s : E' → E, AnalyticAt ℂ s (G t₁) ∧ s (G t₁) = t₁ ∧ (∀ᶠ w in 𝓝 (G t₁), G (s w) = w) ∧
      ∀ᶠ t in 𝓝 t₁, s (G t) = t := by
  have : FiniteDimensional ℂ E := Module.finite_of_finrank_eq_succ hE
  have : FiniteDimensional ℂ E' := Module.finite_of_finrank_eq_succ hE'
  have := FiniteDimensional.complete ℂ E
  have := FiniteDimensional.complete ℂ E'
  -- invertible derivatives near `t₁`
  have hev : ∀ᶠ t in 𝓝 t₁, AnalyticAt ℂ G t ∧ fderiv ℂ G t ≠ 0 :=
    hG.eventually_analyticAt.and (hG.fderiv.continuousAt.eventually_ne hG')
  let equivAt : ∀ t, fderiv ℂ G t ≠ 0 → E ≃L[ℂ] E' := fun t ht ↦
    (LinearEquiv.ofBijective (fderiv ℂ G t : E →ₗ[ℂ] E')
      (b4cov_bijective_of_ne_zero hE hE' _ ht)).toContinuousLinearEquiv
  have hcoe : ∀ t ht, ((equivAt t ht : E ≃L[ℂ] E') : E →L[ℂ] E') = fderiv ℂ G t :=
    fun t ht ↦ by ext; rfl
  have hstrict : HasStrictFDerivAt G ((equivAt t₁ hG' : E ≃L[ℂ] E') : E →L[ℂ] E') t₁ := by
    rw [hcoe t₁ hG']; exact hG.hasStrictFDerivAt
  let K := hstrict.toOpenPartialHomeomorph G
  have hK : (K : E → E') = G := hstrict.toOpenPartialHomeomorph_coe
  have ht₁ : t₁ ∈ K.source := hstrict.mem_toOpenPartialHomeomorph_source
  have hw₁ : G t₁ ∈ K.target := by rw [← hK]; exact K.map_source ht₁
  have hsym : K.symm (G t₁) = t₁ := by
    rw [← hK]; exact K.left_inv ht₁
  refine ⟨K.symm, ?_, hsym, ?_, ?_⟩
  · -- `K.symm` is differentiable near `G t₁`
    have hN : ∀ᶠ w in 𝓝 (G t₁), w ∈ K.target ∧ (AnalyticAt ℂ G (K.symm w) ∧
        fderiv ℂ G (K.symm w) ≠ 0) :=
      Filter.Eventually.and (K.open_target.mem_nhds hw₁ : ∀ᶠ w in 𝓝 (G t₁), w ∈ K.target)
        ((K.symm.continuousAt hw₁).tendsto.eventually
          (p := fun t ↦ AnalyticAt ℂ G t ∧ fderiv ℂ G t ≠ 0) (by rw [hsym]; exact hev))
    obtain ⟨S, hSmem, hS⟩ := hN.exists_mem
    refine b4cov_analyticAt_of_differentiableOn hE' (S := S) (fun w hw ↦ ?_) hSmem
    obtain ⟨hwt, han, hne⟩ := hS w hw
    have hd : HasStrictFDerivAt K ((equivAt _ hne : E ≃L[ℂ] E') : E →L[ℂ] E') (K.symm w) := by
      rw [hcoe _ hne, hK]; exact han.hasStrictFDerivAt
    exact (K.hasStrictFDerivAt_symm hwt hd).differentiableAt.differentiableWithinAt
  · filter_upwards [K.open_target.mem_nhds hw₁] with w hw
    rw [← hK]; exact K.right_inv hw
  · filter_upwards [K.open_source.mem_nhds ht₁] with t ht
    rw [← hK]; exact K.left_inv ht

/-- **Removable singularities on a complex line**: an analytic function on a punctured
neighborhood, bounded there, whose value at the centre is the limit, is analytic. -/
theorem b4cov_analyticAt_of_punctured (hE : Module.finrank ℂ E = 1) {g : E → ℂ} {w₀ : E}
    (hd : ∀ᶠ w in 𝓝[≠] w₀, AnalyticAt ℂ g w) {M : ℝ} (hb : ∀ᶠ w in 𝓝[≠] w₀, ‖g w‖ ≤ M)
    (hlim : g w₀ = limUnder (𝓝[≠] (0 : ℂ)) (fun τ ↦ g (w₀ + b4cov_lineEquiv hE τ))) :
    AnalyticAt ℂ g w₀ := by
  set L := b4cov_lineEquiv hE
  let Φ : ℂ ≃ₜ E := L.toHomeomorph.trans (Homeomorph.addLeft w₀)
  have hΦ : ∀ τ, Φ τ = w₀ + L τ := fun τ ↦ rfl
  have hΦ0 : Φ 0 = w₀ := by simp [hΦ]
  set h : ℂ → ℂ := fun τ ↦ g (w₀ + L τ)
  have hA : ∀ τ, AnalyticAt ℂ (fun σ : ℂ ↦ w₀ + L σ) τ := fun τ ↦
    analyticAt_const.add (L.toContinuousLinearMap.analyticAt τ)
  have hev : ∀ᶠ τ in 𝓝[≠] (0 : ℂ), AnalyticAt ℂ g (w₀ + L τ) ∧ ‖g (w₀ + L τ)‖ ≤ M := by
    have := hd.and hb
    rw [← hΦ0, ← Φ.map_punctured_nhds_eq] at this
    exact Filter.eventually_map.1 this
  rw [eventually_nhdsWithin_iff] at hev
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  have hdiff : DifferentiableOn ℂ h (Metric.ball 0 r \ {0}) := fun τ hτ ↦
    (AnalyticAt.comp (g := g) (f := fun σ : ℂ ↦ w₀ + L σ) (hball τ hτ.1 hτ.2).1
      (hA τ)).differentiableAt.differentiableWithinAt
  have hbdd : BddAbove (norm ∘ h '' (Metric.ball 0 r \ {0})) := by
    refine ⟨M, ?_⟩
    rintro _ ⟨τ, hτ, rfl⟩
    exact (hball τ hτ.1 hτ.2).2
  have hup := Complex.differentiableOn_update_limUnder_of_bddAbove (Metric.ball_mem_nhds 0 hr)
    hdiff hbdd
  have heq : Function.update h 0 (limUnder (𝓝[≠] (0 : ℂ)) h) = h := by
    rw [Function.update_eq_self_iff]
    show _ = g (w₀ + L 0)
    rw [map_zero, add_zero]
    exact hlim.symm
  rw [heq] at hup
  have hh0 : AnalyticAt ℂ h 0 := hup.analyticAt (Metric.ball_mem_nhds 0 hr)
  have hgh : g = h ∘ fun w ↦ L.symm (w - w₀) := by
    funext w
    simp [h]
  rw [hgh]
  have hB : AnalyticAt ℂ (fun w ↦ L.symm (w - w₀)) w₀ :=
    (L.symm.toContinuousLinearMap.analyticAt _).comp (analyticAt_id.sub analyticAt_const)
  exact AnalyticAt.comp (g := h) (f := fun w ↦ L.symm (w - w₀))
    (show AnalyticAt ℂ h ((fun w ↦ L.symm (w - w₀)) w₀) by simpa using hh0) hB

end LocalInverse

section Descent

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {C : Type} [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
variable {E' : Type} [NormedAddCommGroup E'] [NormedSpace ℂ E']
variable {Y : Type} [TopologicalSpace Y] [ChartedSpace E' Y] [IsManifold 𝓘(ℂ, E') ω Y]
variable {G : Type} [Group G] [MulAction G C]

/-- A preimage of the derivative (an inverse when `df_x` is bijective). -/
def b4cov_dinv (E E' : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [ChartedSpace E C]
    [NormedAddCommGroup E'] [NormedSpace ℂ E'] [ChartedSpace E' Y] (f : C → Y) (x : C)
    (v : E') : E :=
  Function.invFun (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E') f x) v

omit [IsManifold 𝓘(ℂ, E) ω C] [IsManifold 𝓘(ℂ, E') ω Y] in
theorem b4cov_mfderiv_dinv (f : C → Y) (x : C)
    (hx : Function.Bijective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E') f x)) (v : E') :
    (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E') f x) (b4cov_dinv E E' f x v) = v :=
  Function.invFun_eq (hx.2 v)

omit [IsManifold 𝓘(ℂ, E) ω C] [IsManifold 𝓘(ℂ, E') ω Y] in
theorem b4cov_dinv_mfderiv (f : C → Y) (x : C)
    (hx : Function.Bijective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E') f x)) (w : E) :
    b4cov_dinv E E' f x ((mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E') f x) w) = w :=
  Function.leftInverse_invFun hx.1 w

omit [IsManifold 𝓘(ℂ, E) ω C] [IsManifold 𝓘(ℂ, E') ω Y] in
theorem b4cov_dinv_linear (f : C → Y) (x : C)
    (hx : Function.Bijective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E') f x)) (a : ℂ) (v w : E') :
    b4cov_dinv E E' f x (a • v + w) = a • b4cov_dinv E E' f x v + b4cov_dinv E E' f x w := by
  apply hx.1
  rw [b4cov_mfderiv_dinv f x hx]
  erw [(mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E') f x).map_add, (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E') f x).map_smul,
    b4cov_mfderiv_dinv f x hx, b4cov_mfderiv_dinv f x hx]
  rfl

/-- **The descended value is independent of the preimage** (invariance of `θ`). -/
theorem b4cov_descent_wellDefined
    (hG : ∀ g : G, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x : C ↦ g • x))
    (f : C → Y) (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω f) (hgal : b4_IsGaloisCover G f)
    (θ : TangentBundle 𝓘(ℂ, E) C → ℂ) (hθ : θ ∈ b4_invariantForms E C G) (x x' : C)
    (hxx' : f x = f x')
    (hx : Function.Bijective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E') f x))
    (hx' : Function.Bijective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E') f x')) (v : E') :
    θ ⟨x', b4cov_dinv E E' f x' v⟩ = θ ⟨x, b4cov_dinv E E' f x v⟩ := by
  obtain ⟨g, rfl⟩ := hgal.2 x x' hxx'
  obtain ⟨k, rfl⟩ : ∃ k : G, g = k⁻¹ := ⟨g⁻¹, (inv_inv g).symm⟩
  -- invariance of `θ` under `k`
  have hinv : ∀ (z : C) (w : E), θ ⟨k⁻¹ • z, mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E) (fun y : C ↦ k⁻¹ • y) z w⟩ =
      θ ⟨z, w⟩ := by
    intro z w
    have h1 := (Submodule.mem_iInf _).1 hθ.2 k
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at h1
    exact congrFun h1 ⟨z, w⟩
  -- the chain rule for `f ∘ k⁻¹ = f`
  have hcomp : f ∘ (fun y : C ↦ k⁻¹ • y) = f := funext fun y ↦ hgal.1 k⁻¹ y
  have hchain : ∀ w : E, mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E') f (k⁻¹ • x)
      (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E) (fun y : C ↦ k⁻¹ • y) x w) =
        mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E') f x w := by
    intro w
    have := mfderiv_comp_apply (g := f) (f := fun y : C ↦ k⁻¹ • y) x
      ((hf _).mdifferentiableAt (by simp)) (((hG k⁻¹) x).mdifferentiableAt (by simp)) w
    rw [hcomp] at this
    exact this.symm
  have hd : b4cov_dinv E E' f (k⁻¹ • x) v =
      mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E) (fun y : C ↦ k⁻¹ • y) x (b4cov_dinv E E' f x v) := by
    apply hx'.1
    rw [b4cov_mfderiv_dinv f _ hx', hchain, b4cov_mfderiv_dinv f x hx]
  rw [hd]
  exact hinv x _

/-- **Fibres of a Galois cover are uniformly unramified.** -/
theorem b4cov_unram_of_fiber
    (hG : ∀ g : G, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x : C ↦ g • x))
    (f : C → Y) (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω f) (hgal : b4_IsGaloisCover G f) (x x' : C)
    (hxx' : f x = f x') (hx : mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E') f x ≠ 0) :
    mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E') f x' ≠ 0 := by
  obtain ⟨g, rfl⟩ := hgal.2 x x' hxx'
  intro h0
  apply hx
  have hcomp : f ∘ (fun y : C ↦ g • y) = f := funext fun y ↦ hgal.1 g y
  have := mfderiv_comp x (g := f) (f := fun y : C ↦ g • y)
    ((hf _).mdifferentiableAt (by simp)) (((hG g) x).mdifferentiableAt (by simp))
  rw [hcomp] at this
  rw [this, h0, ContinuousLinearMap.zero_comp]
  rfl

/-- **The descended function** on the tangent bundle of `Y` (meaningful over regular values). -/
def b4cov_descend0 [Nonempty C] (f : C → Y) (θ : TangentBundle 𝓘(ℂ, E) C → ℂ) :
    TangentBundle 𝓘(ℂ, E') Y → ℂ :=
  fun p ↦ θ ⟨Function.invFun f p.proj, b4cov_dinv E E' f (Function.invFun f p.proj) p.2⟩

theorem b4cov_descend0_apply [Nonempty C] (hE : Module.finrank ℂ E = 1)
    (hE' : Module.finrank ℂ E' = 1)
    (hG : ∀ g : G, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x : C ↦ g • x))
    (f : C → Y) (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω f) (hgal : b4_IsGaloisCover G f)
    (θ : TangentBundle 𝓘(ℂ, E) C → ℂ) (hθ : θ ∈ b4_invariantForms E C G) (x : C)
    (hx : mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E') f x ≠ 0) (v : E') :
    b4cov_descend0 f θ ⟨f x, v⟩ = θ ⟨x, b4cov_dinv E E' f x v⟩ := by
  have hrange : f x ∈ range f := mem_range_self x
  have hx₀ : f (Function.invFun f (f x)) = f x := Function.invFun_eq hrange
  have hd₀ := b4cov_unram_of_fiber hG f hf hgal x _ hx₀.symm hx
  exact b4cov_descent_wellDefined hG f hf hgal θ hθ x _ hx₀.symm
    (b4cov_bijective_of_ne_zero hE hE' _ hx) (b4cov_bijective_of_ne_zero hE hE' _ hd₀) v

/-- **The descended coefficient is analytic at unramified values.** -/
theorem b4cov_descend0_coef_analyticAt [Nonempty C] (hE : Module.finrank ℂ E = 1)
    (hE' : Module.finrank ℂ E' = 1)
    (hG : ∀ g : G, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x : C ↦ g • x))
    (f : C → Y) (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω f) (hgal : b4_IsGaloisCover G f)
    (θ : TangentBundle 𝓘(ℂ, E) C → ℂ) (hθ : θ ∈ b4_invariantForms E C G) (y₀ : Y) (x₁ : C)
    (hx₁ : f x₁ ∈ (extChartAt 𝓘(ℂ, E') y₀).source) (hd₁ : mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E') f x₁ ≠ 0) :
    AnalyticAt ℂ (b4cov_coef (b4cov_descend0 f θ) y₀ (b4cov_lineEquiv hE' 1))
      (extChartAt 𝓘(ℂ, E') y₀ (f x₁)) := by
  have : FiniteDimensional ℂ E := Module.finite_of_finrank_eq_succ hE
  have : FiniteDimensional ℂ E' := Module.finite_of_finrank_eq_succ hE'
  have := FiniteDimensional.complete ℂ E
  have := FiniteDimensional.complete ℂ E'
  set L := b4cov_lineEquiv hE
  set L' := b4cov_lineEquiv hE'
  set φ := extChartAt 𝓘(ℂ, E) x₁ with hφdef
  set ψ := extChartAt 𝓘(ℂ, E') y₀ with hψdef
  set Gx := b4cov_expr E E' f x₁ y₀ with hGxdef
  have hx₁s : x₁ ∈ φ.source := mem_extChartAt_source x₁
  set t₁ := φ x₁
  have hGt₁ : Gx t₁ = ψ (f x₁) := by
    show ψ (f (φ.symm (φ x₁))) = ψ (f x₁)
    rw [φ.left_inv hx₁s]
  let T : Set E := φ.target ∩ φ.symm ⁻¹' (f ⁻¹' ψ.source)
  have hTo : IsOpen T := (continuousOn_extChartAt_symm x₁).isOpen_inter_preimage
    (isOpen_extChartAt_target x₁) (hf.continuous.isOpen_preimage _ (isOpen_extChartAt_source _))
  have ht₁T : t₁ ∈ T := ⟨φ.map_source hx₁s, by
    simp only [mem_preimage, t₁, φ.left_inv hx₁s]; exact hx₁⟩
  have hGan : AnalyticAt ℂ Gx t₁ :=
    b4cov_analyticAt_chart f hf x₁ y₀ t₁ (φ.map_source hx₁s) (by rw [φ.left_inv hx₁s]; exact hx₁)
  have hG' : fderiv ℂ Gx t₁ ≠ 0 :=
    (b4cov_mfderiv_ne_zero_iff_expr f hf x₁ y₀ x₁ hx₁s hx₁).1 hd₁
  obtain ⟨σ, hσan, hσ₁, hGσ, -⟩ := b4cov_exists_localInverse hE hE' hGan hG'
  let κ : E → ℂ := fun t ↦ L'.symm (fderiv ℂ Gx t (L 1))
  have hκan : AnalyticAt ℂ κ t₁ :=
    (L'.symm.toContinuousLinearMap.analyticAt _).comp
      (((ContinuousLinearMap.apply ℂ E' (L 1)).analyticAt _).comp hGan.fderiv)
  have hκne : ∀ t, fderiv ℂ Gx t ≠ 0 → κ t ≠ 0 := by
    intro t ht h0
    apply ht
    ext v
    have h1 : fderiv ℂ Gx t (L 1) = 0 := by
      have := congrArg L' h0
      simpa [κ] using this
    have hv : v = L.symm v • L 1 := by
      rw [← map_smul, smul_eq_mul, mul_one, ContinuousLinearEquiv.apply_symm_apply]
    rw [hv, map_smul, h1, smul_zero]
    rfl
  -- the local model
  let R : E' → ℂ := fun w ↦ (κ (σ w))⁻¹ * b4cov_coef θ x₁ (L 1) (σ w)
  have hσt₁ : σ (Gx t₁) = t₁ := hσ₁
  have hRan : AnalyticAt ℂ R (Gx t₁) := by
    have h1 : AnalyticAt ℂ (κ ∘ σ) (Gx t₁) := (by rw [hσt₁]; exact hκan : AnalyticAt ℂ κ (σ (Gx t₁))).comp hσan
    have h2 : AnalyticAt ℂ (b4cov_coef θ x₁ (L 1) ∘ σ) (Gx t₁) :=
      (by rw [hσt₁]; exact b4cov_coef_analyticAt θ hθ.1.1 x₁ (L 1) t₁ (φ.map_source hx₁s) :
        AnalyticAt ℂ (b4cov_coef θ x₁ (L 1)) (σ (Gx t₁))).comp hσan
    have h3 : (κ ∘ σ) (Gx t₁) ≠ 0 := by
      simp only [Function.comp_apply, hσt₁]; exact hκne t₁ hG'
    exact (h1.inv h3).mul h2
  rw [← hGt₁]
  refine hRan.congr ?_
  have hevt : ∀ᶠ t in 𝓝 t₁, t ∈ T ∧ fderiv ℂ Gx t ≠ 0 :=
    Filter.Eventually.and (hTo.mem_nhds ht₁T : ∀ᶠ t in 𝓝 t₁, t ∈ T)
      (hGan.fderiv.continuousAt.eventually_ne hG')
  have hevw : ∀ᶠ w in 𝓝 (Gx t₁), σ w ∈ T ∧ fderiv ℂ Gx (σ w) ≠ 0 :=
    hσan.continuousAt.tendsto.eventually (p := fun t ↦ t ∈ T ∧ fderiv ℂ Gx t ≠ 0)
      (by rw [hσt₁]; exact hevt)
  filter_upwards [hGσ, hevw] with w hw1 ⟨hwT, hwd⟩
  set t := σ w
  have hxs : φ.symm t ∈ φ.source := φ.map_target hwT.1
  set x := φ.symm t
  have hfx : f x ∈ ψ.source := hwT.2
  have hφx : φ x = t := φ.right_inv hwT.1
  have hψw : ψ.symm w = f x := by
    rw [← hw1]
    exact ψ.left_inv hfx
  have hdx : mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E') f x ≠ 0 :=
    (b4cov_mfderiv_ne_zero_iff_expr f hf x₁ y₀ x hxs hfx).2 (by rw [hφx]; exact hwd)
  have hbij := b4cov_bijective_of_ne_zero hE hE' _ hdx
  have hκt : κ t ≠ 0 := hκne t hwd
  have hdf : mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E') f x (b4cov_vec x₁ x (L 1)) =
      κ t • b4cov_vec y₀ (f x) (L' 1) := by
    rw [← b4cov_vec_triv y₀ (f x) hfx (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E') f x (b4cov_vec x₁ x (L 1))),
      b4cov_triv_mfderiv f hf x₁ y₀ x hxs hfx, b4cov_triv_vec x₁ x hxs, hφx,
      ← b4cov_vec_smul y₀ (f x) hfx]
    congr 1
    show fderiv ℂ Gx t (L 1) = L'.symm (fderiv ℂ Gx t (L 1)) • L' 1
    rw [← map_smul, smul_eq_mul, mul_one, ContinuousLinearEquiv.apply_symm_apply]
  have hdinv : b4cov_dinv E E' f x (b4cov_vec y₀ (f x) (L' 1)) =
      (κ t)⁻¹ • b4cov_vec x₁ x (L 1) := by
    apply hbij.1
    erw [b4cov_mfderiv_dinv f x hbij, (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E') f x).map_smul, hdf, smul_smul,
      inv_mul_cancel₀ hκt, one_smul]
  have h0θ : θ ⟨x, 0⟩ = 0 := by
    have := hθ.1.2 x 1 0 0
    simp only [one_smul, add_zero, one_mul] at this
    linear_combination -this
  have hgen : ∀ (y : Y) (_ : y = f x), b4cov_descend0 f θ ⟨y, b4cov_vec y₀ y (L' 1)⟩ =
      b4cov_descend0 f θ ⟨f x, b4cov_vec y₀ (f x) (L' 1)⟩ := by
    rintro _ rfl; rfl
  symm
  change b4cov_descend0 f θ ⟨ψ.symm w, b4cov_vec y₀ (ψ.symm w) (L' 1)⟩ = R w
  rw [hgen _ hψw]
  erw [b4cov_descend0_apply hE hE' hG f hf hgal θ hθ x hdx]
  rw [hdinv]
  have := hθ.1.2 x (κ t)⁻¹ (b4cov_vec x₁ x (L 1)) 0
  rw [add_zero, h0θ, add_zero] at this
  rw [this]
  rfl

/-- Invariance of `θ ∈ Ω¹(C)^G` in the form `θ(g z, dg w) = θ(z, w)`. -/
theorem b4cov_invariant_apply (θ : TangentBundle 𝓘(ℂ, E) C → ℂ)
    (hθ : θ ∈ b4_invariantForms E C G) (g : G) (z : C) (w : E) :
    θ ⟨g • z, mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E) (fun y : C ↦ g • y) z w⟩ = θ ⟨z, w⟩ := by
  have h1 := (Submodule.mem_iInf _).1 hθ.2 g⁻¹
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at h1
  have := congrFun h1 ⟨z, w⟩
  change θ ⟨g⁻¹⁻¹ • z, mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E) (fun y : C ↦ g⁻¹⁻¹ • y) z w⟩ = θ ⟨z, w⟩ at this
  rw [inv_inv] at this
  exact this

/-- **An invariant form vanishes to order `≥ |G_x| - 1` at `x`** (in the chart at `x`). -/
theorem b4cov_coef_order_ge [Finite G] (hE : Module.finrank ℂ E = 1)
    (hG : ∀ g : G, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x : C ↦ g • x))
    (θ : TangentBundle 𝓘(ℂ, E) C → ℂ) (hθ : θ ∈ b4_invariantForms E C G) (x₀ : C) (h : G)
    (hh : b4_IsRotGen E x₀ h) :
    ((orderOf h - 1 : ℕ) : ℕ∞) ≤ analyticOrderAt
      (fun τ : ℂ ↦ b4cov_coef θ x₀ (b4cov_lineEquiv hE 1)
        (extChartAt 𝓘(ℂ, E) x₀ x₀ + b4cov_lineEquiv hE τ)) 0 := by
  have : FiniteDimensional ℂ E := Module.finite_of_finrank_eq_succ hE
  have := FiniteDimensional.complete ℂ E
  set L := b4cov_lineEquiv hE
  set φ := extChartAt 𝓘(ℂ, E) x₀
  set z₀ := φ x₀
  set Ψ := b4cov_expr E E (fun y : C ↦ h • y) x₀ x₀
  set α := b4cov_coef θ x₀ (L 1)
  have hx₀ : x₀ ∈ φ.source := mem_extChartAt_source x₀
  have hhx : h • x₀ = x₀ := hh.1
  have hΨ0 : Ψ z₀ = z₀ := by
    show φ (h • φ.symm (φ x₀)) = φ x₀
    rw [φ.left_inv hx₀, hhx]
  have hΨan : AnalyticAt ℂ Ψ z₀ :=
    b4cov_analyticAt_chart _ (hG h) x₀ x₀ z₀ (φ.map_source hx₀)
      (by show h • φ.symm (φ x₀) ∈ φ.source; rw [φ.left_inv hx₀, hhx]; exact hx₀)
  have hαan : AnalyticAt ℂ α z₀ := b4cov_coef_analyticAt θ hθ.1.1 x₀ (L 1) z₀ (φ.map_source hx₀)
  -- the derivative of `Ψ` at the fixed point
  have hder : fderiv ℂ Ψ z₀ (L 1) = Complex.exp (2 * Real.pi * Complex.I / (orderOf h : ℂ)) • L 1 := by
    have hmd : MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, E) (fun y : C ↦ h • y) x₀ :=
      ((hG h) x₀).mdifferentiableAt (by simp)
    have hab := hmd.mfderiv_abuse
    rw [modelWithCornersSelf_coe, range_id, fderivWithin_univ] at hab
    have hw : writtenInExtChartAt 𝓘(ℂ, E) 𝓘(ℂ, E) x₀ (fun y : C ↦ h • y) = Ψ := by
      simp only [writtenInExtChartAt, hhx]; rfl
    rw [hw] at hab
    rw [← hab]
    exact hh.2.2 (L 1)
  set ζ := Complex.exp (2 * Real.pi * Complex.I / (orderOf h : ℂ))
  have hζ : IsPrimitiveRoot ζ (orderOf h) := Complex.isPrimitiveRoot_exp _ (orderOf_pos h).ne'
  let μ : E → ℂ := fun t ↦ L.symm (fderiv ℂ Ψ t (L 1))
  -- the relation `α = μ · (α ∘ Ψ)` near the fixed point
  let T : Set E := φ.target ∩ φ.symm ⁻¹' ((fun y : C ↦ h • y) ⁻¹' φ.source)
  have hTo : IsOpen T := (continuousOn_extChartAt_symm x₀).isOpen_inter_preimage
    (isOpen_extChartAt_target x₀) ((hG h).continuous.isOpen_preimage _ (isOpen_extChartAt_source _))
  have hz₀T : z₀ ∈ T := ⟨φ.map_source hx₀, by
    show h • φ.symm (φ x₀) ∈ φ.source; rw [φ.left_inv hx₀, hhx]; exact hx₀⟩
  have hrel : ∀ t ∈ T, α t = μ t * α (Ψ t) := by
    intro t ht
    have hxs : φ.symm t ∈ φ.source := φ.map_target ht.1
    set x := φ.symm t
    have hhxs : h • x ∈ φ.source := ht.2
    have hdh : mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E) (fun y : C ↦ h • y) x (b4cov_vec x₀ x (L 1)) =
        μ t • b4cov_vec x₀ (h • x) (L 1) := by
      rw [← b4cov_vec_triv x₀ (h • x) hhxs (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E) (fun y : C ↦ h • y) x
          (b4cov_vec x₀ x (L 1))),
        b4cov_triv_mfderiv (fun y : C ↦ h • y) (hG h) x₀ x₀ x hxs hhxs,
        b4cov_triv_vec x₀ x hxs, φ.right_inv ht.1, ← b4cov_vec_smul x₀ (h • x) hhxs]
      congr 1
      show fderiv ℂ Ψ t (L 1) = L.symm (fderiv ℂ Ψ t (L 1)) • L 1
      rw [← map_smul, smul_eq_mul, mul_one, ContinuousLinearEquiv.apply_symm_apply]
    have h0θ : θ ⟨h • x, 0⟩ = 0 := by
      have := hθ.1.2 (h • x) 1 0 0
      simp only [one_smul, add_zero, one_mul] at this
      linear_combination -this
    have hgen : ∀ (z : C) (_ : z = h • x), θ ⟨z, b4cov_vec x₀ z (L 1)⟩ =
        θ ⟨h • x, b4cov_vec x₀ (h • x) (L 1)⟩ := by rintro _ rfl; rfl
    have hΨt : φ.symm (Ψ t) = h • x := φ.left_inv hhxs
    change θ ⟨x, b4cov_vec x₀ x (L 1)⟩ =
      μ t * θ ⟨φ.symm (Ψ t), b4cov_vec x₀ (φ.symm (Ψ t)) (L 1)⟩
    rw [hgen _ hΨt]
    have hinv := b4cov_invariant_apply θ hθ h x (b4cov_vec x₀ x (L 1))
    erw [hdh] at hinv
    have := hθ.1.2 (h • x) (μ t) (b4cov_vec x₀ (h • x) (L 1)) 0
    rw [add_zero, h0θ, add_zero] at this
    exact hinv.symm.trans this
  -- transport to `ℂ`
  have hA : AnalyticAt ℂ (fun τ : ℂ ↦ z₀ + L τ) 0 :=
    analyticAt_const.add (L.toContinuousLinearMap.analyticAt 0)
  have hA0 : (fun τ : ℂ ↦ z₀ + L τ) 0 = z₀ := by simp
  have ha : AnalyticAt ℂ (fun τ : ℂ ↦ α (z₀ + L τ)) 0 :=
    AnalyticAt.comp (g := α) (f := fun τ : ℂ ↦ z₀ + L τ)
      (by simp only [map_zero, add_zero]; exact hαan) hA
  have hμan : AnalyticAt ℂ μ z₀ :=
    (L.symm.toContinuousLinearMap.analyticAt _).comp
      (((ContinuousLinearMap.apply ℂ E (L 1)).analyticAt _).comp hΨan.fderiv)
  have hm : AnalyticAt ℂ (fun τ : ℂ ↦ μ (z₀ + L τ)) 0 :=
    AnalyticAt.comp (g := μ) (f := fun τ : ℂ ↦ z₀ + L τ)
      (by simp only [map_zero, add_zero]; exact hμan) hA
  have hp := b4cov_transport_analyticAt hE hE hΨan
  have hp0 := b4cov_transport_zero hE hE Ψ z₀
  have hLζ : L.symm (ζ • L 1) = ζ := by rw [map_smul, ContinuousLinearEquiv.symm_apply_apply,
    smul_eq_mul, mul_one]
  have hp' : deriv (b4cov_transport hE hE Ψ z₀) 0 = ζ := by
    rw [b4cov_transport_deriv hE hE 0 (by simpa using hΨan.differentiableAt)]
    simp only [map_zero, add_zero]
    rw [hder, hLζ]
  have hm0 : (fun τ : ℂ ↦ μ (z₀ + L τ)) 0 = ζ := by
    simp only [map_zero, add_zero, μ]; rw [hder, hLζ]
  have hTA : ∀ᶠ τ in 𝓝 (0 : ℂ), z₀ + L τ ∈ T :=
    hA.continuousAt.tendsto.eventually (p := fun t ↦ t ∈ T)
      (by simp only [map_zero, add_zero]; exact hTo.mem_nhds hz₀T)
  have hrel' : ∀ᶠ τ in 𝓝 (0 : ℂ), α (z₀ + L τ) =
      μ (z₀ + L τ) * α (z₀ + L (b4cov_transport hE hE Ψ z₀ τ)) := by
    filter_upwards [hTA] with τ hτ
    have hzL : z₀ + L (b4cov_transport hE hE Ψ z₀ τ) = Ψ (z₀ + L τ) := by
      show z₀ + L (L.symm (Ψ (z₀ + L τ)) - L.symm (Ψ z₀)) = Ψ (z₀ + L τ)
      rw [map_sub, L.apply_symm_apply, L.apply_symm_apply, hΨ0]
      abel
    rw [hzL]
    exact hrel _ hτ
  exact b4cov_order_ge_of_rel ha hm hp hp0 hp' hm0 hrel' hζ

/-- **The descended coefficient at an unramified point**, in charts at `x₁` and `y₀`. -/
theorem b4cov_descend0_coef_eq [Nonempty C] (hE : Module.finrank ℂ E = 1)
    (hE' : Module.finrank ℂ E' = 1)
    (hG : ∀ g : G, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x : C ↦ g • x))
    (f : C → Y) (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω f) (hgal : b4_IsGaloisCover G f)
    (θ : TangentBundle 𝓘(ℂ, E) C → ℂ) (hθ : θ ∈ b4_invariantForms E C G) (x₁ : C) (y₀ : Y)
    (x : C) (hxs : x ∈ (extChartAt 𝓘(ℂ, E) x₁).source)
    (hfx : f x ∈ (extChartAt 𝓘(ℂ, E') y₀).source) (hdx : mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E') f x ≠ 0) :
    b4cov_coef (b4cov_descend0 f θ) y₀ (b4cov_lineEquiv hE' 1) (extChartAt 𝓘(ℂ, E') y₀ (f x)) =
      ((b4cov_lineEquiv hE').symm (fderiv ℂ (b4cov_expr E E' f x₁ y₀)
        (extChartAt 𝓘(ℂ, E) x₁ x) (b4cov_lineEquiv hE 1)))⁻¹ *
        b4cov_coef θ x₁ (b4cov_lineEquiv hE 1) (extChartAt 𝓘(ℂ, E) x₁ x) := by
  set L := b4cov_lineEquiv hE
  set L' := b4cov_lineEquiv hE'
  set φ := extChartAt 𝓘(ℂ, E) x₁
  set ψ := extChartAt 𝓘(ℂ, E') y₀
  set Gx := b4cov_expr E E' f x₁ y₀
  set κ := L'.symm (fderiv ℂ Gx (φ x) (L 1))
  have hbij := b4cov_bijective_of_ne_zero hE hE' _ hdx
  have hGne : fderiv ℂ Gx (φ x) ≠ 0 :=
    (b4cov_mfderiv_ne_zero_iff_expr f hf x₁ y₀ x hxs hfx).1 hdx
  have hκ : κ ≠ 0 := by
    intro h0
    apply hGne
    ext v
    have h1 : fderiv ℂ Gx (φ x) (L 1) = 0 := by
      have := congrArg L' h0
      simpa [κ] using this
    have hv : v = L.symm v • L 1 := by
      rw [← map_smul, smul_eq_mul, mul_one, ContinuousLinearEquiv.apply_symm_apply]
    rw [hv, map_smul, h1, smul_zero]
    rfl
  have hdf : mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E') f x (b4cov_vec x₁ x (L 1)) =
      κ • b4cov_vec y₀ (f x) (L' 1) := by
    rw [← b4cov_vec_triv y₀ (f x) hfx (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E') f x (b4cov_vec x₁ x (L 1))),
      b4cov_triv_mfderiv f hf x₁ y₀ x hxs hfx, b4cov_triv_vec x₁ x hxs,
      ← b4cov_vec_smul y₀ (f x) hfx]
    congr 1
    show fderiv ℂ Gx (φ x) (L 1) = L'.symm (fderiv ℂ Gx (φ x) (L 1)) • L' 1
    rw [← map_smul, smul_eq_mul, mul_one, ContinuousLinearEquiv.apply_symm_apply]
  have hdinv : b4cov_dinv E E' f x (b4cov_vec y₀ (f x) (L' 1)) = κ⁻¹ • b4cov_vec x₁ x (L 1) := by
    apply hbij.1
    erw [b4cov_mfderiv_dinv f x hbij, (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E') f x).map_smul, hdf, smul_smul,
      inv_mul_cancel₀ hκ, one_smul]
  have h0θ : θ ⟨x, 0⟩ = 0 := by
    have := hθ.1.2 x 1 0 0
    simp only [one_smul, add_zero, one_mul] at this
    linear_combination -this
  have hgenY : ∀ (y : Y) (_ : y = f x), b4cov_descend0 f θ ⟨y, b4cov_vec y₀ y (L' 1)⟩ =
      b4cov_descend0 f θ ⟨f x, b4cov_vec y₀ (f x) (L' 1)⟩ := by rintro _ rfl; rfl
  have hgenC : ∀ (z : C) (_ : z = x), θ ⟨z, b4cov_vec x₁ z (L 1)⟩ =
      θ ⟨x, b4cov_vec x₁ x (L 1)⟩ := by rintro _ rfl; rfl
  change b4cov_descend0 f θ ⟨ψ.symm (ψ (f x)), b4cov_vec y₀ (ψ.symm (ψ (f x))) (L' 1)⟩ =
    κ⁻¹ * θ ⟨φ.symm (φ x), b4cov_vec x₁ (φ.symm (φ x)) (L 1)⟩
  rw [hgenY _ (ψ.left_inv hfx), hgenC _ (φ.left_inv hxs)]
  erw [b4cov_descend0_apply hE hE' hG f hf hgal θ hθ x hdx]
  rw [hdinv]
  have := hθ.1.2 x κ⁻¹ (b4cov_vec x₁ x (L 1)) 0
  rw [add_zero, h0θ, add_zero] at this
  exact this

/-- **The descended coefficient is bounded near every value.** -/
theorem b4cov_descend0_coef_bdd [Finite G] [Nonempty C] [T2Space C] [CompactSpace C]
    [ConnectedSpace C] [FaithfulSMul G C] [T2Space Y] (hE : Module.finrank ℂ E = 1)
    (hE' : Module.finrank ℂ E' = 1)
    (hG : ∀ g : G, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x : C ↦ g • x))
    (f : C → Y) (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω f) (hgal : b4_IsGaloisCover G f)
    (θ : TangentBundle 𝓘(ℂ, E) C → ℂ) (hθ : θ ∈ b4_invariantForms E C G) (x₀ : C) :
    ∃ M : ℝ, ∀ᶠ w in 𝓝[≠] (extChartAt 𝓘(ℂ, E') (f x₀) (f x₀)),
      ‖b4cov_coef (b4cov_descend0 f θ) (f x₀) (b4cov_lineEquiv hE' 1) w‖ ≤ M := by
  have : FiniteDimensional ℂ E := Module.finite_of_finrank_eq_succ hE
  have : FiniteDimensional ℂ E' := Module.finite_of_finrank_eq_succ hE'
  have := FiniteDimensional.complete ℂ E
  have := FiniteDimensional.complete ℂ E'
  have hnc := b4cov_nonconst_of_galois hE f hgal x₀
  set L := b4cov_lineEquiv hE
  set L' := b4cov_lineEquiv hE'
  set φ := extChartAt 𝓘(ℂ, E) x₀
  set ψ := extChartAt 𝓘(ℂ, E') (f x₀)
  set z₀ := φ x₀
  set Gx := b4cov_expr E E' f x₀ (f x₀)
  set e := b4_ramIndex E E' f x₀
  have hx₀ : x₀ ∈ φ.source := mem_extChartAt_source x₀
  -- the numerator vanishes to order `e - 1`
  obtain ⟨h, hh⟩ := b4cov_exists_rotGen hE hG x₀
  have hord_h : orderOf h = e := by
    rw [hh.2.1]; exact (b4cov_ramIndex_galois hE hE' hG f hf hgal x₀).symm
  have hnum := b4cov_coef_order_ge hE hG θ hθ x₀ h hh
  rw [hord_h] at hnum
  have hαan : AnalyticAt ℂ (fun τ : ℂ ↦ b4cov_coef θ x₀ (L 1) (z₀ + L τ)) 0 :=
    AnalyticAt.comp (g := b4cov_coef θ x₀ (L 1)) (f := fun τ : ℂ ↦ z₀ + L τ)
      (by simp only [map_zero, add_zero]
          exact b4cov_coef_analyticAt θ hθ.1.1 x₀ (L 1) z₀ (φ.map_source hx₀))
      (analyticAt_const.add (L.toContinuousLinearMap.analyticAt 0))
  obtain ⟨β, hβ, hαβ⟩ := (natCast_le_analyticOrderAt hαan).1 hnum
  -- the denominator vanishes to order exactly `e - 1`
  obtain ⟨he1, hne, hlow⟩ := b4cov_ramIndex_spec f hf hnc x₀
  have hGan : AnalyticAt ℂ Gx z₀ := b4cov_analyticOnNhd f hf x₀ _ (b4cov_mem_good (E' := E') f x₀)
  set hT := b4cov_transport hE hE' Gx z₀
  have hTan : AnalyticAt ℂ hT 0 := b4cov_transport_analyticAt hE hE' hGan
  have hTord : analyticOrderAt hT 0 = e := b4cov_analyticOrderAt_transport hE hE' hGan he1 hlow hne
  have hDord : analyticOrderAt (deriv hT) 0 = ((e - 1 : ℕ) : ℕ∞) := by
    have h1 := hTan.analyticOrderAt_deriv_add_one
    have h2 : (fun τ ↦ hT τ - hT 0) = hT := by
      funext τ; rw [show hT 0 = 0 from b4cov_transport_zero hE hE' Gx z₀, sub_zero]
    rw [h2, hTord] at h1
    have h3 : ((e - 1 : ℕ) : ℕ∞) + 1 = (e : ℕ∞) := by
      have : (e - 1) + 1 = e := Nat.sub_add_cancel he1
      exact_mod_cast this
    rw [← h3] at h1
    exact WithTop.add_right_cancel ENat.one_ne_top h1
  obtain ⟨v, hv, hv0, hDv⟩ := hTan.deriv.analyticOrderAt_eq_natCast.1 hDord
  -- the ratio is bounded near `0`
  have hratio : ContinuousAt (fun τ ↦ β τ / v τ) 0 := hβ.continuousAt.div hv.continuousAt hv0
  obtain ⟨δ₀, hδ₀, hball⟩ := Metric.continuousAt_iff.1 hratio 1 one_pos
  set M := ‖β 0 / v 0‖ + 1
  have hevτ : ∀ᶠ τ in 𝓝 (0 : ℂ), b4cov_coef θ x₀ (L 1) (z₀ + L τ) = (τ - 0) ^ (e - 1) • β τ ∧
      deriv hT τ = (τ - 0) ^ (e - 1) • v τ ∧ ‖β τ / v τ‖ ≤ M ∧ v τ ≠ 0 ∧
      AnalyticAt ℂ Gx (z₀ + L τ) := by
    have hb : ∀ᶠ τ in 𝓝 (0 : ℂ), ‖β τ / v τ‖ ≤ M := by
      filter_upwards [Metric.ball_mem_nhds 0 hδ₀] with τ hτ
      have := hball hτ
      rw [dist_eq_norm] at this
      have h2 := norm_le_insert' (β τ / v τ) (β 0 / v 0)
      linarith
    have hGev : ∀ᶠ τ in 𝓝 (0 : ℂ), AnalyticAt ℂ Gx (z₀ + L τ) :=
      (analyticAt_const.add (L.toContinuousLinearMap.analyticAt 0)).continuousAt.tendsto.eventually
        (p := fun t ↦ AnalyticAt ℂ Gx t) (by simpa using hGan.eventually_analyticAt)
    exact hαβ.and (hDv.and (hb.and ((hv.continuousAt.eventually_ne hv0).and hGev)))
  obtain ⟨δ, hδ, hδball⟩ := Metric.eventually_nhds_iff_ball.1 hevτ
  -- a small neighborhood of `x₀`
  let τf : C → ℂ := fun x ↦ L.symm (φ x - z₀)
  have hτc : ContinuousAt τf x₀ :=
    L.symm.continuous.continuousAt.comp ((continuousAt_extChartAt x₀).sub continuousAt_const)
  have hτ0 : τf x₀ = 0 := by simp [τf, z₀]
  have hN : φ.source ∩ f ⁻¹' ψ.source ∩ τf ⁻¹' Metric.ball 0 δ ∈ 𝓝 x₀ :=
    inter_mem (b4cov_source_nhds (E := E) (E' := E') f hf.continuous x₀)
      (hτc.preimage_mem_nhds (by rw [hτ0]; exact Metric.ball_mem_nhds 0 hδ))
  obtain ⟨U, hUN, -, -, V, hV, -, hcount⟩ := b4cov_local_degree hE hE' f hf hnc x₀ _ hN
  refine ⟨M, ?_⟩
  have hVw : ∀ᶠ w in 𝓝 (ψ (f x₀)), w ∈ ψ.target ∧ ψ.symm w ∈ V :=
    Filter.Eventually.and ((isOpen_extChartAt_target (f x₀)).mem_nhds
        (mem_extChartAt_target (f x₀)) : ∀ᶠ w in 𝓝 (ψ (f x₀)), w ∈ ψ.target)
      ((continuousAt_extChartAt_symm (f x₀)).tendsto.eventually (p := fun y ↦ y ∈ V)
        (by rw [extChartAt_to_inv]; exact hV))
  filter_upwards [nhdsWithin_le_nhds hVw, self_mem_nhdsWithin] with w ⟨hwt, hwV⟩ hw0
  set y := ψ.symm w
  have hy : y ≠ f x₀ := by
    intro hyx
    apply hw0
    rw [← ψ.right_inv hwt]
    change ψ y = ψ (f x₀)
    rw [hyx]
  obtain ⟨hcard, hram⟩ := hcount y hwV hy
  have hne' : (f ⁻¹' {y} ∩ U).Nonempty := by
    apply Set.nonempty_of_ncard_ne_zero
    rw [hcard]; omega
  obtain ⟨x, hxy, hxU⟩ := hne'
  have hfx : f x = y := hxy
  have hxN := hUN hxU
  have hdx : mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E') f x ≠ 0 :=
    (b4cov_ramIndex_eq_one_iff f hf x).1 (hram x hxU hfx)
  have hw : w = ψ (f x) := by rw [hfx]; exact (ψ.right_inv hwt).symm
  rw [hw, b4cov_descend0_coef_eq hE hE' hG f hf hgal θ hθ x₀ (f x₀) x hxN.1.1 hxN.1.2 hdx]
  set τ := τf x
  have hφx : φ x = z₀ + L τ := by simp [τ, τf]
  have hτδ : τ ∈ Metric.ball (0 : ℂ) δ := hxN.2
  obtain ⟨h1, h2, h3, h4, h5⟩ := hδball τ hτδ
  have hτne : τ ≠ 0 := by
    intro h0
    apply hy
    rw [← hfx]
    congr 1
    apply φ.injOn hxN.1.1 hx₀
    rw [hφx, h0, map_zero, add_zero]
  have hderiv : (L'.symm (fderiv ℂ Gx (φ x) (L 1))) = deriv hT τ := by
    rw [b4cov_transport_deriv hE hE' τ h5.differentiableAt, hφx]
  rw [hderiv, h2, hφx, h1, sub_zero, smul_eq_mul, smul_eq_mul]
  have hτk : τ ^ (e - 1) ≠ 0 := pow_ne_zero _ hτne
  have key : (τ ^ (e - 1) * v τ)⁻¹ * (τ ^ (e - 1) * β τ) = β τ / v τ := by
    field_simp
  rw [key]
  exact h3

/-- The branch values: every preimage is critical. -/
def b4cov_branch (E E' : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [ChartedSpace E C]
    [NormedAddCommGroup E'] [NormedSpace ℂ E'] [ChartedSpace E' Y] (f : C → Y) : Set Y :=
  {y | ∀ x, f x = y → mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E') f x = 0}

/-- The value at a branch point: the limit of the descended coefficient. -/
def b4cov_ell [Nonempty C] (hE' : Module.finrank ℂ E' = 1) (f : C → Y)
    (θ : TangentBundle 𝓘(ℂ, E) C → ℂ) (y : Y) : ℂ :=
  limUnder (𝓝[≠] (0 : ℂ)) fun τ ↦ b4cov_coef (b4cov_descend0 f θ) y (b4cov_lineEquiv hE' 1)
    (extChartAt 𝓘(ℂ, E') y y + b4cov_lineEquiv hE' τ)

open Classical in
/-- **The descended form** on `Y`. -/
def b4cov_descend [Nonempty C] (hE' : Module.finrank ℂ E' = 1) (f : C → Y)
    (θ : TangentBundle 𝓘(ℂ, E) C → ℂ) : TangentBundle 𝓘(ℂ, E') Y → ℂ :=
  fun p ↦ if p.proj ∈ b4cov_branch E E' f then
    (b4cov_lineEquiv hE').symm p.2 * b4cov_ell (E := E) hE' f θ p.proj
  else b4cov_descend0 f θ p

theorem b4cov_branch_finite [CompactSpace C] [ConnectedSpace C] (hE : Module.finrank ℂ E = 1)
    (hE' : Module.finrank ℂ E' = 1) (f : C → Y) (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω f)
    (hnc : ∃ x x', f x ≠ f x') (hsurj : Function.Surjective f) :
    (b4cov_branch E E' f).Finite := by
  have : FiniteDimensional ℂ E' := Module.finite_of_finrank_eq_succ hE'
  have := FiniteDimensional.complete ℂ E'
  refine ((b4cov_critical_finite hE f hf hnc).image f).subset fun y hy ↦ ?_
  obtain ⟨x, rfl⟩ := hsurj y
  exact ⟨x, hy x rfl, rfl⟩

theorem b4cov_not_branch {f : C → Y} {y : Y} (hy : y ∉ b4cov_branch E E' f) :
    ∃ x, f x = y ∧ mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E') f x ≠ 0 := by
  by_contra h
  push Not at h
  exact hy h

section Assemble

variable [Finite G] [Nonempty C] [T2Space C] [CompactSpace C] [ConnectedSpace C]
  [FaithfulSMul G C] [T2Space Y] [ConnectedSpace Y]

theorem b4cov_descend_apply_of_not_branch (hE' : Module.finrank ℂ E' = 1) (f : C → Y)
    (θ : TangentBundle 𝓘(ℂ, E) C → ℂ) (p : TangentBundle 𝓘(ℂ, E') Y)
    (hp : p.proj ∉ b4cov_branch E E' f) :
    b4cov_descend hE' f θ p = b4cov_descend0 f θ p := by
  simp only [b4cov_descend, hp, if_false]

theorem b4cov_descend_linear (hE : Module.finrank ℂ E = 1) (hE' : Module.finrank ℂ E' = 1)
    (hG : ∀ g : G, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x : C ↦ g • x))
    (f : C → Y) (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω f) (hgal : b4_IsGaloisCover G f)
    (θ : TangentBundle 𝓘(ℂ, E) C → ℂ) (hθ : θ ∈ b4_invariantForms E C G) (y : Y) (a : ℂ)
    (v w : TangentSpace 𝓘(ℂ, E') y) :
    b4cov_descend hE' f θ ⟨y, a • v + w⟩ =
      a * b4cov_descend hE' f θ ⟨y, v⟩ + b4cov_descend hE' f θ ⟨y, w⟩ := by
  by_cases hy : y ∈ b4cov_branch E E' f
  · simp only [b4cov_descend, hy, if_true]
    erw [map_add, map_smul]
    rw [smul_eq_mul]
    ring
  · rw [b4cov_descend_apply_of_not_branch hE' f θ _ hy, b4cov_descend_apply_of_not_branch hE' f θ _ hy,
      b4cov_descend_apply_of_not_branch hE' f θ _ hy]
    obtain ⟨x, rfl, hx⟩ := b4cov_not_branch hy
    have hbij := b4cov_bijective_of_ne_zero hE hE' _ hx
    erw [b4cov_descend0_apply hE hE' hG f hf hgal θ hθ x hx,
      b4cov_descend0_apply hE hE' hG f hf hgal θ hθ x hx,
      b4cov_descend0_apply hE hE' hG f hf hgal θ hθ x hx, b4cov_dinv_linear f x hbij]
    exact hθ.1.2 x a _ _

/-- **The coefficients of the descended form are analytic.** -/
theorem b4cov_descend_coef_analyticAt (hE : Module.finrank ℂ E = 1)
    (hE' : Module.finrank ℂ E' = 1)
    (hG : ∀ g : G, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x : C ↦ g • x))
    (f : C → Y) (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω f) (hgal : b4_IsGaloisCover G f)
    (θ : TangentBundle 𝓘(ℂ, E) C → ℂ) (hθ : θ ∈ b4_invariantForms E C G) (y₀ : Y) :
    AnalyticAt ℂ (b4cov_coef (b4cov_descend hE' f θ) y₀ (b4cov_lineEquiv hE' 1))
      (extChartAt 𝓘(ℂ, E') y₀ y₀) := by
  obtain ⟨x₀⟩ := ‹Nonempty C›
  have hnc := b4cov_nonconst_of_galois hE f hgal x₀
  have hsurj := b4cov_surjective hE' f hf hnc
  have hBfin := b4cov_branch_finite hE hE' f hf hnc hsurj
  set ψ := extChartAt 𝓘(ℂ, E') y₀
  set L' := b4cov_lineEquiv hE'
  -- off the branch values the two coefficients agree on an open set
  have hagree : ∀ w ∈ ψ.target, ψ.symm w ∉ b4cov_branch E E' f →
      b4cov_coef (b4cov_descend hE' f θ) y₀ (L' 1) w =
        b4cov_coef (b4cov_descend0 f θ) y₀ (L' 1) w := fun w _ hw ↦
    b4cov_descend_apply_of_not_branch hE' f θ _ hw
  -- analyticity of the descended coefficient at values off the branch set
  have hreg : ∀ w ∈ ψ.target, ψ.symm w ∉ b4cov_branch E E' f →
      AnalyticAt ℂ (b4cov_coef (b4cov_descend0 f θ) y₀ (L' 1)) w := by
    intro w hw hwB
    obtain ⟨x₁, hx₁, hd₁⟩ := b4cov_not_branch hwB
    have hfx₁ : f x₁ ∈ ψ.source := by rw [hx₁]; exact ψ.map_target hw
    have := b4cov_descend0_coef_analyticAt hE hE' hG f hf hgal θ hθ y₀ x₁ hfx₁ hd₁
    rwa [hx₁, ψ.right_inv hw] at this
  -- the open set where `ψ.symm w` avoids the branch values other than `y₀`
  let O : Set E' := ψ.target ∩ ψ.symm ⁻¹' (b4cov_branch E E' f \ {y₀})ᶜ
  have hOo : IsOpen O := (continuousOn_extChartAt_symm y₀).isOpen_inter_preimage
    (isOpen_extChartAt_target y₀) (hBfin.diff).isClosed.isOpen_compl
  have hw₀O : ψ y₀ ∈ O := ⟨mem_extChartAt_target y₀, by
    simp only [mem_preimage, ψ, extChartAt_to_inv]; exact fun h ↦ h.2 rfl⟩
  have hOreg : ∀ w ∈ O, w ≠ ψ y₀ → ψ.symm w ∉ b4cov_branch E E' f := by
    intro w hw hw0 hB
    refine hw.2 ⟨hB, fun h ↦ hw0 ?_⟩
    rw [← ψ.right_inv hw.1, show ψ.symm w = y₀ from h]
  by_cases hy₀ : y₀ ∈ b4cov_branch E E' f
  · -- removable singularity at a branch value
    obtain ⟨x₀, rfl⟩ := hsurj y₀
    obtain ⟨M, hM⟩ := b4cov_descend0_coef_bdd hE hE' hG f hf hgal θ hθ x₀
    have hpunct : O \ {ψ (f x₀)} ∈ 𝓝[≠] (ψ (f x₀)) :=
      diff_mem_nhdsWithin_compl (hOo.mem_nhds hw₀O) _
    have hagree' : ∀ w ∈ O \ {ψ (f x₀)},
        b4cov_coef (b4cov_descend hE' f θ) (f x₀) (L' 1) w =
          b4cov_coef (b4cov_descend0 f θ) (f x₀) (L' 1) w := fun w hw ↦
      hagree w hw.1.1 (hOreg w hw.1 hw.2)
    refine b4cov_analyticAt_of_punctured hE' (M := M) ?_ ?_ ?_
    · filter_upwards [hpunct] with w hw
      have hO' : O \ {ψ (f x₀)} ∈ 𝓝 w := (hOo.sdiff isClosed_singleton).mem_nhds hw
      refine (hreg w hw.1.1 (hOreg w hw.1 hw.2)).congr ?_
      filter_upwards [hO'] with w' hw'
      exact (hagree' w' hw').symm
    · filter_upwards [hpunct, hM] with w hw hwM
      rw [hagree' w hw]; exact hwM
    · -- the value at the centre is the limit
      have hcentre : b4cov_coef (b4cov_descend hE' f θ) (f x₀) (L' 1) (ψ (f x₀)) =
          b4cov_ell (E := E) hE' f θ (f x₀) := by
        have hgen : ∀ (y : Y) (_ : y = f x₀), b4cov_descend hE' f θ ⟨y, b4cov_vec (f x₀) y (L' 1)⟩ =
            b4cov_descend hE' f θ ⟨f x₀, b4cov_vec (f x₀) (f x₀) (L' 1)⟩ := by rintro _ rfl; rfl
        change b4cov_descend hE' f θ ⟨ψ.symm (ψ (f x₀)), b4cov_vec (f x₀) (ψ.symm (ψ (f x₀))) (L' 1)⟩ = _
        rw [hgen _ (ψ.left_inv (mem_extChartAt_source (f x₀))), b4cov_vec_self]
        simp only [b4cov_descend, hy₀, if_true]
        erw [ContinuousLinearEquiv.symm_apply_apply, one_mul]
      rw [hcentre, b4cov_ell]
      unfold limUnder
      congr 1
      refine Filter.map_congr ?_
      let Φ : ℂ ≃ₜ E' := L'.toHomeomorph.trans (Homeomorph.addLeft (ψ (f x₀)))
      have hΦ0 : Φ 0 = ψ (f x₀) := by simp [Φ]
      have := (show ∀ᶠ w in 𝓝[≠] (ψ (f x₀)), w ∈ O \ {ψ (f x₀)} from hpunct)
      rw [← hΦ0, ← Φ.map_punctured_nhds_eq] at this
      filter_upwards [Filter.eventually_map.1 this] with τ hτ
      have hτ' : Φ τ ∈ O \ {ψ (f x₀)} := by rwa [hΦ0] at hτ
      exact (hagree' (Φ τ) hτ').symm
  · -- off the branch values
    refine (hreg _ (mem_extChartAt_target y₀) (by rwa [extChartAt_to_inv])).congr ?_
    have hOy : ∀ᶠ w in 𝓝 (ψ y₀), w ∈ O ∧ ψ.symm w ∉ b4cov_branch E E' f := by
      have hc : ∀ᶠ w in 𝓝 (ψ y₀), ψ.symm w ∈ (b4cov_branch E E' f)ᶜ :=
        (continuousAt_extChartAt_symm y₀).tendsto.eventually (p := fun y ↦ y ∈ (b4cov_branch E E' f)ᶜ)
          (by rw [extChartAt_to_inv]; exact hBfin.isClosed.isOpen_compl.mem_nhds hy₀)
      exact Filter.Eventually.and (hOo.mem_nhds hw₀O : ∀ᶠ w in 𝓝 (ψ y₀), w ∈ O) hc
    filter_upwards [hOy] with w ⟨hwO, hwB⟩
    exact (hagree w hwO.1 hwB).symm

/-- **The descended form is a holomorphic form on `Y`.** -/
theorem b4cov_descend_mem_holForm (hE : Module.finrank ℂ E = 1)
    (hE' : Module.finrank ℂ E' = 1)
    (hG : ∀ g : G, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x : C ↦ g • x))
    (f : C → Y) (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω f) (hgal : b4_IsGaloisCover G f)
    (θ : TangentBundle 𝓘(ℂ, E) C → ℂ) (hθ : θ ∈ b4_invariantForms E C G) :
    b4cov_descend hE' f θ ∈ b3_HolForm E' Y :=
  b4cov_mem_holForm_of_coef hE' _ (fun y a v w ↦ b4cov_descend_linear hE hE' hG f hf hgal θ hθ y a v w)
    (fun y₀ ↦ b4cov_descend_coef_analyticAt hE hE' hG f hf hgal θ hθ y₀)

/-- **The descended form pulls back to `θ`.** -/
theorem b4cov_pullback_descend (hE : Module.finrank ℂ E = 1)
    (hE' : Module.finrank ℂ E' = 1)
    (hG : ∀ g : G, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x : C ↦ g • x))
    (f : C → Y) (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω f) (hgal : b4_IsGaloisCover G f)
    (θ : TangentBundle 𝓘(ℂ, E) C → ℂ) (hθ : θ ∈ b4_invariantForms E C G) :
    b3_pullback E E' f (b4cov_descend hE' f θ) = θ := by
  obtain ⟨x₀⟩ := ‹Nonempty C›
  have hnc := b4cov_nonconst_of_galois hE f hgal x₀
  have hsurj := b4cov_surjective hE' f hf hnc
  have : FiniteDimensional ℂ E' := Module.finite_of_finrank_eq_succ hE'
  have := FiniteDimensional.complete ℂ E'
  have hBfin := b4cov_branch_finite hE hE' f hf hnc hsurj
  have hSfin : (f ⁻¹' b4cov_branch E E' f).Finite :=
    hBfin.preimage' fun y _ ↦ b4cov_fiber_finite hE f hf hnc y
  have hη := b4cov_descend_mem_holForm hE hE' hG f hf hgal θ hθ
  -- agreement off the finite set `f⁻¹ B`
  have hoff : ∀ x, x ∉ f ⁻¹' b4cov_branch E E' f → ∀ v : E,
      (b3_pullback E E' f (b4cov_descend hE' f θ) - θ) ⟨x, v⟩ = 0 := by
    intro x hx v
    obtain ⟨x', hx', hd'⟩ := b4cov_not_branch hx
    have hdx := b4cov_unram_of_fiber hG f hf hgal x' x hx' hd'
    have hbij := b4cov_bijective_of_ne_zero hE hE' _ hdx
    change b4cov_descend hE' f θ ⟨f x, mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E') f x v⟩ - θ ⟨x, v⟩ = 0
    rw [b4cov_descend_apply_of_not_branch hE' f θ ⟨f x, _⟩ hx]
    erw [b4cov_descend0_apply hE hE' hG f hf hgal θ hθ x hdx, b4cov_dinv_mfderiv f x hbij]
    exact sub_self _
  have hD : b3_pullback E E' f (b4cov_descend hE' f θ) - θ ∈ b3_HolForm E C :=
    Submodule.sub_mem _ (b3_pullback_mem_holForm f hf _ hη) hθ.1
  have hzero : b3_pullback E E' f (b4cov_descend hE' f θ) - θ = 0 := by
    funext p
    obtain ⟨x, v⟩ := p
    refine b4cov_form_eq_zero_of_eventually hE _ hD x ?_ v
    have hS' : ((f ⁻¹' b4cov_branch E E' f) \ {x})ᶜ ∈ 𝓝 x :=
      (hSfin.diff).isClosed.isOpen_compl.mem_nhds (fun h ↦ h.2 rfl)
    filter_upwards [mem_nhdsWithin_of_mem_nhds hS', self_mem_nhdsWithin] with x' hx' hx'x
    exact hoff x' fun hB ↦ hx' ⟨hB, hx'x⟩
  exact sub_eq_zero.1 hzero

/-- **`dim Ω¹(C)^G = dim Ω¹(Y)`** for a Galois cover. -/
theorem b4cov_invariantForms_galois [CompactSpace Y] (hE : Module.finrank ℂ E = 1)
    (hE' : Module.finrank ℂ E' = 1)
    (hG : ∀ g : G, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x : C ↦ g • x))
    (f : C → Y) (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω f) (hgal : b4_IsGaloisCover G f) :
    Module.finrank ℂ (b4_invariantForms E C G) = Module.finrank ℂ (b3_HolForm E' Y) := by
  refine le_antisymm ?_ (b4cov_finrank_holForm_le_invariant hE hE' hG f hf hgal)
  have := b3_holForm_finiteDimensional (C := Y) hE'
  let P : b3_HolForm E' Y →ₗ[ℂ] b4_invariantForms E C G :=
    ((b3_pullback E E' f).domRestrict (b3_HolForm E' Y)).codRestrict _ fun η ↦
      b4cov_pullback_mem_invariantForms hG f hf hgal η η.2
  have hsurj : Function.Surjective P := by
    intro θ
    refine ⟨⟨b4cov_descend hE' f (θ : TangentBundle 𝓘(ℂ, E) C → ℂ),
      b4cov_descend_mem_holForm hE hE' hG f hf hgal θ θ.2⟩, ?_⟩
    apply Subtype.ext
    change b3_pullback E E' f (b4cov_descend hE' f (θ : TangentBundle 𝓘(ℂ, E) C → ℂ)) =
      (θ : TangentBundle 𝓘(ℂ, E) C → ℂ)
    exact b4cov_pullback_descend hE hE' hG f hf hgal θ θ.2
  have h1 := LinearMap.finrank_range_le P
  have h2 : LinearMap.range P = ⊤ := LinearMap.range_eq_top.2 hsurj
  rw [h2, finrank_top] at h1
  exact h1

end Assemble

end Descent

end HodgeLean.Foundations.Program
