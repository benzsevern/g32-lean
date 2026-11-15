import HodgeLean.Foundations.AnalyticDivisorAlgebraic2

/-! # Proof obligations for the analytic divisor spec, third stage

One obligation per statement of `HodgeLean.Foundations.AnalyticDivisorAlgebraic3`. All sixteen are proved, by three parallel provers.
-/

noncomputable section

open Set Filter Topology

open scoped Manifold ContDiff

namespace HodgeLean.Foundations.AnalyticDivisorAlgebraic3

open AppellHumbert

section Regular

theorem spec_exists_analytic_implicit_aux {E₁ : Type*} [NormedAddCommGroup E₁]
    [NormedSpace ℂ E₁] [CompleteSpace E₁] {f : E₁ × ℂ → ℂ} {u : E₁ × ℂ}
    (hf : AnalyticAt ℂ f u) (hfu : f u = 0) (hreg : fderiv ℂ f u (0, 1) ≠ 0) :
    ∃ ψ : E₁ → ℂ, AnalyticAt ℂ ψ u.1 ∧ ψ u.1 = u.2 ∧
      ∀ᶠ p in 𝓝 u, (f p = 0 ↔ ψ p.1 = p.2) := by
  have cdf : ContDiffAt ℂ ω f u := hf.contDiffAt
  have pn : (ω : WithTop ℕ∞) ≠ 0 := by simp
  have if₂ : (fderiv ℂ f u ∘L .inr ℂ E₁ ℂ).IsInvertible := by
    refine ⟨ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 _ hreg), ?_⟩
    ext
    simp
  refine ⟨cdf.implicitFunction pn if₂, (cdf.contDiffAt_implicitFunction pn if₂).analyticAt,
    cdf.implicitFunction_apply_self pn if₂, ?_⟩
  simpa only [hfu] using cdf.eventually_apply_eq_iff_implicitFunction pn if₂

theorem spec_not_exists_implicit_sq_sub_aux :
    ¬ ∃ ψ : ℂ → ℂ, ∀ᶠ p in 𝓝 ((0 : ℂ), (0 : ℂ)), (p.2 ^ 2 - p.1 = 0 ↔ ψ p.1 = p.2) := by
  rintro ⟨ψ, h⟩
  have t1 : Tendsto (fun ε : ℂ => (ε ^ 2, ε)) (𝓝[≠] 0) (𝓝 ((0 : ℂ), (0 : ℂ))) :=
    (((continuous_pow 2).prodMk continuous_id).tendsto' 0 _ (by simp)).mono_left
      nhdsWithin_le_nhds
  have t2 : Tendsto (fun ε : ℂ => (ε ^ 2, -ε)) (𝓝[≠] 0) (𝓝 ((0 : ℂ), (0 : ℂ))) :=
    (((continuous_pow 2).prodMk continuous_neg).tendsto' 0 _ (by simp)).mono_left
      nhdsWithin_le_nhds
  obtain ⟨ε, h1, h2, hε⟩ :=
    ((t1.eventually h).and ((t2.eventually h).and self_mem_nhdsWithin)).exists
  have e1 : ψ (ε ^ 2) = ε := (h1).1 (by ring)
  have e2 : ψ (ε ^ 2) = -ε := (h2).1 (by ring)
  have : ε = 0 := by linear_combination (e2 - e1) / 2
  exact hε this

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

theorem spec_exists_prodKerEquiv_aux (φ : V →L[ℂ] ℂ) {v : V} (hv : φ v ≠ 0) :
    ∃ e : (LinearMap.ker (φ : V →ₗ[ℂ] ℂ) × ℂ) ≃L[ℂ] V, ∀ p, e p = (p.1 : V) + p.2 • v := by
  let L : (LinearMap.ker (φ : V →ₗ[ℂ] ℂ) × ℂ) →ₗ[ℂ] V :=
    (LinearMap.ker (φ : V →ₗ[ℂ] ℂ)).subtype.coprod (LinearMap.toSpanSingleton ℂ V v)
  have hL : ∀ p, L p = (p.1 : V) + p.2 • v := fun p => rfl
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨⟨k, hk⟩, s⟩ h
    rw [hL] at h
    have hk' : φ k = 0 := hk
    have hs : s = 0 := by
      have := congrArg φ h
      simp only [map_add, map_smul, hk', smul_eq_mul, zero_add, map_zero] at this
      exact (mul_eq_zero.1 this).resolve_right hv
    subst hs
    simp only [zero_smul, add_zero] at h
    ext <;> simp [h]
  have hsurj : Function.Surjective L := by
    intro w
    refine ⟨(⟨w - (φ w / φ v) • v, ?_⟩, φ w / φ v), ?_⟩
    · show φ (w - (φ w / φ v) • v) = 0
      simp only [map_sub, map_smul, smul_eq_mul]
      field_simp
      ring
    · rw [hL]; simp
  exact ⟨(LinearEquiv.ofBijective L ⟨hinj, hsurj⟩).toContinuousLinearEquiv, fun p => rfl⟩

theorem spec_exists_analytic_graph_aux {f : V → ℂ} {x v : V} (hf : AnalyticAt ℂ f x)
    (hfx : f x = 0) (hv : fderiv ℂ f x v ≠ 0) :
    ∃ ψ : LinearMap.ker (fderiv ℂ f x : V →ₗ[ℂ] ℂ) → ℂ, AnalyticAt ℂ ψ 0 ∧ ψ 0 = 0 ∧
      ∀ᶠ p in 𝓝 (0 : LinearMap.ker (fderiv ℂ f x : V →ₗ[ℂ] ℂ) × ℂ),
        (f (x + (p.1 : V) + p.2 • v) = 0 ↔ ψ p.1 = p.2) := by
  set K := LinearMap.ker (fderiv ℂ f x : V →ₗ[ℂ] ℂ)
  have : CompleteSpace K := FiniteDimensional.complete ℂ K
  let A : (K × ℂ) →L[ℂ] V := K.subtypeL.coprod (ContinuousLinearMap.toSpanSingleton ℂ v)
  have hA : ∀ p : K × ℂ, A p = (p.1 : V) + p.2 • v := fun p => rfl
  set g : K × ℂ → ℂ := fun p => f (x + (p.1 : V) + p.2 • v) with hg
  have hgA : g = fun p => f (x + A p) := by
    funext p; simp only [hg, hA, add_assoc]
  have h0 : x + A 0 = x := by simp
  have hfx' : AnalyticAt ℂ f (x + A 0) := by rwa [h0]
  have hga : AnalyticAt ℂ g 0 := by
    rw [hgA]
    exact AnalyticAt.comp (g := f) (f := fun p => x + A p) hfx'
      (analyticAt_const.add (A.analyticAt 0))
  have hgd : HasFDerivAt g ((fderiv ℂ f x).comp A) 0 := by
    rw [hgA]
    have hd : HasFDerivAt f (fderiv ℂ f x) (x + A 0) := by
      rw [h0]; exact hf.differentiableAt.hasFDerivAt
    exact hd.comp (0 : K × ℂ) (A.hasFDerivAt.const_add x)
  have hreg : fderiv ℂ g ((0 : K), (0 : ℂ)) (0, 1) ≠ 0 := by
    rw [Prod.mk_zero_zero, hgd.fderiv]; simpa [hA] using hv
  obtain ⟨ψ, hψa, hψ0, hψ⟩ := spec_exists_analytic_implicit_aux (u := ((0 : K), (0 : ℂ)))
    (by rw [Prod.mk_zero_zero]; exact hga) (by simp [hg, hfx]) hreg
  rw [Prod.mk_zero_zero] at hψ
  exact ⟨ψ, hψa, hψ0, hψ⟩

theorem spec_isClosedAnalytic_singularLocus_aux {f : V → ℂ} (hf : Differentiable ℂ f) :
    IsClosedAnalytic V {x | f x = 0 ∧ fderiv ℂ f x = 0} := by
  have hfa : AnalyticOnNhd ℂ f univ :=
    AnalyticDivisorAlgebraic2.spec_analyticOnNhd_of_differentiableOn isOpen_univ
      hf.differentiableOn
  have hda : AnalyticOnNhd ℂ (fderiv ℂ f) univ := hfa.fderiv
  have hdc : Continuous (fderiv ℂ f) :=
    continuous_iff_continuousAt.2 fun x => (hda x (mem_univ x)).continuousAt
  let b := Module.finBasis ℂ V
  let F : Option (Fin (Module.finrank ℂ V)) → V → ℂ := fun i =>
    match i with
    | none => f
    | some j => fun z => fderiv ℂ f z (b j)
  rw [isClosedAnalytic_iff_finite]
  refine ⟨(isClosed_eq hf.continuous continuous_const).inter
    (isClosed_eq hdc continuous_const), fun x _ => ⟨univ, isOpen_univ, mem_univ _, by simp,
      Option (Fin (Module.finrank ℂ V)), inferInstance, F, ?_, fun z _ => ?_⟩⟩
  · rintro (_ | j) z -
    · exact hfa z (mem_univ z)
    · exact ((ContinuousLinearMap.apply ℂ ℂ (b j)).analyticAt _).comp (hda z (mem_univ z))
  · simp only [chartAt_self_eq, OpenPartialHomeomorph.refl_symm, OpenPartialHomeomorph.refl_apply,
      id_eq, mem_ofPred_eq, Option.forall, F]
    refine and_congr_right fun _ => ⟨fun h j => by simp [h], fun h => ?_⟩
    exact ContinuousLinearMap.coe_injective (b.ext fun j => by simpa using h j)

end Regular

section Order

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem analyticAt_line_comp {f : E → ℂ} {x : E} (hf : AnalyticAt ℂ f x) (v : E) :
    AnalyticAt ℂ (fun t : ℂ => f (x + t • v)) 0 := by
  have hl : AnalyticAt ℂ (fun t : ℂ => x + t • v) 0 :=
    analyticAt_const.add (analyticAt_id.smul analyticAt_const)
  exact hf.comp_of_eq hl (by simp)

theorem deriv_line_comp {f : E → ℂ} {x : E} (hf : DifferentiableAt ℂ f x) (v : E) :
    deriv (fun t : ℂ => f (x + t • v)) 0 = fderiv ℂ f x v := by
  have hl : HasDerivAt (fun t : ℂ => x + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add x
  have hf' : HasFDerivAt f (fderiv ℂ f x) (x + (0 : ℂ) • v) := by
    simpa using hf.hasFDerivAt
  exact (hf'.comp_hasDerivAt (0 : ℂ) hl).deriv

theorem spec_analyticOrderAt_line_eq_one_iff_aux {f : E → ℂ} {x : E} (hf : AnalyticAt ℂ f x)
    (hfx : f x = 0) (v : E) :
    analyticOrderAt (fun t : ℂ => f (x + t • v)) 0 = 1 ↔ fderiv ℂ f x v ≠ 0 := by
  have hg := analyticAt_line_comp hf v
  have hg0 : (fun t : ℂ => f (x + t • v)) 0 = 0 := by simpa using hfx
  rw [← deriv_line_comp hf.differentiableAt v]
  refine ⟨fun h hd => ?_, fun hd => hg.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hg0 hd⟩
  have hadd := hg.analyticOrderAt_deriv_add_one
  simp only [hg0, sub_zero] at hadd
  have hne : analyticOrderAt (deriv fun t : ℂ => f (x + t • v)) 0 ≠ 0 :=
    analyticOrderAt_ne_zero.2 ⟨hg.deriv, hd⟩
  rw [h] at hadd
  generalize analyticOrderAt (deriv fun t : ℂ => f (x + t • v)) 0 = r at hadd hne
  cases r with
  | top => simp at hadd
  | coe n =>
    have : n + 1 = 1 := by exact_mod_cast hadd
    exact hne (by simp [show n = 0 by omega])

theorem spec_two_le_analyticOrderAt_line_iff_aux {f : E → ℂ} {x : E} (hf : AnalyticAt ℂ f x)
    (hfx : f x = 0) :
    (∀ v : E, 2 ≤ analyticOrderAt (fun t : ℂ => f (x + t • v)) 0) ↔ fderiv ℂ f x = 0 := by
  constructor
  · intro h
    ext v
    by_contra hv
    have h1 := (spec_analyticOrderAt_line_eq_one_iff_aux hf hfx v).2 hv
    have h2 := h v
    rw [h1] at h2
    exact absurd h2 (by decide)
  · intro h v
    have h1 : analyticOrderAt (fun t : ℂ => f (x + t • v)) 0 ≠ 1 := fun h1 =>
      (spec_analyticOrderAt_line_eq_one_iff_aux hf hfx v).1 h1 (by simp [h])
    have h0 : analyticOrderAt (fun t : ℂ => f (x + t • v)) 0 ≠ 0 :=
      analyticOrderAt_ne_zero.2 ⟨analyticAt_line_comp hf v, by simpa using hfx⟩
    generalize analyticOrderAt (fun t : ℂ => f (x + t • v)) 0 = r at h0 h1
    cases r with
    | top => exact le_top
    | coe n =>
      have : n ≠ 0 := by exact_mod_cast h0
      have : n ≠ 1 := by exact_mod_cast h1
      exact_mod_cast (by omega : 2 ≤ n)

theorem spec_analyticOrderAt_line_mul_aux {f g : E → ℂ} {x : E} (hf : AnalyticAt ℂ f x)
    (hg : AnalyticAt ℂ g x) (hgx : g x ≠ 0) (v : E) :
    analyticOrderAt (fun t : ℂ => g (x + t • v) * f (x + t • v)) 0 =
      analyticOrderAt (fun t : ℂ => f (x + t • v)) 0 := by
  have h := analyticOrderAt_mul (analyticAt_line_comp hg v) (analyticAt_line_comp hf v)
  have h0 : analyticOrderAt (fun t : ℂ => g (x + t • v)) 0 = 0 :=
    analyticOrderAt_eq_zero.2 (Or.inr (by simpa using hgx))
  rw [h0, zero_add] at h
  exact h

theorem spec_analyticOrderAt_line_depends_on_direction_aux :
    analyticOrderAt (fun t : ℂ => (t • ((1 : ℂ), (0 : ℂ))).1 * (t • ((1 : ℂ), (0 : ℂ))).2) 0
        = ⊤ ∧
      analyticOrderAt (fun t : ℂ => (t • ((1 : ℂ), (1 : ℂ))).1 * (t • ((1 : ℂ), (1 : ℂ))).2) 0
        = 2 := by
  constructor
  · rw [analyticOrderAt_eq_top]
    exact Eventually.of_forall fun t => by simp
  · have : (fun t : ℂ => (t • ((1 : ℂ), (1 : ℂ))).1 * (t • ((1 : ℂ), (1 : ℂ))).2) =
        (· - (0 : ℂ)) ^ 2 := by
      funext t
      simp [sq]
    rw [this, analyticOrderAt_centeredMonomial]
    rfl

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

theorem holFactor_differentiable_line (D : Datum (V := V)) (l : D.lattice) :
    Differentiable ℂ (holFactor D l) := by
  let f : V →ₗ[ℂ] ℂ :=
    { toFun := D.hermitian.toFun l
      map_add' := D.hermitian.add_right l
      map_smul' := fun c x ↦ D.hermitian.smul_right c l x }
  have hf : Differentiable ℂ (fun v ↦ D.hermitian.toFun l v) :=
    (LinearMap.toContinuousLinearMap f).differentiable
  exact ((hf.const_mul _).add_const _).cexp.const_mul _

theorem spec_analyticOrderAt_theta_line_add_aux (D : Datum (V := V)) {θ : V → ℂ}
    (hθ : θ ∈ sections D) (l : D.lattice) (x w : V) :
    analyticOrderAt (fun t : ℂ => θ (x + l + t • w)) 0 =
      analyticOrderAt (fun t : ℂ => θ (x + t • w)) 0 := by
  have hl : Differentiable ℂ (fun t : ℂ => x + t • w) :=
    (differentiable_const _).add (differentiable_id.smul_const w)
  have he : (fun t : ℂ => θ (x + l + t • w)) =
      (fun t : ℂ => holFactor D l (x + t • w)) * (fun t : ℂ => θ (x + t • w)) := by
    funext t
    rw [Pi.mul_apply, ← hθ.2 l (x + t • w)]
    congr 1
    abel
  have ha : AnalyticAt ℂ (fun t : ℂ => holFactor D l (x + t • w)) 0 :=
    ((holFactor_differentiable_line D l).comp hl).analyticAt 0
  have hb : AnalyticAt ℂ (fun t : ℂ => θ (x + t • w)) 0 := (hθ.1.comp hl).analyticAt 0
  rw [he, analyticOrderAt_mul ha hb]
  rw [analyticOrderAt_eq_zero.2 (Or.inr (by simpa using holFactor_ne_zero D l x)), zero_add]

theorem spec_fderiv_theta_add_eq_zero_iff_aux (D : Datum (V := V)) {θ : V → ℂ}
    (hθ : θ ∈ sections D) (l : D.lattice) {v : V} (hv : θ v = 0) :
    fderiv ℂ θ (v + l) = 0 ↔ fderiv ℂ θ v = 0 := by
  have he : (fun w => θ (w + l)) = fun w => holFactor D l w * θ w :=
    funext fun w => hθ.2 l w
  have h1 : fderiv ℂ (fun w => θ (w + l)) v = fderiv ℂ θ (v + l) := fderiv_comp_add_right _
  have h2 : HasFDerivAt (fun w => holFactor D l w * θ w)
      (holFactor D l v • fderiv ℂ θ v + θ v • fderiv ℂ (holFactor D l) v) v :=
    ((holFactor_differentiable_line D l v).hasFDerivAt).mul ((hθ.1 v).hasFDerivAt)
  have h3 : HasFDerivAt (fun w => holFactor D l w * θ w) (holFactor D l v • fderiv ℂ θ v) v := by
    convert h2 using 1
    ext u
    simp [hv]
  rw [← h1, he, h3.fderiv]
  have ha := holFactor_ne_zero D l v
  constructor
  · intro h
    ext u
    have h' := congrArg (fun L : V →L[ℂ] ℂ => L u) h
    simpa [ha] using h'
  · intro h
    ext u
    simp [h]

end Order

section Charts

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E']
  {N : Type*} [TopologicalSpace N] [ChartedSpace E' N]

/-- A holomorphic map is analytic in any two charts of the maximal analytic atlases. -/
theorem analyticAt_chart_comp_of_contMDiffAt {φ : N → M} {e : OpenPartialHomeomorph N E'}
    {e' : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ, E') ω N)
    (he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℂ, E) ω M) {y : N} (hy : y ∈ e.source)
    (hφy : φ y ∈ e'.source) (hφ : ContMDiffAt 𝓘(ℂ, E') 𝓘(ℂ, E) ω φ y) :
    AnalyticAt ℂ (e' ∘ φ ∘ e.symm) (e y) := by
  rw [contMDiffAt_iff_of_mem_maximalAtlas he he' hy hφy] at hφ
  have h := hφ.2
  simp only [OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm,
    modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, range_id, Function.id_comp,
    Function.comp_id, contDiffWithinAt_univ] at h
  exact h.analyticAt

/-- Pulling a local description of a closed analytic set back along a map `g` from an open set
of a model space whose composite with the preferred chart is analytic. -/
theorem exists_local_description_comp {E'' : Type*} [NormedAddCommGroup E'']
    [NormedSpace ℂ E''] {Z : Set M} (hZ : IsClosedAnalytic E Z) {g : E'' → M} {W : Set E''}
    (hW : IsOpen W) (hg : ContinuousOn g W) {z₀ : E''} (hz₀ : z₀ ∈ W) {x : M}
    (hgx : g z₀ = x) (hx : x ∈ Z)
    (han : ∀ z ∈ W, g z ∈ (chartAt E x).source → AnalyticAt ℂ (chartAt E x ∘ g) z) :
    ∃ U : Set E'', IsOpen U ∧ z₀ ∈ U ∧ U ⊆ W ∧
      ∃ (n : ℕ) (f : Fin n → E'' → ℂ), (∀ i, AnalyticOnNhd ℂ (f i) U) ∧
        ∀ z ∈ U, (g z ∈ Z ↔ ∀ i, f i z = 0) := by
  obtain ⟨Uc, hUco, hxUc, -, n, F, hF, hZF⟩ := hZ.2 x hx
  set c := chartAt E x
  have hW' : IsOpen (W ∩ g ⁻¹' c.source) := hg.isOpen_inter_preimage hW c.open_source
  have hcg : ContinuousOn (c ∘ g) (W ∩ g ⁻¹' c.source) :=
    c.continuousOn.comp (hg.mono inter_subset_left) fun z hz => hz.2
  refine ⟨W ∩ g ⁻¹' c.source ∩ (c ∘ g) ⁻¹' Uc, hcg.isOpen_inter_preimage hW' hUco,
    ⟨⟨hz₀, by simp [hgx, c]⟩, by simpa [hgx, c] using hxUc⟩,
    fun z hz => hz.1.1, n, fun i => F i ∘ c ∘ g, fun i z hz => ?_, fun z hz => ?_⟩
  · exact (hF i _ hz.2).comp (han z hz.1.1 hz.1.2)
  · have h := hZF (c (g z)) hz.2
    rwa [c.left_inv hz.1.2] at h

theorem spec_isClosedAnalytic_iff_maximalAtlas_aux [IsManifold 𝓘(ℂ, E) ω M] {Z : Set M} :
    IsClosedAnalytic E Z ↔ IsClosed Z ∧
      ∀ e ∈ IsManifold.maximalAtlas 𝓘(ℂ, E) ω M, ∀ x ∈ Z, x ∈ e.source →
        ∃ U : Set E, IsOpen U ∧ e x ∈ U ∧ U ⊆ e.target ∧
          ∃ (n : ℕ) (f : Fin n → E → ℂ), (∀ i, AnalyticOnNhd ℂ (f i) U) ∧
            ∀ z ∈ U, (e.symm z ∈ Z ↔ ∀ i, f i z = 0) := by
  refine ⟨fun hZ => ⟨hZ.1, fun e he x hx hxe => ?_⟩,
    fun h => ⟨h.1, fun x hx =>
      h.2 _ (IsManifold.chart_mem_maximalAtlas x) x hx (mem_chart_source E x)⟩⟩
  refine exists_local_description_comp hZ e.open_target e.continuousOn_symm (e.map_source hxe)
    (e.left_inv hxe) hx fun z hz hzc => ?_
  have h := analyticAt_chart_comp_of_contMDiffAt (φ := id) he
    (IsManifold.chart_mem_maximalAtlas x)
    (e.map_target hz) hzc contMDiffAt_id
  rwa [e.right_inv hz] at h

theorem spec_isClosedAnalytic_preimage_aux [IsManifold 𝓘(ℂ, E) ω M]
    [IsManifold 𝓘(ℂ, E') ω N] {φ : N → M} (hφ : ContMDiff 𝓘(ℂ, E') 𝓘(ℂ, E) ω φ)
    {Z : Set M} (hZ : IsClosedAnalytic E Z) : IsClosedAnalytic E' (φ ⁻¹' Z) := by
  refine ⟨hZ.1.preimage hφ.continuous, fun y hy => ?_⟩
  set c' := chartAt E' y
  refine exists_local_description_comp (g := φ ∘ c'.symm) hZ c'.open_target
    (hφ.continuous.comp_continuousOn c'.continuousOn_symm) (mem_chart_target E' y)
    (by simp [c', (chartAt E' y).left_inv (mem_chart_source E' y)]) hy fun z hz hzc => ?_
  have h := analyticAt_chart_comp_of_contMDiffAt (IsManifold.chart_mem_maximalAtlas y)
    (IsManifold.chart_mem_maximalAtlas (φ y)) (c'.map_target hz) hzc (hφ _)
  rwa [c'.right_inv hz] at h

theorem spec_isClosedAnalytic_of_localBiholomorph_aux [IsManifold 𝓘(ℂ, E) ω M]
    [IsManifold 𝓘(ℂ, E') ω N] {π : N → M} {Z : Set M} (hZc : IsClosed Z)
    (hloc : ∀ x ∈ Z, ∃ e : OpenPartialHomeomorph N M, x ∈ e.target ∧ EqOn π e e.source ∧
      ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, E') ω e.symm e.target)
    (hZ : IsClosedAnalytic E' (π ⁻¹' Z)) : IsClosedAnalytic E Z := by
  refine ⟨hZc, fun x hx => ?_⟩
  obtain ⟨e, hxe, hπe, he⟩ := hloc x hx
  set d := chartAt E x
  -- on `e.target`, `π ∘ e.symm` is the identity
  have hπ : ∀ m ∈ e.target, π (e.symm m) = m := fun m hm => by
    rw [hπe (e.map_target hm), e.right_inv hm]
  have hW : IsOpen (d.target ∩ d.symm ⁻¹' e.target) :=
    d.isOpen_inter_preimage_symm e.open_target
  have hdx : d.symm (d x) = x := d.left_inv (mem_chart_source E x)
  obtain ⟨U, hUo, hxU, hUW, n, f, hf, hZf⟩ := exists_local_description_comp
    (g := e.symm ∘ d.symm) (z₀ := d x) (x := e.symm x) hZ hW
    (e.continuousOn_symm.comp (d.continuousOn_symm.mono inter_subset_left) fun z hz => hz.2)
    ⟨mem_chart_target E x, show d.symm (d x) ∈ e.target by rw [hdx]; exact hxe⟩
    (by simp only [Function.comp_apply, hdx]) (show π (e.symm x) ∈ Z by rw [hπ x hxe]; exact hx)
    fun z hz hzc => by
      have h := analyticAt_chart_comp_of_contMDiffAt (IsManifold.chart_mem_maximalAtlas x)
        (IsManifold.chart_mem_maximalAtlas (e.symm x)) (d.map_target hz.1) hzc
        (he.contMDiffAt (e.open_target.mem_nhds hz.2))
      rwa [d.right_inv hz.1] at h
  refine ⟨U, hUo, hxU, fun z hz => (hUW hz).1, n, f, hf, fun z hz => ?_⟩
  rw [← hZf z hz, Function.comp_apply, mem_preimage, hπ _ (hUW hz).2]

theorem spec_isClosedAnalytic_of_theta_preimage_aux {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [FiniteDimensional ℂ V] [IsManifold 𝓘(ℂ, E) ω M] (D : Datum (V := V))
    {θ : V → ℂ} (hθ : θ ∈ sections D) {π : V → M} {Z : Set M} (hZc : IsClosed Z)
    (hloc : ∀ x ∈ Z, ∃ e : OpenPartialHomeomorph V M, x ∈ e.target ∧ EqOn π e e.source ∧
      ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, V) ω e.symm e.target)
    (hZ : π ⁻¹' Z = {v | θ v = 0}) : IsClosedAnalytic E Z :=
  spec_isClosedAnalytic_of_localBiholomorph_aux hZc hloc
    (hZ ▸ AnalyticDivisorAlgebraic2.spec_isClosedAnalytic_theta D hθ)

theorem spec_not_isClosedAnalytic_graph_re_aux :
    ¬ IsClosedAnalytic (ℂ × ℂ) {w : ℂ × ℂ | w.1 = (w.2.re : ℂ)} := by
  intro h
  have h' := spec_isClosedAnalytic_preimage_aux (ContinuousLinearMap.inr ℂ ℂ ℂ).contMDiff h
  refine not_isClosedAnalytic_re_eq_zero ?_
  convert h' using 1
  ext s
  simp [eq_comm]

end Charts

end HodgeLean.Foundations.AnalyticDivisorAlgebraic3
