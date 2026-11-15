import HodgeLean.Foundations.Program.SchoenSelectedGeometrySphereAnalytic
import HodgeLean.Foundations.Program.RiemannRochProofs

noncomputable section
set_option maxRecDepth 2000
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry Filter Topology Set
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Program
attribute [local irreducible] b4cov_lineEquiv

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
theorem s0_injective_holomorphic_curve_coordinates
    {E Y : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace Y] [ChartedSpace E Y] [IsManifold 𝓘(ℂ, E) ω Y]
    (hE : Module.finrank ℂ E = 1)
    (q : ℂ → Y) (x : ℂ) (hq : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, E) ω q x)
    (s : Set ℂ) (hs : s ∈ 𝓝 x) (hi : Set.InjOn q s) :
    ∃ e : OpenPartialHomeomorph ℂ Y, x ∈ e.source ∧ e x = q x ∧
      (e : ℂ → Y) =ᶠ[𝓝 x] q ∧
      ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, E) ω e x ∧
      ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ω e.symm (q x) := by
  let φ := (chartAt E (q x)).trans
    (b4cov_lineEquiv hE).symm.toHomeomorph.toOpenPartialHomeomorph
  have hx : q x ∈ φ.source := ⟨mem_chart_source E (q x), Set.mem_univ _⟩
  have hφ : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ω φ (q x) := by
    change ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ω
      ((b4cov_lineEquiv hE).symm ∘ chartAt E (q x)) (q x)
    have hlin : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ω (b4cov_lineEquiv hE).symm :=
      (b4cov_lineEquiv hE).symm.contDiff.contMDiff
    exact hlin.contMDiffAt.comp (q x)
      (contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas (q x))
        (mem_chart_source E (q x)))
  have ha : AnalyticAt ℂ (φ ∘ q) x := (hφ.comp x hq).contDiffAt.analyticAt
  have hsource : ∀ᶠ z in 𝓝 x, q z ∈ φ.source :=
    hq.continuousAt (φ.open_source.mem_nhds hx)
  have hU : s ∩ q ⁻¹' φ.source ∈ 𝓝 x := inter_mem hs hsource
  have hiU : Set.InjOn (φ ∘ q) (s ∩ q ⁻¹' φ.source) := by
    intro a ha b hb hab
    exact hi ha.1 hb.1 (φ.injOn ha.2 hb.2 hab)
  obtain ⟨d, hdx, hd⟩ := RiemannRochTop_injective_analytic_local_homeomorph
    (φ ∘ q) x ha _ hU hiU
  let e := d.trans φ.symm
  have hemem : x ∈ e.source := by
    refine ⟨hdx, ?_⟩
    change d x ∈ φ.target
    rw [hd]
    exact φ.map_source hx
  have heq : (e : ℂ → Y) =ᶠ[𝓝 x] q := by
    filter_upwards [hsource] with z hz
    change φ.symm (d z) = q z
    rw [hd]
    exact φ.left_inv hz
  have hda : AnalyticAt ℂ d x := by rw [hd]; exact ha
  have hdi : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω d.symm (φ (q x)) := by
    have h : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω d.symm (d x) :=
      (RiemannRochTop_analytic_local_homeomorph_inverse d x hdx hda).contDiffAt.contMDiffAt
    simpa only [hd, Function.comp_apply] using h
  exact ⟨e, hemem, heq.eq_of_nhds, heq, hq.congr_of_eventuallyEq heq, hdi.comp (q x) hφ⟩

#print axioms s0_injective_holomorphic_curve_coordinates

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
theorem s0_curve_homeomorph_inverse_holomorphic
    {A E Y : Type} [TopologicalSpace A] [ChartedSpace ℂ A] [IsManifold 𝓘(ℂ, ℂ) ω A]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace Y] [ChartedSpace E Y] [IsManifold 𝓘(ℂ, E) ω Y]
    (hE : Module.finrank ℂ E = 1) (e : A ≃ₜ Y)
    (he : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, E) ω e) :
    ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ω e.symm := by
  intro y
  let a := e.symm y
  let c := chartAt ℂ a
  let t := c a
  have ha : a ∈ c.source := mem_chart_source ℂ a
  have ht : t ∈ c.target := c.map_source ha
  let q : ℂ → Y := e ∘ c.symm
  have hqt : q t = y := by
    change e (c.symm (c a)) = y
    rw [c.left_inv ha]
    exact e.apply_symm_apply y
  have hc : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω c.symm t :=
    contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas a) ht
  have hq : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, E) ω q t :=
    (he.contMDiffAt).comp t hc
  have hi : Set.InjOn q c.target := by
    intro z hz w hw h
    exact c.symm.injOn hz hw (e.injective h)
  obtain ⟨d, hdt, hde, hdq, _, hdi⟩ :=
    s0_injective_holomorphic_curve_coordinates hE q t hq c.target (c.open_target.mem_nhds ht) hi
  have hdy : d t = y := hde.trans hqt
  have hds : d.symm y = t := by rw [← hdy]; exact d.left_inv hdt
  have hdinv : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ω d.symm y := by simpa only [hqt] using hdi
  have hdcont : Tendsto d.symm (𝓝 y) (𝓝 t) := by
    simpa only [hdy] using d.tendsto_symm hdt
  have htarget : d.target ∈ 𝓝 y := by
    rw [← hdy]
    exact d.open_target.mem_nhds (d.map_source hdt)
  have heq : (c.symm ∘ d.symm) =ᶠ[𝓝 y] e.symm := by
    filter_upwards [hdcont hdq, htarget] with z hz hzt
    apply e.injective
    change q (d.symm z) = e (e.symm z)
    rw [e.apply_symm_apply]
    exact hz.symm.trans (d.right_inv hzt)
  exact (hc.comp_of_eq hdinv hds).congr_of_eventuallyEq heq.symm

#print axioms s0_curve_homeomorph_inverse_holomorphic

attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
theorem s0_sphere_projective_inverse_holomorphic :
    letI : SmoothOfRelativeDimension 1
        (Over.mk (ProjectiveSpace.toBase (Fin 2) (Spec ↧ℂ))).hom :=
      s0_complex_projective_relative_dimension 1
    ContMDiff 𝓘(ℂ, Fin 1 → ℂ) 𝓘(ℂ, ℂ) ω s0_sphere_projective_homeomorph.symm := by
  letI : SmoothOfRelativeDimension 1
      (Over.mk (ProjectiveSpace.toBase (Fin 2) (Spec ↧ℂ))).hom :=
    s0_complex_projective_relative_dimension 1
  exact s0_curve_homeomorph_inverse_holomorphic (by simp)
    s0_sphere_projective_homeomorph s0_sphere_projective_holomorphic

#print axioms s0_sphere_projective_inverse_holomorphic

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The scheme-theoretic projective line is a smooth projective model of the analytic sphere.
Source: Hartshorne, Algebraic Geometry, II.2.5, the two standard projective-line charts. -/
theorem s0_sphere_curve_model :
    ∃ X : Over (Spec ↧ℂ),
      ∃ (_ : IsIntegral X.left) (_ : Smooth X.hom) (_ : IsProjective X.hom),
      TopologicalSpace.dim X.left = 1 ∧
      ∃ e : OnePoint ℂ ≃ₜ AlgebraicGeometry.ComplexPoint X,
        ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, Fin (TopologicalSpace.dim X.left) → ℂ) ω e ∧
        ContMDiff 𝓘(ℂ, Fin (TopologicalSpace.dim X.left) → ℂ) 𝓘(ℂ, ℂ) ω e.symm := by
  let X := Over.mk (ProjectiveSpace.toBase (Fin 2) (Spec ↧ℂ))
  letI : IsIntegral X.left := s0_complex_projective_integral 1
  letI : Smooth X.hom := s0_projective_space_smooth 1 (Spec ↧ℂ)
  letI : IsProjective X.hom := s0_projective_space_projective 1 (Spec ↧ℂ)
  have hd : TopologicalSpace.dim X.left = 1 := s0_complex_projective_dimension 1
  have hcomp : ∀ (d : ℕ) (_ : d = 1) (h : SmoothOfRelativeDimension d X.hom),
      letI := h
      ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, Fin d → ℂ) ω s0_sphere_projective_homeomorph ∧
      ContMDiff 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, ℂ) ω s0_sphere_projective_homeomorph.symm := by
    intro d hd h
    subst d
    exact ⟨s0_sphere_projective_holomorphic, s0_sphere_projective_inverse_holomorphic⟩
  obtain ⟨hforward, hinverse⟩ := hcomp _ hd inferInstance
  exact ⟨X, inferInstance, inferInstance, inferInstance, hd,
    s0_sphere_projective_homeomorph, hforward, hinverse⟩

#print axioms s0_sphere_curve_model

end HodgeLean.Foundations.Program
