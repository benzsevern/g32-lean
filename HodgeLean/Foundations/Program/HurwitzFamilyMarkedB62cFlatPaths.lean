import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cRegular
import Mathlib.Analysis.Calculus.ContDiff.Deriv

noncomputable section

namespace HodgeLean.Foundations.Program

open Filter Asymptotics
open scoped Topology NNReal

theorem b6m_hasDerivAt_lipschitz_comp_zero {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {K : ℝ≥0} (hf : LipschitzWith K f)
    {γ : ℝ → E} {s : ℝ} (hγ : HasDerivAt γ 0 s) :
    HasDerivAt (f ∘ γ) 0 s := by
  have hsmall : (fun t ↦ γ t - γ s) =o[𝓝 s] (fun t ↦ t - s) := by
    simpa only [smul_zero, sub_zero] using hγ.isLittleO
  have hbound : (fun t ↦ f (γ t) - f (γ s)) =O[𝓝 s] (fun t ↦ γ t - γ s) :=
    IsBigO.of_bound K (Filter.Eventually.of_forall fun t ↦ hf.norm_sub_le (γ t) (γ s))
  apply HasDerivAt.of_isLittleO
  simpa only [Function.comp_apply, smul_zero, sub_zero] using hbound.trans_isLittleO hsmall

theorem b6m_lipschitz_comp_deriv_bound {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {K : ℝ≥0} (hf : LipschitzWith K f)
    {γ : ℝ → E} {s : ℝ} (hγ : DifferentiableAt ℝ γ s)
    (hd : deriv γ s ≠ 0 → DifferentiableAt ℝ f (γ s)) :
    DifferentiableAt ℝ (f ∘ γ) s ∧ ‖deriv (f ∘ γ) s‖ ≤ K * ‖deriv γ s‖ := by
  by_cases hz : deriv γ s = 0
  · have h := b6m_hasDerivAt_lipschitz_comp_zero hf (hz ▸ hγ.hasDerivAt)
    exact ⟨h.differentiableAt, by simp [h.deriv, hz]⟩
  · have h := (hd hz).hasFDerivAt.comp_hasDerivAt s hγ.hasDerivAt
    refine ⟨h.differentiableAt, ?_⟩
    rw [h.deriv]
    exact ((fderiv ℝ f (γ s)).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hf) (norm_nonneg _))

theorem b6m_contDiff_lipschitz_comp_flat {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {K : ℝ≥0} (hf : LipschitzWith K f)
    {γ : ℝ → E} (hγ : ContDiff ℝ 1 γ)
    (hd : ∀ s, deriv γ s ≠ 0 → ContDiffAt ℝ 1 f (γ s)) :
    ContDiff ℝ 1 (f ∘ γ) := by
  have hbound (s : ℝ) := b6m_lipschitz_comp_deriv_bound hf
    (hγ.differentiable one_ne_zero s) (fun hs ↦ (hd s hs).differentiableAt one_ne_zero)
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun s ↦ (hbound s).1, continuous_iff_continuousAt.mpr ?_⟩
  intro s
  by_cases hs : deriv γ s = 0
  · have hz : deriv (f ∘ γ) s = 0 :=
      (b6m_hasDerivAt_lipschitz_comp_zero hf
        (hs ▸ (hγ.differentiable one_ne_zero s).hasDerivAt)).deriv
    change Tendsto (deriv (f ∘ γ)) (𝓝 s) (𝓝 (deriv (f ∘ γ) s))
    rw [hz, tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero (fun _ ↦ norm_nonneg _) (fun t ↦ (hbound t).2)
    have h := ((hγ.continuous_deriv le_rfl).continuousAt (x := s)).norm.const_mul (K : ℝ)
    simpa only [ContinuousAt, hs, norm_zero, mul_zero] using h
  · exact (((hd s hs).comp s hγ.contDiffAt).derivWithin (m := 0) (by simp)).continuousAt

theorem b6m_radial_tent_contDiffAt (c z : ℂ) (r : ℝ) (hr : 0 < r)
    (hc : z ≠ c) (hb : dist z c ≠ r) :
    ContDiffAt ℝ 1 (fun x : ℂ ↦ max 0 (1 - dist x c / r)) z := by
  let f : ℂ → ℝ := fun x ↦ 1 - dist x c / r
  have hf : Continuous f := continuous_const.sub ((continuous_id.dist continuous_const).div_const r)
  have hd : ContDiffAt ℝ 1 f z := by
    dsimp [f]
    simp only [dist_eq_norm, div_eq_mul_inv]
    exact contDiffAt_const.sub
      (((contDiffAt_id.sub contDiffAt_const).norm ℝ (sub_ne_zero.mpr hc)).mul contDiffAt_const)
  have hn : f z ≠ 0 := by
    dsimp [f]
    intro h
    apply hb
    apply (div_eq_one_iff_eq hr.ne').mp
    linarith
  rcases lt_or_gt_of_ne hn with hn | hn
  · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    have he : ∀ᶠ x in 𝓝 z, f x < 0 := (isOpen_lt hf continuous_const).mem_nhds hn
    filter_upwards [he] with x hx
    exact max_eq_left hx.le
  · apply hd.congr_of_eventuallyEq
    have he : ∀ᶠ x in 𝓝 z, 0 < f x := (isOpen_lt continuous_const hf).mem_nhds hn
    filter_upwards [he] with x hx
    exact max_eq_right hx.le

theorem b6m_plane_contDiff_comp_flat (b t : Fin 10 → ℂ) (hb : b ∈ b6_chart)
    {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ)
    (hflat : ∀ s i, γ s = b i ∨ dist (γ s) (b i) = b6t_radius b → deriv γ s = 0) :
    ContDiff ℝ 1 (b6t_plane b t ∘ γ) := by
  have hr := (b6t_discs b hb).1
  have hρ (i : Fin 10) :
      ContDiff ℝ 1 (fun s ↦ max 0 (1 - dist (γ s) (b i) / b6t_radius b)) := by
    apply b6m_contDiff_lipschitz_comp_flat (b6m_radial_tent_lipschitz (b i) _ hr) hγ
    intro s hs
    apply b6m_radial_tent_contDiffAt (b i) (γ s) _ hr
    · exact fun h ↦ hs (hflat s i (Or.inl h))
    · exact fun h ↦ hs (hflat s i (Or.inr h))
  exact hγ.add (ContDiff.sum fun i _ ↦ (hρ i).smul contDiff_const)

theorem b6m_contDiffAt_real_of_analytic_comp {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : E → ℂ} {k : ℂ → ℂ} {z : E}
    (hg : ContinuousAt g z) (hk : AnalyticAt ℂ k (g z))
    (hkd : fderiv ℂ k (g z) ≠ 0) (hkg : ContDiffAt ℝ 1 (k ∘ g) z) :
    ContDiffAt ℝ 1 g z := by
  obtain ⟨s, hs, _, _, hsk⟩ := b4cov_exists_localInverse (by simp) (by simp) hk hkd
  have heq : g =ᶠ[𝓝 z] s ∘ (k ∘ g) := by
    filter_upwards [hg.eventually hsk] with w hw
    exact hw.symm
  exact (((hs.contDiffAt.restrict_scalars ℝ).comp z hkg)).congr_of_eventuallyEq heq

open Manifold
open scoped Manifold ContDiff

theorem b6m_contMDiffAt_path_of_unramified_comp {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {D X : Type}
    [TopologicalSpace D] [TopologicalSpace X] [ChartedSpace ℂ D] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ, ℂ) ω D] [IsManifold 𝓘(ℂ, ℂ) ω X]
    (g : E → D) (k : D → X) (z : E) (hg : ContinuousAt g z)
    (hk : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω k)
    (hkd : mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) k (g z) ≠ 0)
    (hkg : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℂ) 1 (k ∘ g) z) :
    ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℂ) 1 g z := by
  let ψ := extChartAt 𝓘(ℂ, ℂ) (g z)
  let G : E → ℂ := ψ ∘ g
  let K := writtenInExtChartAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (g z) k
  have hGc : ContinuousAt G z :=
    (contMDiffAt_extChartAt (I := 𝓘(ℂ, ℂ)) (n := ω) (x := g z)).continuousAt.comp hg
  have hK : AnalyticAt ℂ K (G z) :=
    b4cov_analyticOnNhd k hk (g z) _ (b4cov_mem_good k (g z))
  have hKd : fderiv ℂ K (G z) ≠ 0 :=
    hkd ∘ (b4cov_mfderiv_eq_zero_iff k hk (g z) (g z)
      (mem_extChartAt_source _) (mem_extChartAt_source _)).mpr
  have heq : K ∘ G =ᶠ[𝓝 z] extChartAt 𝓘(ℂ, ℂ) (k (g z)) ∘ (k ∘ g) := by
    have hsrc : ψ.source ∈ 𝓝 (g z) := extChartAt_source_mem_nhds (I := 𝓘(ℂ, ℂ)) (g z)
    filter_upwards [hg.eventually hsrc] with w hw
    change extChartAt 𝓘(ℂ, ℂ) (k (g z)) (k (ψ.symm (ψ (g w)))) = _
    rw [ψ.left_inv hw]
    rfl
  have hF : ContDiffAt ℝ 1 (extChartAt 𝓘(ℂ, ℂ) (k (g z)) ∘ (k ∘ g)) z := by
    have H := (contMDiffAt_iff_target.mp hkg).2.contDiffAt
    simpa only [extChartAt_coe, modelWithCornersSelf_coe, Function.comp_apply] using H
  have hG := b6m_contDiffAt_real_of_analytic_comp hGc hK hKd
    (hF.congr_of_eventuallyEq heq)
  apply contMDiffAt_iff_target.mpr
  refine ⟨hg, ?_⟩
  apply contMDiffAt_iff_contDiffAt.mpr
  simpa only [G, ψ, extChartAt_coe, modelWithCornersSelf_coe] using hG

attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

theorem b6m_filled_path_contMDiff_flat {C D : Type}
    [TopologicalSpace C] [TopologicalSpace D] [ChartedSpace ℂ D]
    [IsManifold 𝓘(ℂ, ℂ) ω D]
    (b t : Fin 10 → ℂ) (hb : b ∈ b6_chart)
    (f : C → OnePoint ℂ) (k : D → OnePoint ℂ)
    (hk : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω k)
    (e : C ≃ₜ D) (he : ∀ x, k (e x) = b6t_sphere b t (f x))
    (γ : ℝ → C) (hγ : Continuous γ) (p : ℝ → ℂ) (hp : ContDiff ℝ 1 p)
    (hproj : ∀ s, f (γ s) = (p s : OnePoint ℂ))
    (hflat : ∀ s i, p s = b i ∨ dist (p s) (b i) = b6t_radius b → deriv p s = 0)
    (hkd : ∀ s, mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) k (e (γ s)) ≠ 0) :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) 1 (e ∘ γ) := by
  have H := b3A_contMDiff_comp_real (fun z : ℂ ↦ (z : OnePoint ℂ))
    b4cov_coe_contMDiff (b6t_plane b t ∘ p)
    (b6m_plane_contDiff_comp_flat b t hb hp hflat).contMDiff
  have hcomp : k ∘ (e ∘ γ) = (fun z : ℂ ↦ (z : OnePoint ℂ)) ∘ (b6t_plane b t ∘ p) := by
    funext s
    change k (e (γ s)) = (b6t_plane b t (p s) : OnePoint ℂ)
    rw [he, hproj]
    rfl
  intro s
  apply b6m_contMDiffAt_path_of_unramified_comp (e ∘ γ) k s
    (e.continuous.comp hγ).continuousAt hk (hkd s)
  rw [hcomp]
  exact H s

end HodgeLean.Foundations.Program
