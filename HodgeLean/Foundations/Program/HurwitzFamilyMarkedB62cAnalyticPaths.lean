import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cSegments
import Mathlib.Analysis.Analytic.IsolatedZeros

noncomputable section

namespace HodgeLean.Foundations.Program

open Set Filter Topology

theorem b6m_analytic_eq_or_finite {f g : ℝ → ℝ} {U K : Set ℝ}
    (hf : AnalyticOnNhd ℝ f U) (hg : AnalyticOnNhd ℝ g U)
    (hU : IsPreconnected U) (hK : IsCompact K) (hKU : K ⊆ U) :
    EqOn f g U ∨ {s ∈ K | f s = g s}.Finite := by
  rcases hf.eqOn_or_eventually_ne_of_preconnected hg hU with h | h
  · exact Or.inl h
  · right
    have h' := hK.finite_sdiff_of_mem_codiscreteWithin
      ((codiscreteWithin_mono hKU) h)
    exact h'.subset (fun s hs ↦ ⟨hs.1, fun hn ↦ hn hs.2⟩)

theorem b6m_analytic_circle_eq_or_finite {p : ℝ → ℂ} {U K : Set ℝ}
    (hp : AnalyticOnNhd ℝ p U) (hU : IsPreconnected U)
    (hK : IsCompact K) (hKU : K ⊆ U) (c : ℂ) (r : ℝ) (hr : 0 ≤ r) :
    (∀ s ∈ U, dist (p s) c = r) ∨ {s ∈ K | dist (p s) c = r}.Finite := by
  have ha : AnalyticOnNhd ℝ (fun s ↦ Complex.normSq (p s - c)) U := by
    intro s hs
    have h : AnalyticAt ℝ (fun s ↦ p s - c) s := (hp s hs).sub analyticAt_const
    have hre := (Complex.reCLM.analyticAt (p s - c)).comp (f := fun s ↦ p s - c) h
    have him := (Complex.imCLM.analyticAt (p s - c)).comp (f := fun s ↦ p s - c) h
    exact hre.mul hre |>.add (him.mul him)
  have heq (s : ℝ) : Complex.normSq (p s - c) = r ^ 2 ↔ dist (p s) c = r := by
    rw [← Complex.sq_norm, ← dist_eq_norm]
    exact sq_eq_sq₀ dist_nonneg hr
  rcases b6m_analytic_eq_or_finite ha (fun _ _ ↦ analyticAt_const) hU hK hKU with h | h
  · exact Or.inl (fun s hs ↦ (heq s).mp (h hs))
  · exact Or.inr (h.subset (fun s hs ↦ ⟨hs.1, (heq s).mpr hs.2⟩))

theorem b6m_analytic_tent_constant_or_finite {p : ℝ → ℂ} {U K : Set ℝ}
    (hp : AnalyticOnNhd ℝ p U) (hU : IsPreconnected U)
    (hK : IsCompact K) (hKU : K ⊆ U) (c : ℂ) (r : ℝ) (hr : 0 < r) :
    (∃ d : ℝ, ∀ s ∈ U, max 0 (1 - dist (p s) c / r) = d) ∨
      {s ∈ K | p s = c ∨ dist (p s) c = r}.Finite := by
  rcases b6m_analytic_circle_eq_or_finite hp hU hK hKU c 0 le_rfl with h | hzero
  · left
    exact ⟨1, fun s hs ↦ by rw [h s hs]; norm_num⟩
  rcases b6m_analytic_circle_eq_or_finite hp hU hK hKU c r hr.le with h | hcircle
  · left
    exact ⟨0, fun s hs ↦ by rw [h s hs, div_self hr.ne']; norm_num⟩
  · right
    apply (hzero.union hcircle).subset
    rintro s ⟨hs, heq | heq⟩
    · exact Or.inl ⟨hs, by rw [heq, dist_self]⟩
    · exact Or.inr ⟨hs, heq⟩

theorem b6m_plane_reparam_constant_or_finite (b t : Fin 10 → ℂ) (hb : b ∈ b6_chart)
    (p : ℝ → ℂ) (hp : ∀ s ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ 1 p s)
    (hbad : ∀ i, (∃ d : ℝ, ∀ s ∈ Icc (0 : ℝ) 1,
        max 0 (1 - dist (p s) (b i) / b6t_radius b) = d) ∨
      {s ∈ Icc (0 : ℝ) 1 | p s = b i ∨ dist (p s) (b i) = b6t_radius b}.Finite) :
    ∃ σ : ℝ → ℝ, ContDiff ℝ 1 σ ∧ (∀ s, σ s ∈ Icc 0 1) ∧
      (∀ᶠ s in 𝓝 0, σ s = 0) ∧ (∀ᶠ s in 𝓝 1, σ s = 1) ∧
      ContDiff ℝ 1 (p ∘ σ) ∧ ContDiff ℝ 1 (b6t_plane b t ∘ (p ∘ σ)) ∧
      (∀ s, σ s ∈ Ioo 0 1 →
        (∀ i, p (σ s) ≠ b i ∧ dist (p (σ s)) (b i) ≠ b6t_radius b) →
        0 < deriv σ s) := by
  classical
  let S (i : Fin 10) : Set ℝ := if
      ∃ d : ℝ, ∀ s ∈ Icc (0 : ℝ) 1,
        max 0 (1 - dist (p s) (b i) / b6t_radius b) = d
    then ∅ else {s ∈ Icc (0 : ℝ) 1 | p s = b i ∨ dist (p s) (b i) = b6t_radius b}
  have hS (i : Fin 10) : (S i).Finite := by
    dsimp only [S]
    split_ifs with h
    · exact finite_empty
    · exact (hbad i).resolve_left h
  obtain ⟨σ, hd, hr, h0, h1, hflat, hpos⟩ :=
    b6m_finite_flat_step (⋃ i, S i) (finite_iUnion hS)
  have hγ : ContDiff ℝ 1 (p ∘ σ) :=
    contDiff_iff_contDiffAt.mpr (fun s ↦ (hp (σ s) (hr s)).comp s hd.contDiffAt)
  have hρ (i : Fin 10) :
      ContDiff ℝ 1 (fun s ↦ max 0 (1 - dist (p (σ s)) (b i) / b6t_radius b)) := by
    by_cases hc : ∃ d : ℝ, ∀ s ∈ Icc (0 : ℝ) 1,
        max 0 (1 - dist (p s) (b i) / b6t_radius b) = d
    · obtain ⟨d, hd⟩ := hc
      have heq : (fun s ↦ max 0 (1 - dist (p (σ s)) (b i) / b6t_radius b)) =
          fun _ ↦ d := funext (fun s ↦ hd (σ s) (hr s))
      rw [heq]
      exact contDiff_const
    · apply b6m_contDiff_lipschitz_comp_flat
        (b6m_radial_tent_lipschitz (b i) _ (b6t_discs b hb).1) hγ
      intro s hs
      apply b6m_radial_tent_contDiffAt (b i) _ _ (b6t_discs b hb).1
      all_goals
        intro heq
        apply hs
        have hmem : σ s ∈ S i := by
          simp only [S, if_neg hc]
          exact ⟨hr s, by first | exact Or.inl heq | exact Or.inr heq⟩
        have H := ((hp (σ s) (hr s)).differentiableAt one_ne_zero).hasFDerivAt.comp_hasDerivAt
          s (hflat s (mem_iUnion.mpr ⟨i, hmem⟩))
        simpa using H.deriv
  refine ⟨σ, hd, hr, h0, h1, hγ,
    hγ.add (ContDiff.sum fun i _ ↦ (hρ i).smul contDiff_const), ?_⟩
  intro s hs hreg
  apply hpos s hs
  intro hmem
  obtain ⟨i, hi'⟩ := mem_iUnion.mp hmem
  dsimp only [S] at hi'
  split_ifs at hi' with hc
  · exact notMem_empty _ hi'
  · exact hi'.2.elim (hreg i).1 (hreg i).2

theorem b6m_analytic_plane_reparam (b t : Fin 10 → ℂ) (hb : b ∈ b6_chart)
    (p : ℝ → ℂ) {U : Set ℝ} (hp : AnalyticOnNhd ℝ p U)
    (hU : IsPreconnected U) (hIU : Icc (0 : ℝ) 1 ⊆ U) :
    ∃ σ : ℝ → ℝ, ContDiff ℝ 1 σ ∧ (∀ s, σ s ∈ Icc 0 1) ∧
      (∀ᶠ s in 𝓝 0, σ s = 0) ∧ (∀ᶠ s in 𝓝 1, σ s = 1) ∧
      ContDiff ℝ 1 (p ∘ σ) ∧ ContDiff ℝ 1 (b6t_plane b t ∘ (p ∘ σ)) ∧
      (∀ s, σ s ∈ Ioo 0 1 →
        (∀ i, p (σ s) ≠ b i ∧ dist (p (σ s)) (b i) ≠ b6t_radius b) →
        0 < deriv σ s) := by
  apply b6m_plane_reparam_constant_or_finite b t hb p
    (fun s hs ↦ (hp s (hIU hs)).contDiffAt)
  intro i
  rcases b6m_analytic_tent_constant_or_finite hp hU isCompact_Icc hIU
    (b i) (b6t_radius b) (b6t_discs b hb).1 with h | h
  · obtain ⟨d, hd⟩ := h
    exact Or.inl ⟨d, fun s hs ↦ hd s (hIU hs)⟩
  · exact Or.inr h

open Manifold
open scoped Manifold ContDiff

attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

theorem b6m_filling_analytic_reparam {C D : Type}
    [TopologicalSpace C] [TopologicalSpace D] [ChartedSpace ℂ C] [ChartedSpace ℂ D]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [IsManifold 𝓘(ℂ, ℂ) ω D]
    (b t : Fin 10 → ℂ) (hb : b ∈ b6_chart)
    (f : C → OnePoint ℂ) (k : D → OnePoint ℂ)
    (hk : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω k)
    (e : C ≃ₜ D) (he : ∀ x, k (e x) = b6t_sphere b t (f x))
    (γ : ℝ → C) (hγ : ∀ s ∈ Icc (0 : ℝ) 1,
      ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) 1 γ s)
    (p : ℝ → ℂ) {U : Set ℝ} (hp : AnalyticOnNhd ℝ p U)
    (hU : IsPreconnected U) (hIU : Icc (0 : ℝ) 1 ⊆ U)
    (hproj : ∀ s ∈ Icc (0 : ℝ) 1, f (γ s) = (p s : OnePoint ℂ))
    (hkd : ∀ s ∈ Icc (0 : ℝ) 1, mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) k (e (γ s)) ≠ 0) :
    ∃ σ : ℝ → ℝ, ContDiff ℝ 1 σ ∧ (∀ s, σ s ∈ Icc 0 1) ∧
      σ 0 = 0 ∧ σ 1 = 1 ∧
      b3A_IsGoodPath (E := ℂ) (γ ∘ σ) (γ 0) (γ 1) ∧
      b3A_IsGoodPath (E := ℂ) (e ∘ (γ ∘ σ)) (e (γ 0)) (e (γ 1)) ∧
      (∀ s, σ s ∈ Ioo 0 1 →
        (∀ i, p (σ s) ≠ b i ∧ dist (p (σ s)) (b i) ≠ b6t_radius b) →
        0 < deriv σ s) := by
  obtain ⟨σ, hd, hr, h0, h1, _, htrans, hpos⟩ :=
    b6m_analytic_plane_reparam b t hb p hp hU hIU
  have hg : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) 1 (γ ∘ σ) :=
    fun s ↦ (hγ (σ s) (hr s)).comp s (hd.contMDiff s)
  have H := b3A_contMDiff_comp_real (fun z : ℂ ↦ (z : OnePoint ℂ))
    b4cov_coe_contMDiff (b6t_plane b t ∘ (p ∘ σ)) htrans.contMDiff
  have hcomp : k ∘ (e ∘ (γ ∘ σ)) =
      (fun z : ℂ ↦ (z : OnePoint ℂ)) ∘ (b6t_plane b t ∘ (p ∘ σ)) := by
    funext s
    change k (e (γ (σ s))) = (b6t_plane b t (p (σ s)) : OnePoint ℂ)
    rw [he, hproj (σ s) (hr s)]
    rfl
  have hge : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) 1 (e ∘ (γ ∘ σ)) := by
    intro s
    apply b6m_contMDiffAt_path_of_unramified_comp _ k s
      (e.continuous.comp hg.continuous).continuousAt hk (hkd (σ s) (hr s))
    rw [hcomp]
    exact H s
  exact ⟨σ, hd, hr, h0.self_of_nhds, h1.self_of_nhds,
    ⟨hg, h0.mono (fun s hs ↦ congrArg γ hs), h1.mono (fun s hs ↦ congrArg γ hs)⟩,
    ⟨hge, h0.mono (fun s hs ↦ congrArg (e ∘ γ) hs),
      h1.mono (fun s hs ↦ congrArg (e ∘ γ) hs)⟩, hpos⟩

theorem b6m_analyticAt_finite_coordinate {g : ℂ → OnePoint ℂ} {z : ℂ}
    (hg : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω g z)
    (hz : g z ≠ OnePoint.infty) : AnalyticAt ℂ (b4cov_chart0 ∘ g) z := by
  obtain ⟨w, hw⟩ := OnePoint.ne_infty_iff_exists.mp hz
  have H := (contMDiffAt_iff_target.mp hg).2
  have H' : ContDiffAt ℂ ω (b4cov_chart0 ∘ g) z := by
    apply contMDiffAt_iff_contDiffAt.mp
    simpa only [extChartAt_coe, modelWithCornersSelf_coe, Function.comp_apply,
      ← hw, b4cov_chartAt_coe, Function.id_comp] using H
  exact H'.analyticAt

theorem b6m_analytic_segment_projection {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] (f : C → OnePoint ℂ)
    (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f) (a v : ℂ) (ι : ℂ → C)
    (hi : ∀ z ∈ segment ℝ a (a + v), ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω ι z)
    (hfin : ∀ z ∈ segment ℝ a (a + v), f (ι z) ≠ OnePoint.infty) :
    AnalyticOnNhd ℝ (fun s : ℝ ↦ b4cov_chart0 (f (ι (a + s • v)))) (Icc 0 1) := by
  intro s hs
  have hseg : a + s • v ∈ segment ℝ a (a + v) := by
    rw [segment_eq_image']
    exact ⟨s, hs, by simp⟩
  have H := b6m_analyticAt_finite_coordinate
    ((hf (ι (a + s • v))).comp (a + s • v) (hi _ hseg)) (hfin _ hseg)
  have hA : AnalyticAt ℝ (fun s : ℝ ↦ a + s • v) s :=
    analyticAt_const.add (analyticAt_id.smul analyticAt_const)
  exact H.restrictScalars.comp (f := fun s : ℝ ↦ a + s • v) hA

theorem b6m_filling_holomorphic_segment {C D : Type}
    [TopologicalSpace C] [TopologicalSpace D] [ChartedSpace ℂ C] [ChartedSpace ℂ D]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [IsManifold 𝓘(ℂ, ℂ) ω D]
    (b t : Fin 10 → ℂ) (hb : b ∈ b6_chart)
    (f : C → OnePoint ℂ) (k : D → OnePoint ℂ)
    (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f)
    (hk : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω k)
    (e : C ≃ₜ D) (he : ∀ x, k (e x) = b6t_sphere b t (f x))
    (a v : ℂ) (ι : ℂ → C)
    (hi : ∀ z ∈ segment ℝ a (a + v), ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω ι z)
    (hfin : ∀ z ∈ segment ℝ a (a + v), f (ι z) ≠ OnePoint.infty)
    (hkd : ∀ z ∈ segment ℝ a (a + v), mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) k (e (ι z)) ≠ 0) :
    ∃ σ : ℝ → ℝ, ContDiff ℝ 1 σ ∧ (∀ s, σ s ∈ Icc 0 1) ∧
      σ 0 = 0 ∧ σ 1 = 1 ∧
      b3A_IsGoodPath (E := ℂ) (fun s ↦ ι (a + σ s • v)) (ι a) (ι (a + v)) ∧
      b3A_IsGoodPath (E := ℂ) (fun s ↦ e (ι (a + σ s • v)))
        (e (ι a)) (e (ι (a + v))) ∧
      (∀ s, σ s ∈ Ioo 0 1 →
        (∀ i, b4cov_chart0 (f (ι (a + σ s • v))) ≠ b i ∧
          dist (b4cov_chart0 (f (ι (a + σ s • v)))) (b i) ≠ b6t_radius b) →
        0 < deriv σ s) := by
  let γ : ℝ → C := fun s ↦ ι (a + s • v)
  let p : ℝ → ℂ := fun s ↦ b4cov_chart0 (f (γ s))
  have hseg (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      a + s • v ∈ segment ℝ a (a + v) := by
    rw [segment_eq_image']
    exact ⟨s, hs, by simp⟩
  have hγ : ∀ s ∈ Icc (0 : ℝ) 1, ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) 1 γ s := by
    intro s hs
    have H : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) 1 ι (a + s • v) :=
      (b3A_contMDiffWithinAt_real (hi _ (hseg s hs))).of_le le_top
    have hA : ContDiff ℝ 1 (fun s : ℝ ↦ a + s • v) :=
      contDiff_const.add (contDiff_id.smul contDiff_const)
    exact H.comp s (hA.contMDiff s)
  have hproj : ∀ s ∈ Icc (0 : ℝ) 1, f (γ s) = (p s : OnePoint ℂ) := by
    intro s hs
    obtain ⟨w, hw⟩ := OnePoint.ne_infty_iff_exists.mp (hfin _ (hseg s hs))
    change f (ι (a + s • v)) = (b4cov_chart0 (f (ι (a + s • v))) : OnePoint ℂ)
    rw [← hw, b4cov_chart0_coe]
  obtain ⟨σ, hd, hr, h0, h1, hg, hge, hpos⟩ := b6m_filling_analytic_reparam b t hb f k hk e he
    γ hγ p (b6m_analytic_segment_projection f hf a v ι hi hfin)
    (convex_Icc (0 : ℝ) 1).isPreconnected Subset.rfl hproj (fun s hs ↦ hkd _ (hseg s hs))
  refine ⟨σ, hd, hr, h0, h1, ?_, ?_, hpos⟩
  · simpa only [γ, Function.comp_def, zero_smul, one_smul, add_zero] using hg
  · simpa only [γ, Function.comp_def, zero_smul, one_smul, add_zero] using hge

end HodgeLean.Foundations.Program
