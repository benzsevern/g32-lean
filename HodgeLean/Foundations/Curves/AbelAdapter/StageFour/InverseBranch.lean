import HodgeLean.Foundations.Program.HurwitzPrymCovDescent

noncomputable section
open HodgeLean.Foundations.Program Filter Set
open scoped Manifold ContDiff Topology
namespace HodgeLean.Foundations.Curves.AbelAdapter.StageFour

/-- Source: Forster, Lectures on Riemann Surfaces, §2, the holomorphic inverse function theorem. -/
theorem holomorphic_inverse_branch
    {E E' C Y : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup E'] [NormedSpace ℂ E']
    [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
    [TopologicalSpace Y] [ChartedSpace E' Y] [IsManifold 𝓘(ℂ, E') ω Y]
    (hE : Module.finrank ℂ E = 1) (hE' : Module.finrank ℂ E' = 1)
    (f : C → Y) (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω f)
    (q : C) (hd : mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E') f q ≠ 0) :
    ∃ r : Y → C, r (f q) = q ∧ ContMDiffAt 𝓘(ℂ, E') 𝓘(ℂ, E) ω r (f q) ∧
      (∀ᶠ y in 𝓝 (f q), f (r y) = y) ∧ (∀ᶠ x in 𝓝 q, r (f x) = x) := by
  haveI : FiniteDimensional ℂ E := Module.finite_of_finrank_eq_succ hE
  haveI : FiniteDimensional ℂ E' := Module.finite_of_finrank_eq_succ hE'
  haveI := FiniteDimensional.complete ℂ E
  haveI := FiniteDimensional.complete ℂ E'
  let φ := extChartAt 𝓘(ℂ, E) q
  let ψ := extChartAt 𝓘(ℂ, E') (f q)
  let G := b4cov_expr E E' f q (f q)
  let t := φ q
  have hq : q ∈ φ.source := mem_extChartAt_source q
  have hψ : f q ∈ ψ.source := mem_extChartAt_source (f q)
  have hGt : G t = ψ (f q) := by
    change ψ (f (φ.symm (φ q))) = ψ (f q)
    rw [φ.left_inv hq]
  have hGan : AnalyticAt ℂ G t :=
    b4cov_analyticAt_chart f hf q (f q) t (φ.map_source hq)
      (by rw [φ.left_inv hq]; exact hψ)
  have hGd : fderiv ℂ G t ≠ 0 :=
    (b4cov_mfderiv_ne_zero_iff_expr f hf q (f q) q hq hψ).1 hd
  obtain ⟨σ, hσ, hσt, hGσ, hσG⟩ := b4cov_exists_localInverse hE hE' hGan hGd
  have hσq : σ (ψ (f q)) = t := hGt ▸ hσt
  have hσan : AnalyticAt ℂ σ (ψ (f q)) := hGt ▸ hσ
  let r : Y → C := fun y ↦ φ.symm (σ (ψ y))
  have hrq : r (f q) = q := by
    change φ.symm (σ (ψ (f q))) = q
    rw [hσq]
    exact φ.left_inv hq
  have hφsym : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, E) ω φ.symm t :=
    (contMDiffWithinAt_extChartAt_symm_target_self (I := 𝓘(ℂ, E)) (n := ω) q).contMDiffAt
      ((isOpen_extChartAt_target (I := 𝓘(ℂ, E)) q).mem_nhds (φ.map_source hq))
  have hφσ : ContMDiffAt 𝓘(ℂ, E') 𝓘(ℂ, E) ω (fun z ↦ φ.symm (σ z)) (ψ (f q)) := by
    have hφσq : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, E) ω φ.symm (σ (ψ (f q))) := by
      rw [hσq]
      exact hφsym
    exact hφσq.comp _ hσan.contDiffAt.contMDiffAt
  have hr : ContMDiffAt 𝓘(ℂ, E') 𝓘(ℂ, E) ω r (f q) :=
    hφσ.comp _ (contMDiffAt_extChartAt (I := 𝓘(ℂ, E')) (n := ω) (x := f q))
  refine ⟨r, hrq, hr, ?_, ?_⟩
  · have hψc := (contMDiffAt_extChartAt (I := 𝓘(ℂ, E')) (n := ω) (x := f q)).continuousAt
    have he : ∀ᶠ z in 𝓝 (ψ (f q)), G (σ z) = z := hGt ▸ hGσ
    have hi : ∀ᶠ y in 𝓝 (f q), f (r y) ∈ ψ.source := by
      have hc : ContinuousAt (fun y ↦ f (r y)) (f q) := hf.continuous.continuousAt.comp hr.continuousAt
      have hm : ψ.source ∈ 𝓝 (f (r (f q))) := by rw [hrq]; exact extChartAt_source_mem_nhds _
      exact hc.eventually hm
    filter_upwards [hψc.tendsto.eventually he, hi, extChartAt_source_mem_nhds (I := 𝓘(ℂ, E')) (f q)] with y heq hy hys
    apply ψ.injOn hy hys
    exact heq
  · have hφc := (contMDiffAt_extChartAt (I := 𝓘(ℂ, E)) (n := ω) (x := q)).continuousAt
    have he := hφc.tendsto.eventually hσG
    filter_upwards [he, extChartAt_source_mem_nhds (I := 𝓘(ℂ, E)) q] with x hx hxs
    have hGφ : G (φ x) = ψ (f x) := by
      change ψ (f (φ.symm (φ x))) = ψ (f x)
      rw [φ.left_inv hxs]
    change φ.symm (σ (ψ (f x))) = x
    exact (congrArg φ.symm ((congrArg σ hGφ).symm.trans hx)).trans (φ.left_inv hxs)

end HodgeLean.Foundations.Curves.AbelAdapter.StageFour
