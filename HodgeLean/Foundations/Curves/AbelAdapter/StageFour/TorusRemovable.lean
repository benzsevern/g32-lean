import HodgeLean.Foundations.Curves.AbelAdapter.StageFour.TorusLocalLift
import Mathlib.Analysis.Complex.RemovableSingularity

noncomputable section
open HodgeLean.Foundations.Program Filter
open scoped TensorProduct Manifold ContDiff Topology
namespace HodgeLean.Foundations.Curves.AbelAdapter.StageFour

/-- Source: Forster, Lectures on Riemann Surfaces, §6, removable singularities in local charts. -/
theorem torus_holomorphicAt_of_punctured
    {L : Type} [AddCommGroup L] [Module.Finite ℤ L]
    (F : Submodule ℂ (ℂ ⊗[ℤ] L))
    [DiscreteTopology (b2_latticeMap L F).range]
    (f : ℂ → b2_torus L F) (q : ℂ) (hc : ContinuousAt f q)
    (hh : ∀ᶠ z in 𝓝[≠] q, ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, b5_V L F) ω f z) :
    ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, b5_V L F) ω f q := by
  letI := b2_torus_isManifold F
  let g : ℂ → b5_V L F := fun z ↦ chartAt (b5_V L F) (f q) (f z)
  have hchart : ContMDiffAt 𝓘(ℂ, b5_V L F) 𝓘(ℂ, b5_V L F) ω
      (chartAt (b5_V L F) (f q)) (f q) := by
    simpa only [extChartAt_coe, modelWithCornersSelf_coe, Function.id_comp] using
      (contMDiffAt_extChartAt (I := 𝓘(ℂ, b5_V L F)) (n := ω) (x := f q))
  have hsource := hc.eventually (chart_source_mem_nhds (b5_V L F) (f q))
  have hgd : ∀ᶠ z in 𝓝[≠] q, DifferentiableAt ℂ g z := by
    filter_upwards [hh, hsource.filter_mono nhdsWithin_le_nhds] with z hz hs
    have hcz : ContMDiffAt 𝓘(ℂ, b5_V L F) 𝓘(ℂ, b5_V L F) ω
        (chartAt (b5_V L F) (f q)) (f z) := by
      simpa only [extChartAt_coe, modelWithCornersSelf_coe, Function.id_comp] using
        (contMDiffAt_extChartAt' (I := 𝓘(ℂ, b5_V L F)) (n := ω) hs)
    exact (hcz.comp z hz).contDiffAt.differentiableAt (by simp)
  have hga : AnalyticAt ℂ g q :=
    Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hgd
      (hchart.continuousAt.comp hc)
  have he : f =ᶠ[𝓝 q] (fun z ↦ b2_torusCover L F (g z)) := by
    filter_upwards [hsource] with z hz
    exact ((chartAt (b5_V L F) (f q)).left_inv hz).symm.trans
      (b2t_torusChart_symm_apply F (f q) (g z))
  exact ((b2_torusCover_contMDiff F).contMDiffAt.comp q
    hga.contDiffAt.contMDiffAt).congr_of_eventuallyEq he


/-- Source: Forster, Lectures on Riemann Surfaces, §6, removable singularities in local charts. -/
theorem torus_holomorphicAt_of_punctured_manifold
    {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
    {L : Type} [AddCommGroup L] [Module.Finite ℤ L]
    (F : Submodule ℂ (ℂ ⊗[ℤ] L))
    [DiscreteTopology (b2_latticeMap L F).range]
    (f : C → b2_torus L F) (q : C) (hc : ContinuousAt f q)
    (hh : ∀ᶠ z in 𝓝[≠] q, ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, b5_V L F) ω f z) :
    ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, b5_V L F) ω f q := by
  let e := chartAt ℂ q
  have hq : q ∈ e.source := mem_chart_source ℂ q
  have ht : e q ∈ e.target := e.map_source hq
  have heq : e.symm (e q) = q := e.left_inv hq
  have hr : Tendsto e.symm (𝓝 (e q)) (𝓝 q) := by
    simpa only [heq] using (e.symm.continuousAt ht).tendsto
  have htarget : ∀ᶠ t in 𝓝 (e q), t ∈ e.target := e.open_target.mem_nhds ht
  have hp : Tendsto e.symm (𝓝[≠] (e q)) (𝓝[≠] q) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨hr.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [htarget.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with t htar hne
    change e.symm t ≠ q
    intro he
    have hte : t = e q := (e.right_inv htar).symm.trans (congrArg e he)
    exact hne hte
  have hsymm : ∀ t ∈ e.target,
      ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω e.symm t := by
    intro t htar
    have htar' : t ∈ (extChartAt 𝓘(ℂ, ℂ) q).target := by
      simpa [e, extChartAt_target] using htar
    have hs := (contMDiffOn_extChartAt_symm (I := 𝓘(ℂ, ℂ)) (n := ω) q t htar').contMDiffAt
      ((isOpen_extChartAt_target (I := 𝓘(ℂ, ℂ)) q).mem_nhds htar')
    simpa only [extChartAt_coe_symm, modelWithCornersSelf_coe_symm, Function.comp_id] using hs
  have hkc : ContinuousAt (f ∘ e.symm) (e q) := by
    change Tendsto (f ∘ e.symm) (𝓝 (e q)) (𝓝 (f (e.symm (e q))))
    rw [heq]
    exact hc.tendsto.comp hr
  have hkh : ∀ᶠ t in 𝓝[≠] (e q),
      ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, b5_V L F) ω (f ∘ e.symm) t := by
    filter_upwards [hp.eventually hh,
      htarget.filter_mono nhdsWithin_le_nhds] with t hf htar
    exact hf.comp t (hsymm t htar)
  have hk := torus_holomorphicAt_of_punctured F (f ∘ e.symm) (e q) hkc hkh
  have he : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω e q := by
    simpa only [extChartAt_coe, modelWithCornersSelf_coe, Function.id_comp] using
      (contMDiffAt_extChartAt (I := 𝓘(ℂ, ℂ)) (n := ω) (x := q))
  apply (hk.comp q he).congr_of_eventuallyEq
  filter_upwards [e.open_source.mem_nhds hq] with z hz
  exact (congrArg f (e.left_inv hz)).symm



/-- Source: Forster, Lectures on Riemann Surfaces, §6, removable singularities in local charts. -/
theorem torus_holomorphic_of_finite_exceptional
    {C : Type} [TopologicalSpace C] [T1Space C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C]
    {L : Type} [AddCommGroup L] [Module.Finite ℤ L]
    (F : Submodule ℂ (ℂ ⊗[ℤ] L))
    [DiscreteTopology (b2_latticeMap L F).range]
    (f : C → b2_torus L F) (hc : Continuous f)
    (S : Set C) (hS : S.Finite)
    (hh : ∀ z ∉ S, ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, b5_V L F) ω f z) :
    ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, b5_V L F) ω f := by
  intro q
  apply torus_holomorphicAt_of_punctured_manifold F f q hc.continuousAt
  have hfin : (S \ {q}).Finite := hS.diff
  have hn : ∀ᶠ z in 𝓝 q, z ∉ S \ {q} :=
    hfin.isClosed.isOpen_compl.mem_nhds (by simp)
  filter_upwards [hn.filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with z hz hne
  apply hh z
  intro hzs
  exact hz ⟨hzs, hne⟩


end HodgeLean.Foundations.Curves.AbelAdapter.StageFour
