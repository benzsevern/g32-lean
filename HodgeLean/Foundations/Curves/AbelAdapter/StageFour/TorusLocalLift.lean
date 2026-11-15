import HodgeLean.Foundations.Curves.AbelAdapter.StageTwo.CoverDifferential

noncomputable section
open HodgeLean.Foundations.Program HodgeLean.Foundations.Curves.AbelAdapter.StageTwo
open Filter
open scoped TensorProduct Manifold ContDiff Topology
namespace HodgeLean.Foundations.Curves.AbelAdapter.StageFour

theorem torus_localLift {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace C] [ChartedSpace E C]
    {L : Type} [AddCommGroup L] [Module.Finite ℤ L]
    (F : Submodule ℂ (ℂ ⊗[ℤ] L))
    [DiscreteTopology (b2_latticeMap L F).range]
    (f : C → b2_torus L F) (q : C)
    (hf : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, b5_V L F) ω f q) :
    ∃ g : C → b5_V L F,
      ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, b5_V L F) ω g q ∧
      f =ᶠ[𝓝 q] b2_torusCover L F ∘ g := by
  let g : C → b5_V L F := fun x ↦ chartAt (b5_V L F) (f q) (f x)
  have hc : ContMDiffAt 𝓘(ℂ, b5_V L F) 𝓘(ℂ, b5_V L F) ω
      (chartAt (b5_V L F) (f q)) (f q) := by
    simpa only [extChartAt_coe, modelWithCornersSelf_coe, Function.id_comp] using
      (contMDiffAt_extChartAt (I := 𝓘(ℂ, b5_V L F)) (n := ω) (x := f q))
  refine ⟨g, hc.comp q hf, ?_⟩
  filter_upwards [hf.continuousAt.eventually (chart_source_mem_nhds (b5_V L F) (f q))] with x hx
  exact ((chartAt (b5_V L F) (f q)).left_inv hx).symm.trans
    (b2t_torusChart_symm_apply F (f q) (g x))

end HodgeLean.Foundations.Curves.AbelAdapter.StageFour
