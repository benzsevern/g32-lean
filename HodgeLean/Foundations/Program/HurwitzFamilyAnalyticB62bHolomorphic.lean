import HodgeLean.Foundations.Program.HurwitzFamilyAnalyticDefs

noncomputable section

open scoped Manifold ContDiff
open Manifold

namespace HodgeLean.Foundations.Program

attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

theorem b6a_value_power_contMDiff (j : Fin 13) (e : ℕ) :
    ContMDiff 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) 𝓘(ℂ, ℂ) ω
      (fun q : (Fin 10 → ℂ) × ℂ ↦ b6a_value q.1 j (q.2 ^ e)) := by
  unfold b6a_value
  split_ifs with hj hj0 hj1
  · apply b4cov_coe_contMDiff.comp
    apply ContDiff.contMDiff
    fun_prop
  · apply b4cov_coe_contMDiff.comp
    apply ContDiff.contMDiff
    fun_prop
  · apply b4cov_coe_contMDiff.comp
    apply ContDiff.contMDiff
    fun_prop
  · have hinf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω b4cov_chartInf.symm := by
      intro z
      apply contMDiffAt_symm_of_mem_maximalAtlas
        (IsManifold.subset_maximalAtlas (by
          change b4cov_chartInf ∈ ({b4cov_chart0, b4cov_chartInf} : Set _)
          simp))
      change z ∈ b4cov_chartInf.target
      simp [b4cov_chartInf, b4cov_chart0_target]
    have hp : ContDiff ℂ ω (fun q : (Fin 10 → ℂ) × ℂ ↦ q.2 ^ e) := by fun_prop
    simpa only [Function.comp_def, b4cov_chartInf_symm] using hinf.comp hp.contMDiff

theorem b6a_map_contMDiff_of_local_formulas (b : Fin 10 → ℂ) (C : Type)
    [TopologicalSpace C]
    [ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)]
    [IsManifold 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω (b6t_polydisc b × C)]
    (f : C → OnePoint ℂ) (n : C → ℕ)
    (A : (b6t_polydisc b × C) →
      OpenPartialHomeomorph (b6t_polydisc b × C) ((Fin 10 → ℂ) × ℂ))
    (hA : ∀ q, q ∈ (A q).source ∧
      A q ∈ atlas ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C))
    (hparam : ∀ q y, y ∈ (A q).source → (A q y).1 = y.1.val)
    (hfree : ∀ q, f q.2 ∉ Set.range (b6_branch b) →
      ∀ y ∈ (A q).source, b6a_map b f y = ((A q y).2 : OnePoint ℂ))
    (hmark : ∀ q (j : Fin 13), f q.2 = b6_branch b j →
      ∀ y ∈ (A q).source,
        b6a_map b f y = b6a_value y.1.val j ((A q y).2 ^ n q.2)) :
    ContMDiff 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) 𝓘(ℂ, ℂ) ω (b6a_map b f) := by
  intro q
  have hchart : ContMDiffAt 𝓘(ℂ, (Fin 10 → ℂ) × ℂ)
      𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω (A q) q :=
    contMDiffAt_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas (hA q).2) (hA q).1
  by_cases hq : f q.2 ∈ Set.range (b6_branch b)
  · obtain ⟨j, hj⟩ := hq
    apply ((b6a_value_power_contMDiff j (n q.2)).contMDiffAt.comp q hchart).congr_of_eventuallyEq
    filter_upwards [(A q).open_source.mem_nhds (hA q).1] with y hy
    simpa only [Function.comp_apply, hparam q y hy] using hmark q j hj.symm y hy
  · have hsnd : ContDiff ℂ ω (fun z : (Fin 10 → ℂ) × ℂ ↦ z.2) := contDiff_snd
    apply ((b4cov_coe_contMDiff.comp hsnd.contMDiff).contMDiffAt.comp q hchart).congr_of_eventuallyEq
    filter_upwards [(A q).open_source.mem_nhds (hA q).1] with y hy
    exact hfree q hq y hy

end HodgeLean.Foundations.Program
