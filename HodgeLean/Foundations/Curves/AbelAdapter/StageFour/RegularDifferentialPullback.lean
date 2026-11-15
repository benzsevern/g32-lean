import HodgeLean.Foundations.Program.RiemannRoch

noncomputable section
open HodgeLean.Foundations.Program
open Manifold Filter Topology
open scoped ContDiff
namespace HodgeLean.Foundations.Curves.AbelAdapter.StageFour

/-- Source: Forster, Lectures on Riemann Surfaces, §§9, 14, holomorphic pullback away from poles. -/
theorem differential_pullback_holomorphic_on_regular_image
    {E E' C Y : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup E'] [NormedSpace ℂ E']
    [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
    [TopologicalSpace Y] [ChartedSpace E' Y] [IsManifold 𝓘(ℂ, E') ω Y]
    (h : Module.finrank ℂ E = 1) (h' : Module.finrank ℂ E' = 1)
    (f : C → Y) (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω f)
    (θ : TangentBundle 𝓘(ℂ, E') Y → ℂ) (hθ : HurwitzPrymRR_IsLinear θ)
    (ha : ∀ x, AnalyticAt ℂ (HurwitzPrymRR_loc h' θ (f x)) 0) :
    b3_pullback E E' f θ ∈ b3_HolForm E C := by
  apply RiemannRochEichler_holForm_of_loc_analytic h
  · intro x a v w
    change θ ⟨f x, mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E') f x (a • v + w)⟩ = _
    rw [map_add, map_smul]
    exact hθ (f x) a _ _
  · intro x
    letI : FiniteDimensional ℂ E' := Module.finite_of_finrank_eq_succ h'
    letI : CompleteSpace E' := FiniteDimensional.complete ℂ E'
    let T := b4cov_transport h h' (b4cov_expr E E' f x (f x))
      (extChartAt 𝓘(ℂ, E) x x)
    have hG := b4cov_analyticAt_chart f hf x (f x)
      (extChartAt 𝓘(ℂ, E) x x) (mem_extChartAt_target x) (by
        rw [extChartAt_to_inv]; exact mem_extChartAt_source (f x))
    have hT : AnalyticAt ℂ T 0 := b4cov_transport_analyticAt h h' hG
    have hT0 : T 0 = 0 := b4cov_transport_zero h h' _ _
    have ha' : AnalyticAt ℂ (HurwitzPrymRR_loc h' θ (f x)) (T 0) := by
      rw [hT0]; exact ha x
    have hp := (ha'.comp hT).mul hT.deriv
    apply hp.congr
    have he := HurwitzPrymRR_loc_pullback h h' f hf x (f x)
      (mem_extChartAt_source (f x)) θ hθ
    filter_upwards [he] with t ht
    simpa only [T, Pi.mul_apply, Function.comp_apply, sub_self, map_zero, zero_add] using ht.symm

end HodgeLean.Foundations.Curves.AbelAdapter.StageFour
