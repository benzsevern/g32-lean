import HodgeLean.Foundations.Program.HurwitzPrymCovDegree

noncomputable section
set_option maxHeartbeats 400000
open Manifold Set
open scoped ContDiff
namespace HodgeLean.Foundations.Program

/-- The normalized chart germ of an action has its tangent multiplier as derivative. -/
theorem s0_action_chart_multiplier
    {C H : Type} [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
    [Group H] [MulAction H C]
    (hH : ∀ h : H, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun z : C ↦ h • z))
    (x : C) (h : H) :
    deriv (b4cov_transport (Module.finrank_self ℂ) (Module.finrank_self ℂ)
      (writtenInExtChartAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) x (fun z : C ↦ h • z))
      (extChartAt 𝓘(ℂ, ℂ) x x)) 0 = b4cov_lam (Module.finrank_self ℂ) x h := by
  have han := b4cov_analyticOnNhd (fun z : C ↦ h • z) (hH h) x
    (extChartAt 𝓘(ℂ, ℂ) x x) (b4cov_mem_good (fun z : C ↦ h • z) x)
  have hd := b4cov_transport_deriv (Module.finrank_self ℂ) (Module.finrank_self ℂ)
    (0 : ℂ) (by simpa only [map_zero, add_zero] using han.differentiableAt)
  have hab := ((hH h x).mdifferentiableAt (by simp)).mfderiv_abuse
  rw [modelWithCornersSelf_coe, Set.range_id, fderivWithin_univ] at hab
  simp only [map_zero, add_zero] at hd
  rw [← hab] at hd
  exact hd

#print axioms s0_action_chart_multiplier
end HodgeLean.Foundations.Program
