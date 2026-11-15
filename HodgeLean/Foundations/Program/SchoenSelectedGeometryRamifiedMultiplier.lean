import HodgeLean.Foundations.Program.SchoenSelectedGeometryCenteredComposition
import HodgeLean.Foundations.Program.SchoenSelectedGeometryCenteredOrder
import HodgeLean.Foundations.Program.SchoenSelectedGeometryChartMultiplier
import HodgeLean.Foundations.Program.SchoenSelectedGeometryLeadingAction

noncomputable section
set_option maxHeartbeats 400000
open Manifold Filter Topology
open scoped ContDiff
namespace HodgeLean.Foundations.Program

/-- Ramification raises tangent multipliers to the local degree under an equivariant map. -/
theorem s0_ramified_action_multiplier
    {C Y H K : Type}
    [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C] [ConnectedSpace C]
    [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ, ℂ) ω Y]
    [Group H] [MulAction H C] [Group K] [MulAction K Y]
    (hH : ∀ h : H, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun z : C ↦ h • z))
    (hK : ∀ k : K, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun z : Y ↦ k • z))
    (f : C → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f)
    (hnc : ∃ x x', f x ≠ f x') (x : C) (h : H) (k : K)
    (hx : h • x = x) (he : ∀ z, f (h • z) = k • f z) :
    b4cov_lam (Module.finrank_self ℂ) (f x) k =
      b4cov_lam (Module.finrank_self ℂ) x h ^ b4_ramIndex ℂ ℂ f x := by
  have heq : f ∘ (fun z : C ↦ h • z) = (fun z : Y ↦ k • z) ∘ f := funext he
  have h₁ := s0_centeredChartMap_comp (fun z : C ↦ h • z) f (hH h).continuous x
  rw [hx, heq] at h₁
  have h₂ := s0_centeredChartMap_comp f (fun z : Y ↦ k • z) hf.continuous x
  have hgerm := h₁.symm.trans h₂
  have hd := s0_analytic_leading_equivariance
    (s0_centeredChartMap_analytic f hf x)
    (s0_centeredChartMap_analytic (fun z : C ↦ h • z) (hH h) x)
    (s0_centeredChartMap_analytic (fun z : Y ↦ k • z) (hK k) (f x))
    (b4cov_transport_zero _ _ _ _) (b4cov_transport_zero _ _ _ _)
    (b4cov_transport_zero _ _ _ _) (s0_centeredChartMap_order f hf hnc x) hgerm
  unfold s0_centeredChartMap at hd
  rw [s0_action_chart_multiplier hK, s0_action_chart_multiplier hH] at hd
  exact hd

#print axioms s0_ramified_action_multiplier
end HodgeLean.Foundations.Program
