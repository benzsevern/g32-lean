import HodgeLean.Foundations.Curves.AbelTheorem.ThirdKindCorrection

noncomputable section
open HodgeLean.Foundations.Program
open HodgeLean.Foundations.Curves.AbelAdapter.StageFour
open Module Manifold
open scoped ContDiff BigOperators
namespace HodgeLean.Foundations.Curves.AbelTheorem
set_option maxHeartbeats 400000
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace C] [ChartedSpace E C]
  [IsManifold 𝓘(ℂ, E) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]

theorem loop_integral_sub_holomorphic (h : finrank ℂ E = 1)
    (D : C →₀ ℤ) (w : b4c_MeroForm E C h) (u : b3_HolForm E C)
    (ha : ∀ x, x ∉ D.support → AnalyticAt ℂ (HurwitzPrymRR_loc h w x) 0)
    (γ : b3_SmoothLoop E C) (hav : ∀ t, γ.val t ∉ D.support) :
    loopIntegral γ ((w : TangentBundle 𝓘(ℂ, E) C → ℂ) -
        (u : TangentBundle 𝓘(ℂ, E) C → ℂ)) = loopIntegral γ w - loopIntegral γ u := by
  unfold loopIntegral b3_pathIntegral
  exact intervalIntegral.integral_sub
    ((continuous_integrand_off_support h D w ha γ.val γ.property.2 hav).intervalIntegrable 0 1)
    ((b3A_continuous_integrand γ.val γ.property.2 u).intervalIntegrable 0 1)

end HodgeLean.Foundations.Curves.AbelTheorem
