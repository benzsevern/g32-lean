import HodgeLean.Foundations.Program.CurveJacobian

noncomputable section
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Program

/-- Translating an Abel–Jacobi map by its value at a point changes its basepoint to that point. -/
theorem s0_abelJacobi_rebase
    {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
    (p₀ p₁ : C) (aj : C → b3_Jacobian E C) (h : b3_IsAbelJacobi E C p₀ aj) :
    b3_IsAbelJacobi E C p₁ (fun p ↦ aj p - aj p₁) := by
  refine ⟨sub_self _, ?_⟩
  intro γ hγ
  obtain ⟨v, hv, he⟩ := h.2 γ hγ
  refine ⟨v, hv, ?_⟩
  calc
    (aj (γ 1) - aj p₁) - (aj (γ 0) - aj p₁) = aj (γ 1) - aj (γ 0) := by abel
    _ = _ := he

#print axioms s0_abelJacobi_rebase
end HodgeLean.Foundations.Program
