import HodgeLean.Foundations.Curves.AbelAdapter.StageTwo.AbelChartDifferential

/-! # Literal tangent normalization at the center of a curve disc

HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
open HodgeLean.Foundations.Program
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Curves.AbelAdapter.StageTwo

/-- At the disc center, its form coefficient is the original tangent value on the chosen vector.
Source: Forster, §9; TangentBundle.symmL_trivializationAt.
HC no distance; AV milestone no distance. -/
theorem discCoef_zero
    {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
    (θ : TangentBundle 𝓘(ℂ, E) C → ℂ) (q : C) (u : E) :
    b3A_discCoef θ q u 0 = θ ⟨q, u⟩ := by
  unfold b3A_discCoef b3A_disc b3A_coef
  rw [zero_smul, add_zero, (chartAt E q).left_inv (mem_chart_source E q)]
  change θ ⟨q, (trivializationAt E (TangentSpace 𝓘(ℂ, E)) q).symmL ℂ q u⟩ = _
  rw [TangentBundle.symmL_trivializationAt (mem_chart_source E q),
    mfderivWithin_range_extChartAt_symm]
  rfl

#print axioms discCoef_zero

end HodgeLean.Foundations.Curves.AbelAdapter.StageTwo
