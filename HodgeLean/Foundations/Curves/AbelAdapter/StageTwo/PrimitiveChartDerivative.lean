import HodgeLean.Foundations.Curves.AbelAdapter.StageTwo.AbelChartDifferential

/-! # Exact scalar derivatives of normalized local Abel primitives

HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open HodgeLean.Foundations.Program
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Curves.AbelAdapter.StageTwo

/-- The primitive of a basis form retains its specified derivative in centered chart coordinates.
Source: Forster, §§9–10; HasMFDerivAt.comp and centeredChart_hasMFDerivAt.
HC no distance; AV milestone no distance. -/
theorem primitive_centeredChart_mfderiv
    {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
    (q : C) (κ : E →L[ℂ] ℂ) (G : ℂ → ℂ) (a c : ℂ) (hG : HasDerivAt G a 0) (v : E) :
    mfderiv 𝓘(ℂ, E) 𝓘(ℂ, ℂ)
      (fun y : C ↦ c + (G (κ (extChartAt 𝓘(ℂ, E) q y - extChartAt 𝓘(ℂ, E) q q)) - G 0)) q v =
      a * κ v := by
  let ζ : C → ℂ := fun y ↦ κ (extChartAt 𝓘(ℂ, E) q y - extChartAt 𝓘(ℂ, E) q q)
  have hζ0 : ζ q = 0 := by simp only [ζ, sub_self, map_zero]
  have hz : HasMFDerivAt 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ζ q κ := centeredChart_hasMFDerivAt q κ
  have hGm : HasMFDerivAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) G (ζ q)
      (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℂ ℂ) a) := by
    rw [hζ0]
    exact hG.hasFDerivAt.hasMFDerivAt
  have h0 := (hasMFDerivAt_const (I := 𝓘(ℂ, E)) (I' := 𝓘(ℂ, ℂ)) c q).add
    ((hGm.comp q hz).sub (hasMFDerivAt_const (I := 𝓘(ℂ, E)) (I' := 𝓘(ℂ, ℂ)) (G 0) q))
  have hh := congrArg (fun L : E →L[ℂ] ℂ ↦ L v) h0.mfderiv
  simp only [zero_add, sub_zero] at hh
  change mfderiv 𝓘(ℂ, E) 𝓘(ℂ, ℂ) (fun y : C ↦ c + (G (ζ y) - G 0)) q v = κ v • a at hh
  have hm : (κ v : ℂ) • a = a * κ v := by rw [smul_eq_mul, mul_comm]
  exact hh.trans hm

#print axioms primitive_centeredChart_mfderiv

end HodgeLean.Foundations.Curves.AbelAdapter.StageTwo
