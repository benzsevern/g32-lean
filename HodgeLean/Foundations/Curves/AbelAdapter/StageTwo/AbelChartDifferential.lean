import HodgeLean.Foundations.Curves.AbelAdapter.StageTwo.CoverDifferential

/-! # Differential normalization of centered curve-chart coordinates

HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open HodgeLean.Foundations.Program
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Curves.AbelAdapter.StageTwo

/-- A centered scalar chart coordinate has exactly its specified linear covector at the center.
Source: Forster, §9; mfderiv_extChartAt_self.
HC no distance; AV milestone no distance. -/
theorem centeredChart_mfderiv
    {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
    (q : C) (κ : E →L[ℂ] ℂ) :
    mfderiv 𝓘(ℂ, E) 𝓘(ℂ, ℂ)
      (fun y : C ↦ κ (extChartAt 𝓘(ℂ, E) q y - extChartAt 𝓘(ℂ, E) q q)) q = κ := by
  have hφ := (contMDiffAt_extChartAt (I := 𝓘(ℂ, E)) (n := ω) (x := q)).mdifferentiableAt (by simp)
  have hδ := hφ.sub (mdifferentiableAt_const (c := extChartAt 𝓘(ℂ, E) q q))
  change mfderiv 𝓘(ℂ, E) 𝓘(ℂ, ℂ)
    (κ ∘ ((fun y : C ↦ extChartAt 𝓘(ℂ, E) q y) - (fun _ : C ↦ extChartAt 𝓘(ℂ, E) q q))) q = κ
  erw [mfderiv_comp q κ.mdifferentiableAt hδ, ContinuousLinearMap.mfderiv_eq,
    mfderiv_sub hφ mdifferentiableAt_const, mfderiv_extChartAt_self, mfderiv_const,
    sub_zero, ContinuousLinearMap.comp_id]

/-- A centered scalar chart coordinate has the prescribed covector as its actual differential.
Source: Forster, §9; centeredChart_mfderiv.
HC no distance; AV milestone no distance. -/
theorem centeredChart_hasMFDerivAt
    {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
    (q : C) (κ : E →L[ℂ] ℂ) :
    HasMFDerivAt 𝓘(ℂ, E) 𝓘(ℂ, ℂ)
      (fun y : C ↦ κ (extChartAt 𝓘(ℂ, E) q y - extChartAt 𝓘(ℂ, E) q q)) q κ := by
  have hφ := (contMDiffAt_extChartAt (I := 𝓘(ℂ, E)) (n := ω) (x := q)).mdifferentiableAt (by simp)
  have hδ := hφ.sub (mdifferentiableAt_const (c := extChartAt 𝓘(ℂ, E) q q))
  have hh : HasMFDerivAt 𝓘(ℂ, E) 𝓘(ℂ, ℂ)
      (fun y : C ↦ κ (extChartAt 𝓘(ℂ, E) q y - extChartAt 𝓘(ℂ, E) q q)) q
      (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, ℂ)
        (fun y : C ↦ κ (extChartAt 𝓘(ℂ, E) q y - extChartAt 𝓘(ℂ, E) q q)) q) :=
    (κ.mdifferentiableAt.comp q hδ).hasMFDerivAt
  exact (congrArg (fun L : E →L[ℂ] ℂ ↦
    HasMFDerivAt 𝓘(ℂ, E) 𝓘(ℂ, ℂ)
      (fun y : C ↦ κ (extChartAt 𝓘(ℂ, E) q y - extChartAt 𝓘(ℂ, E) q q)) q L)
        (centeredChart_mfderiv q κ)).mp hh

#print axioms centeredChart_mfderiv
#print axioms centeredChart_hasMFDerivAt

end HodgeLean.Foundations.Curves.AbelAdapter.StageTwo
