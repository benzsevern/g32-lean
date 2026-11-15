import HodgeLean.Foundations.TubularEuler.NormalGeometryInputs
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! # Operators of the supplied metric in Hilbert coordinates

A fixed linear coordinate equivalence transports the original bilinear
coefficients before Riesz duality turns them into metric operators.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open Topology
namespace HodgeLean.Foundations.TubularEuler

variable {M E : Type*} [TopologicalSpace M] {d : ℕ} [ChartedSpace (Fin d → ℂ) M]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def chartMetricOperator (g : ChartHermitianMetric M d) (L : E ≃L[ℝ] (Fin d → ℂ))
    (z : M) (a : E) : E →L[ℝ] E :=
  InnerProductSpace.continuousLinearMapOfBilin
    ((g.coefficient z (L a)).bilinearComp L.toContinuousLinearMap L.toContinuousLinearMap)

theorem chartMetricOperator_inner (g : ChartHermitianMetric M d)
    (L : E ≃L[ℝ] (Fin d → ℂ)) (z : M) (a u w : E) :
    inner ℝ (chartMetricOperator g L z a u) w =
      g.coefficient z (L a) (L u) (L w) := by
  exact InnerProductSpace.continuousLinearMapOfBilin_apply _ u w

theorem chartMetricOperator_positive (g : ChartHermitianMetric M d)
    (L : E ≃L[ℝ] (Fin d → ℂ)) (z : M) (a : E)
    (ha : L a ∈ (chartAt (Fin d → ℂ) z).target) (u : E) (hu : u ≠ 0) :
    0 < inner ℝ (chartMetricOperator g L z a u) u := by
  rw [chartMetricOperator_inner]
  exact g.positive z (L a) ha (L u) (fun h => hu (L.injective (h.trans (map_zero L).symm)))

theorem chartMetricOperator_symmetric (g : ChartHermitianMetric M d)
    (L : E ≃L[ℝ] (Fin d → ℂ)) (z : M) (a : E)
    (ha : L a ∈ (chartAt (Fin d → ℂ) z).target) (u w : E) :
    inner ℝ (chartMetricOperator g L z a u) w =
      inner ℝ u (chartMetricOperator g L z a w) := by
  calc
    inner ℝ (chartMetricOperator g L z a u) w = g.coefficient z (L a) (L u) (L w) :=
      chartMetricOperator_inner g L z a u w
    _ = g.coefficient z (L a) (L w) (L u) := g.symmetric z (L a) ha (L u) (L w)
    _ = inner ℝ (chartMetricOperator g L z a w) u := (chartMetricOperator_inner g L z a w u).symm
    _ = inner ℝ u (chartMetricOperator g L z a w) := real_inner_comm _ _

theorem chartMetricOperator_contDiffOn (g : ChartHermitianMetric M d)
    (L : E ≃L[ℝ] (Fin d → ℂ)) (z : M) :
    ContDiffOn ℝ ⊤ (chartMetricOperator g L z)
      (L ⁻¹' (chartAt (Fin d → ℂ) z).target) := by
  have hbase : ContDiffOn ℝ ⊤ (fun a : E => g.coefficient z (L a))
      (L ⁻¹' (chartAt (Fin d → ℂ) z).target) :=
    (g.smooth z).comp L.contDiff.contDiffOn (fun _ ha => ha)
  let flip₁ := (ContinuousLinearMap.flipₗᵢ ℝ E (Fin d → ℂ) ℝ).toContinuousLinearEquiv.toContinuousLinearMap
  let flip₂ := (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).toContinuousLinearEquiv.toContinuousLinearMap
  let Riesz := (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have h₁ := hbase.clm_comp (contDiffOn_const (c := L.toContinuousLinearMap))
  have h₂ := flip₁.contDiff.comp_contDiffOn h₁
  have h₃ := h₂.clm_comp (contDiffOn_const (c := L.toContinuousLinearMap))
  have h₄ := flip₂.contDiff.comp_contDiffOn h₃
  exact (contDiffOn_const (c := Riesz)).clm_comp h₄

#print axioms chartMetricOperator_contDiffOn

#print axioms chartMetricOperator_symmetric

#print axioms chartMetricOperator_positive

#print axioms chartMetricOperator
#print axioms chartMetricOperator_inner

end HodgeLean.Foundations.TubularEuler
