import HodgeLean.Foundations.IntegralHomology.StageTwo.BarycentricPoint
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbPrismCoordinates
import Mathlib.Analysis.Normed.Module.Basic

/-! Barycentric distributions parametrize finite convex hulls continuously.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open Convexity
namespace HodgeLean.Foundations.IntegralHomology.StageTwo

theorem barycentricPoint_range {I E : Type} [Fintype I] [AddCommGroup E] [Module ℝ E]
    (v : I → E) : Set.range (barycentricPoint v) = convexHull ℝ (Set.range v) := by
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    exact barycentricPoint_mem_convexHull v p _ (fun i => Set.mem_range_self i)
  · intro hx
    obtain ⟨w, hw⟩ :=
      (HodgeLean.Foundations.Program.s2v_hardt6rb_convexHull_range_weights v x).mp hx
    let p : StdSimplex ℝ I := {
      weights := Finsupp.equivFunOnFinite.symm w.val
      nonneg := fun i => by simpa using w.property.1 i
      total := by simpa [Finsupp.sum_fintype] using w.property.2 }
    refine ⟨p, ?_⟩
    rw [barycentricPoint, Finsupp.sum_fintype _ _ (fun i => zero_smul ℝ (v i))]
    exact hw

theorem continuous_barycentricPoint {I E : Type} [Fintype I]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (v : I → E) :
    Continuous (barycentricPoint v) := by
  have h : barycentricPoint v = fun p : StdSimplex ℝ I => ∑ i, p.weights i • v i := by
    funext p
    exact Finsupp.sum_fintype _ _ (fun i => zero_smul ℝ (v i))
  rw [h]
  exact continuous_finset_sum _ (fun i _ =>
    (StdSimplex.continuous_weights_apply ℝ i).smul continuous_const)

end HodgeLean.Foundations.IntegralHomology.StageTwo
