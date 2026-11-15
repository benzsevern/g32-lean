import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Geometry.Convex.ConvexSpace.ModuleTopology

/-! Finite barycentric points and their change of index.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open Convexity
namespace HodgeLean.Foundations.IntegralHomology.StageTwo

variable {I J E : Type} [AddCommGroup E] [Module ℝ E]

def barycentricPoint (v : I → E) (p : StdSimplex ℝ I) : E :=
  p.weights.sum (fun i r => r • v i)

theorem barycentricPoint_map (f : I → J) (v : J → E) (p : StdSimplex ℝ I) :
    barycentricPoint v (p.map f) = barycentricPoint (fun i => v (f i)) p := by
  simp only [barycentricPoint, StdSimplex.weights_map,
    Finsupp.sum_mapDomain_index, zero_smul, add_smul, implies_true]

theorem barycentricPoint_mem_convexHull [Fintype I] (v : I → E) (p : StdSimplex ℝ I)
    (s : Set E) (hv : ∀ i, v i ∈ s) : barycentricPoint v p ∈ convexHull ℝ s := by
  apply mem_convexHull_of_exists_fintype p.weights v p.nonneg p.total_of_fintype hv
  exact (Finsupp.sum_fintype p.weights (fun i r => r • v i) (fun i => zero_smul ℝ (v i))).symm

end HodgeLean.Foundations.IntegralHomology.StageTwo
