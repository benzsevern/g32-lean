import HodgeLean.Foundations.Program.G32Native.QuaternionGraphExpansion
import Mathlib.LinearAlgebra.Dimension.Constructions

noncomputable section
set_option maxHeartbeats 200000

namespace HodgeLean.Foundations.Program.QuaternionGraph
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Every graph wedge lies in the span of its homogeneous coefficients. -/
theorem graphWedge_mem_coeff_span {n : ℕ} (u v : Fin n → V) (t : K) :
    graphWedge u v t ∈ Submodule.span K (Set.range (graphCoeff (K := K) u v)) := by
  rw [graphWedge_eq_sum_coeff]
  apply Submodule.sum_mem
  intro k hk
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

/-- A graph-wedge family has rank at most its number of homogeneous coefficients. -/
theorem graph_wedge_span_finrank_le [Module.Finite K V] {n : ℕ} (u v : Fin n → V) :
    Module.finrank K (Submodule.span K (Set.range (graphWedge (K := K) u v))) ≤ n+1 := by
  have hle : Submodule.span K (Set.range (graphWedge (K := K) u v)) ≤
      Submodule.span K (Set.range (graphCoeff (K := K) u v)) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨t, rfl⟩
    exact graphWedge_mem_coeff_span u v t
  exact (Submodule.finrank_mono hle).trans (by
    simpa only [Fintype.card_fin, Set.finrank] using
      (finrank_range_le_card (R := K) (graphCoeff (K := K) u v)))

#print axioms graph_wedge_span_finrank_le
end HodgeLean.Foundations.Program.QuaternionGraph
