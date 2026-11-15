import HodgeLean.Foundations.Program.G32Native.QuaternionGraphBounds
import HodgeLean.Foundations.Program.G32Native.QuaternionGraphCoordinates
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Vandermonde

noncomputable section
set_option maxHeartbeats 200000

namespace HodgeLean.Foundations.Program.QuaternionGraph

variable {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]

/-- The graph wedges of two complementary frames have the expected polynomial rank. -/
theorem graph_wedge_span_finrank {n : ℕ} (b : Module.Basis (Fin n × Fin 2) K V) :
    Module.finrank K (Submodule.span K (Set.range
      (graphWedge (K := K) (fun i => b (i, 0)) (fun i => b (i, 1))))) = n + 1 := by
  letI : Module.Finite K V := Module.Finite.of_basis b
  apply Nat.le_antisymm (graph_wedge_span_finrank_le _ _)
  let t : Fin (n+1) → K := fun i => (i.val : K)
  have ht : Function.Injective t := by
    intro i j h
    exact Fin.ext (Nat.cast_injective h)
  have hi := graphWedge_samples_independent b t ht
  have hs : Submodule.span K (Set.range (fun i =>
      graphWedge (K := K) (fun j => b (j,0)) (fun j => b (j,1)) (t i))) ≤
      Submodule.span K (Set.range (graphWedge (K := K) (fun j => b (j,0)) (fun j => b (j,1)))) := by
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨t i, rfl⟩
  have hr := Submodule.finrank_mono hs
  rw [finrank_span_eq_card hi, Fintype.card_fin] at hr
  exact hr

#print axioms graph_wedge_span_finrank
end HodgeLean.Foundations.Program.QuaternionGraph
