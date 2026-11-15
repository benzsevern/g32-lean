import HodgeLean.Foundations.Program.G32Native.QuaternionGraphExpansion
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Vandermonde

noncomputable section
set_option maxHeartbeats 200000

namespace HodgeLean.Foundations.Program.QuaternionGraph
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Coordinate projection selecting the second frame in the first `k` positions. -/
def graphProjection {n : ℕ} (b : Module.Basis (Fin n × Fin 2) K V) (k : Fin (n+1)) :
    V →ₗ[K] (Fin n → K) :=
  LinearMap.pi (fun i => b.coord (i, if i.val < k.val then 1 else 0))

/-- The determinant functional associated with the first `k` second-frame positions. -/
def graphFunctional {n : ℕ} (b : Module.Basis (Fin n × Fin 2) K V) (k : Fin (n+1)) :
    (⋀[K]^n V) →ₗ[K] K :=
  exteriorPower.alternatingMapLinearEquiv
    ((Pi.basisFun K (Fin n)).det.compLinearMap (graphProjection b k))

/-- Projected graph vectors form a diagonal matrix with `k` entries equal to the parameter. -/
theorem graphProjection_frame {n : ℕ} (b : Module.Basis (Fin n × Fin 2) K V)
    (k : Fin (n+1)) (t : K) (i j : Fin n) :
    graphProjection b k (b (j,0) + t • b (j,1)) i =
      if i = j then (if i.val < k.val then t else 1) else 0 := by
  classical
  by_cases hij : i = j
  · subst j
    by_cases hi : i.val < k.val <;>
      simp [graphProjection, hi, Module.Basis.coord_apply, Finsupp.single_apply]
  · have hji : j ≠ i := Ne.symm hij
    simp [graphProjection, Module.Basis.coord_apply, Finsupp.single_apply, hij, hji]

/-- The graph determinant functional evaluates to the indicated monomial. -/
theorem graphFunctional_graphWedge {n : ℕ} (b : Module.Basis (Fin n × Fin 2) K V)
    (k : Fin (n+1)) (t : K) :
    graphFunctional b k (graphWedge (fun i => b (i,0)) (fun i => b (i,1)) t) = t ^ k.val := by
  classical
  unfold graphFunctional graphWedge
  rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    AlternatingMap.compLinearMap_apply, Module.Basis.det_apply]
  have hm : (Pi.basisFun K (Fin n)).toMatrix
      (fun j => graphProjection b k (b (j,0) + t • b (j,1))) =
      Matrix.diagonal (fun i : Fin n => if i.val < k.val then t else 1) := by
    ext i j
    simp only [Module.Basis.toMatrix_apply, Pi.basisFun_repr,
      graphProjection_frame, Matrix.diagonal_apply]
  rw [hm, Matrix.det_diagonal]
  simp only [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
  congr 1
  rw [← Fintype.card_subtype]
  exact Fintype.card_fin_lt_of_le (Nat.le_of_lt_succ k.isLt)

/-- Distinct scalar samples give linearly independent graph wedges. -/
theorem graphWedge_samples_independent {n : ℕ}
    (b : Module.Basis (Fin n × Fin 2) K V) (t : Fin (n+1) → K)
    (ht : Function.Injective t) :
    LinearIndependent K (fun i => graphWedge (fun j => b (j,0)) (fun j => b (j,1)) (t i)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have he : ∀ k : Fin (n+1), ∑ j, c j * t j ^ k.val = 0 := by
    intro k
    have h := congrArg (graphFunctional b k) hc
    simpa only [map_sum, map_smul, graphFunctional_graphWedge, map_zero, smul_eq_mul] using h
  have hz := Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero ht he
  exact congrFun hz i

#print axioms graphWedge_samples_independent
end HodgeLean.Foundations.Program.QuaternionGraph
