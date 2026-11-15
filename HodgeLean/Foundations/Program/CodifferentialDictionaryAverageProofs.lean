import HodgeLean.Foundations.Program.CodifferentialDictionaryRealizationProofs

noncomputable section
open Set Filter Topology Manifold HodgeLean.Papers
open scoped TensorProduct
namespace HodgeLean.Foundations.Program
attribute [local instance] Classical.propDecidable
attribute [local instance] b65z_SharedFamily.topC b65z_SharedFamily.chartC
  b65z_SharedFamily.manC b65z_SharedFamily.t2C b65z_SharedFamily.compactC
  b65z_SharedFamily.connectedC b65z_SharedFamily.actionC b65z_SharedFamily.totalChart
  b65z_SharedFamily.totalMan b65z_SharedFamily.fibreChart b65z_SharedFamily.fibreMan
  b65z_SharedFamily.fibreT2 b65z_SharedFamily.fibreCompact b65z_SharedFamily.fibreConnected
  b65z_SharedFamily.fibreFaithful

open Metric Matrix

theorem b66d_coordinate_average (cj : Bool) (i j : Fin 4) :
    ∑ h : b4b_Group, b65g_mat cj h 0 i * b65g_mat (!cj) h 0 j =
      if i = j then (38880 : ℂ) else 0 := by
  have hn (i j : Fin 4) : ∑ h : b4b_Group,
      b4b_toMatrix h 0 i * starRingEnd ℂ (b4b_toMatrix h 0 j) =
      if i = j then (38880 : ℂ) else 0 := by
    have ht : (Matrix.single i j (1 : ℂ) : Matrix (Fin 4) (Fin 4) ℂ).trace =
        if i = j then 1 else 0 := by
      by_cases hij : i = j
      · subst j
        simp only [Matrix.trace_single_eq_same, ite_true]
      · rw [Matrix.trace_single_eq_of_ne i j 1 hij, ite_eq_right hij]
    have hm (A B : Matrix (Fin 4) (Fin 4) ℂ) :
        (A * (Matrix.single i j 1 : Matrix (Fin 4) (Fin 4) ℂ) * B) 0 0 = A 0 i * B j 0 := by
      simp [Matrix.mul_apply, Matrix.single_apply, ite_and]
    have h := congrFun (congrFun (b63l_average_scalar (Matrix.single i j 1)) 0) 0
    simp only [Matrix.sum_apply, hm, b63l_toMatrix_entry_inv, ht,
      Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, ite_true, mul_one] at h
    split_ifs at h ⊢ <;> norm_num at h ⊢ <;> exact h
  cases cj
  · simpa [b65g_mat] using hn i j
  · simpa [b65g_mat, mul_comm, eq_comm] using hn j i

end HodgeLean.Foundations.Program
