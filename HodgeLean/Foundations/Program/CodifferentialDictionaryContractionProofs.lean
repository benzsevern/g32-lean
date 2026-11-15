import HodgeLean.Foundations.Program.CodifferentialDictionaryAverageProofs

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

theorem b66d_column_average (cj : Bool) (i j : Fin 4) :
    ∑ h : b4b_Group, b65g_mat cj h i 0 * b65g_mat (!cj) h j 0 =
      if i = j then (38880 : ℂ) else 0 := by
  have h := (Equiv.sum_comp (Equiv.inv b4b_Group)
    (fun h => b65g_mat (!cj) h 0 i * b65g_mat (!(!cj)) h 0 j)).trans
      (b66d_coordinate_average (!cj) i j)
  cases cj <;> simpa [b65g_mat, b63l_toMatrix_entry_inv, Equiv.inv_apply] using h

theorem b66d_bilinear_average (cj : Bool)
    (A B : (Fin 4 → ℂ) →ₗ[ℂ] ℂ) :
    (∑ h : b4b_Group, A (b65g_rep cj h (Pi.single 0 1)) *
      B (b65g_rep (!cj) h (Pi.single 0 1))) =
      (38880 : ℂ) * ∑ i : Fin 4, A (Pi.single i 1) * B (Pi.single i 1) := by
  have hexpand (L : (Fin 4 → ℂ) →ₗ[ℂ] ℂ) (h : b4b_Group) (cj : Bool) :
      L (b65g_rep cj h (Pi.single 0 1)) =
        ∑ i : Fin 4, b65g_mat cj h i 0 * L (Pi.single i 1) := by
    have hv : b65g_rep cj h (Pi.single 0 1) =
        ∑ i : Fin 4, b65g_mat cj h i 0 • (Pi.single i 1 : Fin 4 → ℂ) := by
      ext j
      simp [b65g_rep, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [hv, map_sum]
    simp only [map_smul, smul_eq_mul]
  simp_rw [hexpand, Finset.sum_mul, Finset.mul_sum]
  calc
    (∑ h : b4b_Group, ∑ i : Fin 4, ∑ j : Fin 4,
      (b65g_mat cj h i 0 * A (Pi.single i 1)) *
        (b65g_mat (!cj) h j 0 * B (Pi.single j 1))) =
      ∑ i : Fin 4, ∑ j : Fin 4,
        (∑ h : b4b_Group, b65g_mat cj h i 0 * b65g_mat (!cj) h j 0) *
          (A (Pi.single i 1) * B (Pi.single j 1)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro h hh
      ring
    _ = _ := by
      simp only [b66d_column_average, ite_mul, zero_mul, Finset.sum_ite_eq,
        Finset.mem_univ, ite_true, Finset.mul_sum, mul_assoc]

theorem b66d_chartForm_toForm {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c) (q : b66f_Coeff D) :
    b66f_gen_b66g_toForm D t q = b66f_chartForm D t q := by
  funext u
  have hp : u.1.val = (t, u.1.val.2) := Prod.ext u.1.property rfl
  change q u.1.val u.1.val.2 * b66f_gen_b66g_sliceD D t u.1.val u.1 u.2 = _
  rw [hp]
  rfl

end HodgeLean.Foundations.Program
