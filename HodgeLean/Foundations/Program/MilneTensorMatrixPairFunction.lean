import HodgeLean.Foundations.Program.MilneTensorMatrixPairs
import HodgeLean.Foundations.Program.MilneTensorPairing

noncomputable section
open scoped TensorProduct
open Matrix
namespace HodgeLean.Foundations.Program
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem m1b_matrixPairVectors_tensorFunction (Q : Matrix ι ι ℂ) (v : Fin 2 → ι → ℂ) :
    m1b_tensorFunction (1 : Matrix ι ι ℂ).toBilin' 2
      (∑ ij : ι × ι, ⨂ₜ[ℂ] s, m1b_matrixPairVectors Q ij s) v = Q.toBilin' (v 0) (v 1) := by
  simp only [map_sum, MultilinearMap.sum_apply, m1b_tensorFunction_apply,
    m1b_tensorBilin_tprod, Fin.prod_univ_two, m1b_matrixPairVectors,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.toBilin'_apply', Matrix.one_mulVec]
  simp [dotProduct, Matrix.mulVec, Fintype.sum_prod_type, Pi.single_apply,
    mul_ite, ite_mul, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]

end HodgeLean.Foundations.Program
