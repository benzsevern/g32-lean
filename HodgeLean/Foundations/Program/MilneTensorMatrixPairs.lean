import HodgeLean.Foundations.Program.MilneTensorRankOneForm

noncomputable section
namespace HodgeLean.Foundations.Program
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def m1b_matrixPairVectors (Q : Matrix ι ι ℂ) (ij : ι × ι) : Fin 2 → ι → ℂ :=
  ![Q ij.1 ij.2 • Pi.single ij.1 1, Pi.single ij.2 1]

theorem m1b_matrixPairVectors_sum (Q : Matrix ι ι ℂ) :
    (∑ ij : ι × ι, m1b_rankOneForm (m1b_matrixPairVectors Q ij)) =
      fun ij => Q ij.1 ij.2 := by
  funext ij
  rcases ij with ⟨i, j⟩
  simp [Finset.sum_apply, m1b_rankOneForm_apply, m1b_matrixPairVectors,
    Fintype.sum_prod_type, Pi.single_apply, mul_ite, ite_mul]

end HodgeLean.Foundations.Program
