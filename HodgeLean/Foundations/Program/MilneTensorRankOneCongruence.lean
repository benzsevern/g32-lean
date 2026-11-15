import HodgeLean.Foundations.Program.MilneTensorRankOneForm

noncomputable section
open Matrix
namespace HodgeLean.Foundations.Program
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem m1b_rankOneForm_congruence (M : Matrix ι ι ℂ) (v : Fin 2 → ι → ℂ) :
    m1b_congruenceCoordinates M (m1b_rankOneForm v) =
      m1b_rankOneForm (fun s => M.transpose *ᵥ v s) := by
  funext ij
  rcases ij with ⟨i, j⟩
  change (M.transpose * (Matrix.of (fun a b => m1b_rankOneForm v (a, b))) * M) i j = _
  simp only [Matrix.mul_apply, m1b_rankOneForm_apply, Matrix.mulVec, dotProduct,
    Matrix.transpose_apply, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  change M b i * (v 0 b * v 1 a) * M a j = M b i * v 0 b * (M a j * v 1 a)
  ring

end HodgeLean.Foundations.Program
