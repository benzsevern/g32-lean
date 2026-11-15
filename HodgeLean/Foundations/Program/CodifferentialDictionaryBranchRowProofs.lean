import HodgeLean.Foundations.Program.CodifferentialDictionaryPolynomialResidueProofs

noncomputable section
open Metric Matrix
namespace HodgeLean.Foundations.Program

theorem b66d_branch_row_evaluation (p : Fin 12 → ℂ) (O : b65p_Outputs p)
    {θ : ℂ} (hθ : θ ∈ Metric.ball (0 : ℂ) O.radius) (N : Fin 10 → ℂ) (k : Fin 10) :
    (N ᵥ* b65g_branchMatrix p θ) k =
      (∑ j : Fin 10, N j * b65p_moving p θ (Fin.castLE (by norm_num) k) ^ j.val) /
        (b65g_rest (b65p_poles p θ) (Fin.castLE (by norm_num) k)
          (b65p_moving p θ (Fin.castLE (by norm_num) k)) *
          (b65p_moving p θ 10 * b65p_moving p θ 11 /
            ((b65p_moving p θ 11 - b65p_moving p θ 10) *
              b65p_moving p θ (Fin.castLE (by norm_num) k) ^ 2))) := by
  change (∑ j : Fin 10, N j * b65g_branchMatrix p θ j k) = _
  simp_rw [b65g_branchMatrix_eq p O hθ]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  ring

end HodgeLean.Foundations.Program
