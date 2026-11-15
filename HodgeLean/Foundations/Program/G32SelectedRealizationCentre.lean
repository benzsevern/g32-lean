import HodgeLean.Foundations.Program.G32SelectedRealizationRetainedProjector

noncomputable section
open HodgeLean.Papers
namespace HodgeLean.Foundations.Program

theorem g32y_inverse_centre_scalar :
    ∃ l : ℂ, l ^ 2 + l + 1 = 0 ∧
      b4b_toMatrix (b63d_scalarElement⁻¹) = l • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  have hinv : b63d_scalarElement⁻¹ = b63d_scalarElement ^ 2 := by
    calc
      b63d_scalarElement⁻¹ = b63d_scalarElement⁻¹ * b63d_scalarElement ^ 3 := by
        rw [b63d_scalarElement_cube, mul_one]
      _ = b63d_scalarElement ^ 2 := by group
  refine ⟨g32h_omega ^ 2, ?_, ?_⟩
  · linear_combination (g32h_omega ^ 2 - g32h_omega + 1) * g32h_omega_sq_add
  · rw [hinv, map_pow, b63d_scalarElement_matrix, smul_pow, one_pow]

end HodgeLean.Foundations.Program
