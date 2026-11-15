import HodgeLean.Foundations.Program.PrymVariationLatticePresentation
import HodgeLean.Papers.PapersG32Certificates

noncomputable section
open HodgeLean.Papers
namespace HodgeLean.Foundations.Program

theorem b63l_toMatrix_mem_unitary (g : b4b_Group) :
    b4b_toMatrix g ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
  apply (Submonoid.closure_le.2 ?_) g.property
  intro A hA
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hA
  rcases hA with rfl | rfl | rfl | rfl
  · exact papers_g32_r1_unitary g32h_omega g32h_omega_sq_add
  · exact papers_g32_r2_unitary g32h_omega g32h_omega_sq_add
  · exact papers_g32_x_unitary g32h_omega g32h_omega_sq_add
  · exact papers_g32_y_unitary g32h_omega g32h_omega_sq_add

theorem b63l_toMatrix_inv_eq_star (g : b4b_Group) :
    b4b_toMatrix g⁻¹ = star (b4b_toMatrix g) := by
  apply (HurwitzPrymRex_g32_isUnit (b4b_toMatrix g) g.property).mul_left_cancel
  rw [← b4b_toMatrix.map_mul, mul_inv_cancel, b4b_toMatrix.map_one]
  exact (Matrix.mem_unitaryGroup_iff.mp (b63l_toMatrix_mem_unitary g)).symm

end HodgeLean.Foundations.Program
