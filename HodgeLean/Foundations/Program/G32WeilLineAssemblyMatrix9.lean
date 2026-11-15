import HodgeLean.Foundations.Program.G32WeilLineAssemblyMatrix8

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

open HodgeLean.Papers
namespace HodgeLean.Foundations.Program
theorem g32c_r_cube_matrix (w : ℂ) (hw : w ^ 2 + w + 1 = 0) :
    g32c_M0 w * g32c_M0 w * g32c_M0 w = g32c_M5 w := by
  rw [g32c_mul0 w hw, g32c_mul1 w hw]

theorem g32c_x_four_matrix (w : ℂ) (hw : w ^ 2 + w + 1 = 0) :
    g32c_M2 w * g32c_M2 w * g32c_M2 w * g32c_M2 w = g32c_M5 w := by
  rw [g32c_mul2 w hw, g32c_mul3 w hw, g32c_matrix_mul4 w hw]

theorem g32c_y_cube_matrix (w : ℂ) (hw : w ^ 2 + w + 1 = 0) :
    g32c_M3 w * g32c_M3 w * g32c_M3 w = g32c_M5 w := by
  rw [g32c_mul5 w hw, g32c_mul6 w hw]

theorem g32c_reflection2_matrix (w : ℂ) (hw : w ^ 2 + w + 1 = 0) :
    g32c_M2 w * g32c_M0 w * g32c_M7 w = g32c_M10 w := by
  rw [g32c_mul7 w hw, g32c_mul8 w hw]

theorem g32c_reflection3_matrix (w : ℂ) (hw : w ^ 2 + w + 1 = 0) :
    g32c_M3 w * g32c_M0 w * g32c_M8 w = g32c_M12 w := by
  rw [g32c_mul9 w hw, g32c_mul10 w hw]

theorem g32c_reflection4_matrix (w : ℂ) (hw : w ^ 2 + w + 1 = 0) :
    g32c_M3 w * g32c_M2 w * g32c_M0 w * g32c_M7 w * g32c_M8 w = g32c_M16 w := by
  rw [g32c_mul11 w hw, g32c_mul12 w hw, g32c_mul13 w hw, g32c_mul14 w hw]

end HodgeLean.Foundations.Program
