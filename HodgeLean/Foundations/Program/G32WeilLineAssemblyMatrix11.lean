import HodgeLean.Foundations.Program.G32WeilLineAssemblyMatrix10

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

open HodgeLean.Papers
namespace HodgeLean.Foundations.Program
theorem g32c_r_inv_matrix (w : ℂ) (hw : w ^ 2 + w + 1 = 0) :
    g32c_M0 w * g32c_M0 w = g32c_M4 w := by
  rw [g32c_mul46 w hw]

theorem g32c_s_cube_matrix (w : ℂ) (hw : w ^ 2 + w + 1 = 0) :
    g32c_M1 w * g32c_M1 w * g32c_M1 w = g32c_M5 w := by
  rw [g32c_mul47 w hw, g32c_mul48 w hw]

end HodgeLean.Foundations.Program
