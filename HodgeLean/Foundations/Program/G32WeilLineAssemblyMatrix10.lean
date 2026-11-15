import HodgeLean.Foundations.Program.G32WeilLineAssemblyMatrix9

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

open HodgeLean.Papers
namespace HodgeLean.Foundations.Program
theorem g32c_x_inv_matrix (w : ℂ) (hw : w ^ 2 + w + 1 = 0) :
    g32c_M2 w * g32c_M2 w * g32c_M2 w = g32c_M7 w := by
  rw [g32c_mul15 w hw, g32c_mul16 w hw]

theorem g32c_y_inv_matrix (w : ℂ) (hw : w ^ 2 + w + 1 = 0) :
    g32c_M3 w * g32c_M3 w = g32c_M8 w := by
  rw [g32c_mul17 w hw]

theorem g32c_word_x_matrix (w : ℂ) (hw : w ^ 2 + w + 1 = 0) :
    g32c_M0 w * g32c_M12 w * g32c_M16 w * g32c_M1 w * g32c_M16 w * g32c_M0 w * g32c_M12 w * g32c_M16 w * g32c_M1 w * g32c_M0 w * g32c_M12 w * g32c_M1 w = g32c_M27 w := by
  rw [g32c_mul18 w hw, g32c_mul19 w hw, g32c_mul20 w hw, g32c_mul21 w hw, g32c_mul22 w hw, g32c_mul23 w hw, g32c_mul24 w hw, g32c_mul25 w hw, g32c_mul26 w hw, g32c_mul27 w hw, g32c_mul28 w hw]

theorem g32c_word_y_matrix (w : ℂ) (hw : w ^ 2 + w + 1 = 0) :
    g32c_M0 w * g32c_M1 w * g32c_M16 w * g32c_M0 w * g32c_M1 w * g32c_M12 w * g32c_M16 w * g32c_M10 w * g32c_M0 w * g32c_M16 w = g32c_M36 w := by
  rw [g32c_mul29 w hw, g32c_mul30 w hw, g32c_mul31 w hw, g32c_mul32 w hw, g32c_mul33 w hw, g32c_mul34 w hw, g32c_mul35 w hw, g32c_mul36 w hw, g32c_mul37 w hw]

theorem g32c_conjugacy_matrix (w : ℂ) (hw : w ^ 2 + w + 1 = 0) :
    g32c_M0 w * g32c_M0 w * g32c_M1 w * g32c_M0 w * g32c_M0 w * g32c_M40 w * g32c_M42 w * g32c_M42 w = g32c_M44 w := by
  rw [g32c_mul38 w hw, g32c_mul39 w hw, g32c_mul40 w hw, g32c_mul41 w hw, g32c_mul42 w hw, g32c_mul43 w hw, g32c_mul44 w hw]

theorem g32c_s_inv_matrix (w : ℂ) (hw : w ^ 2 + w + 1 = 0) :
    g32c_M1 w * g32c_M1 w = g32c_M45 w := by
  rw [g32c_mul45 w hw]

end HodgeLean.Foundations.Program
