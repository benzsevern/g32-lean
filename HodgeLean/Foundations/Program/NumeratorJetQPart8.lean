import HodgeLean.Foundations.Program.NumeratorJetNumeratorDefs

/-! # Checks of the polynomial parts of `D_θ q`, coefficient 8 -/

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000 in
/-- The stored polynomial-part coefficients satisfy their formula. -/
theorem b65e_G_table_8_0 :
    ∀ b : Fin 3, ∀ n : Fin 8, b65e_GQ 8 0 b n = b65e_GFormulaQ 8 0 b n.val := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored polynomial-part coefficients satisfy their formula. -/
theorem b65e_G_table_8_1 :
    ∀ b : Fin 3, ∀ n : Fin 8, b65e_GQ 8 1 b n = b65e_GFormulaQ 8 1 b n.val := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored polynomial-part coefficients satisfy their formula. -/
theorem b65e_G_table_8_2 :
    ∀ b : Fin 3, ∀ n : Fin 8, b65e_GQ 8 2 b n = b65e_GFormulaQ 8 2 b n.val := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- The stored polynomial-part coefficients satisfy their formula. -/
theorem b65e_G_table_8_3 :
    ∀ b : Fin 3, ∀ n : Fin 8, b65e_GQ 8 3 b n = b65e_GFormulaQ 8 3 b n.val := by
  decide +kernel

end HodgeLean.Foundations.Program
